import V185TrunkScan23Chunk0150

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_892600 : List Nat := [2, 1, 2, 1, 2, 1, 1, 6, 7]
def baseStart_892600 : Nat := 118140960795 + 892600 * 2 ^ 59
def prefixEnd_892600 : Nat := 4983230072969 + 3 ^ 40 * 892600 * 2
def baseEnd_892600 : Nat := 50925870244812548010557

theorem tailTrace_892600 : CollatzResearch.WordTrace tailWord_892600 prefixEnd_892600 50925870244812548010557 := by
  unfold tailWord_892600
  simp only [CollatzResearch.WordTrace]
  refine ⟨16277898283135059394213627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21703864377513412525618169 16277898283135059394213627)
  ·
    refine ⟨24416847424702589091320441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16277898283135059394213627 24416847424702589091320441)
    ·
      refine ⟨18312635568526941818490331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24416847424702589091320441 18312635568526941818490331)
      ·
        refine ⟨27468953352790412727735497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18312635568526941818490331 27468953352790412727735497)
        ·
          refine ⟨20601715014592809545801623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27468953352790412727735497 20601715014592809545801623)
          ·
            refine ⟨30902572521889214318702435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20601715014592809545801623 30902572521889214318702435)
            ·
              refine ⟨46353858782833821478053653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30902572521889214318702435 46353858782833821478053653)
              ·
                refine ⟨2172837130445335381783765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46353858782833821478053653 2172837130445335381783765)
                ·
                  refine ⟨50925870244812548010557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2172837130445335381783765 50925870244812548010557)
                  ·
                    rfl

theorem cell23_892600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 7].length) (baseStart_892600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892600 prefixEnd_892600 := by exact prefixLift 892600
  have htrace : WordTrace (prefixWord ++ tailWord_892600) baseStart_892600 baseEnd_892600 := by
    simpa [prefixWord, tailWord_892600, baseEnd_892600] using wordTrace_append hprefix tailTrace_892600
  have hstable : (prefixWord ++ tailWord_892600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892600).length < 2 ^ (prefixWord ++ tailWord_892600).sum := by decide
  have hdescent : baseEnd_892600 < baseStart_892600 := by decide
  rcases family_descends (prefixWord ++ tailWord_892600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892628 : List Nat := [2, 4, 1, 3, 1, 1, 1, 4, 2, 2, 2]
def baseStart_892628 : Nat := 118140960795 + 892628 * 2 ^ 59
def prefixEnd_892628 : Nat := 4983230072969 + 3 ^ 40 * 892628 * 2
def baseEnd_892628 : Nat := 458347209661638822544885

theorem tailTrace_892628 : CollatzResearch.WordTrace tailWord_892628 prefixEnd_892628 458347209661638822544885 := by
  unfold tailWord_892628
  simp only [CollatzResearch.WordTrace]
  refine ⟨16278408905084339785223269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21704545206779119713631025 16278408905084339785223269)
  ·
    refine ⟨3052201669703313709729363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16278408905084339785223269 3052201669703313709729363)
    ·
      refine ⟨4578302504554970564594045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3052201669703313709729363 4578302504554970564594045)
      ·
        refine ⟨1716863439208113961722767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4578302504554970564594045 1716863439208113961722767)
        ·
          refine ⟨2575295158812170942584151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1716863439208113961722767 2575295158812170942584151)
          ·
            refine ⟨3862942738218256413876227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2575295158812170942584151 3862942738218256413876227)
            ·
              refine ⟨5794414107327384620814341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3862942738218256413876227 5794414107327384620814341)
              ·
                refine ⟨1086452645123884616402689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5794414107327384620814341 1086452645123884616402689)
                ·
                  refine ⟨814839483842913462302017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1086452645123884616402689 814839483842913462302017)
                  ·
                    refine ⟨611129612882185096726513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 814839483842913462302017 611129612882185096726513)
                    ·
                      refine ⟨458347209661638822544885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 611129612882185096726513 458347209661638822544885)
                      ·
                        rfl

theorem cell23_892628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_892628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892628 prefixEnd_892628 := by exact prefixLift 892628
  have htrace : WordTrace (prefixWord ++ tailWord_892628) baseStart_892628 baseEnd_892628 := by
    simpa [prefixWord, tailWord_892628, baseEnd_892628] using wordTrace_append hprefix tailTrace_892628
  have hstable : (prefixWord ++ tailWord_892628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892628).length < 2 ^ (prefixWord ++ tailWord_892628).sum := by decide
  have hdescent : baseEnd_892628 < baseStart_892628 := by decide
  rcases family_descends (prefixWord ++ tailWord_892628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892634 : List Nat := [3, 1, 1, 2, 2, 4, 1, 4, 5]
def baseStart_892634 : Nat := 118140960795 + 892634 * 2 ^ 59
def prefixEnd_892634 : Nat := 4983230072969 + 3 ^ 40 * 892634 * 2
def baseEnd_892634 : Nat := 50927810060618422118873

theorem tailTrace_892634 : CollatzResearch.WordTrace tailWord_892634 prefixEnd_892634 50927810060618422118873 := by
  unfold tailWord_892634
  simp only [CollatzResearch.WordTrace]
  refine ⟨8139259162036735648791239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21704691098764628396776637 8139259162036735648791239)
  ·
    refine ⟨12208888743055103473186859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8139259162036735648791239 12208888743055103473186859)
    ·
      refine ⟨18313333114582655209780289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12208888743055103473186859 18313333114582655209780289)
      ·
        refine ⟨13734999835936991407335217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18313333114582655209780289 13734999835936991407335217)
        ·
          refine ⟨10301249876952743555501413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13734999835936991407335217 10301249876952743555501413)
          ·
            refine ⟨1931484351928639416656515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10301249876952743555501413 1931484351928639416656515)
            ·
              refine ⟨2897226527892959124984773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1931484351928639416656515 2897226527892959124984773)
              ·
                refine ⟨543229973979929835934645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2897226527892959124984773 543229973979929835934645)
                ·
                  refine ⟨50927810060618422118873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 543229973979929835934645 50927810060618422118873)
                  ·
                    rfl

theorem cell23_892634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 4, 5].length) (baseStart_892634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892634 prefixEnd_892634 := by exact prefixLift 892634
  have htrace : WordTrace (prefixWord ++ tailWord_892634) baseStart_892634 baseEnd_892634 := by
    simpa [prefixWord, tailWord_892634, baseEnd_892634] using wordTrace_append hprefix tailTrace_892634
  have hstable : (prefixWord ++ tailWord_892634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892634).length < 2 ^ (prefixWord ++ tailWord_892634).sum := by decide
  have hdescent : baseEnd_892634 < baseStart_892634 := by decide
  rcases family_descends (prefixWord ++ tailWord_892634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892654 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 2, 5, 2]
def baseStart_892654 : Nat := 118140960795 + 892654 * 2 ^ 59
def prefixEnd_892654 : Nat := 4983230072969 + 3 ^ 40 * 892654 * 2
def baseEnd_892654 : Nat := 458360560158655720819765

theorem tailTrace_892654 : CollatzResearch.WordTrace tailWord_892654 prefixEnd_892654 458360560158655720819765 := by
  unfold tailWord_892654
  simp only [CollatzResearch.WordTrace]
  refine ⟨4069720763509310751361627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21705177405382990673928677 4069720763509310751361627)
  ·
    refine ⟨6104581145263966127042441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4069720763509310751361627 6104581145263966127042441)
    ·
      refine ⟨4578435858947974595281831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6104581145263966127042441 4578435858947974595281831)
      ·
        refine ⟨6867653788421961892922747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4578435858947974595281831 6867653788421961892922747)
        ·
          refine ⟨10301480682632942839384121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6867653788421961892922747 10301480682632942839384121)
          ·
            refine ⟨7726110511974707129538091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10301480682632942839384121 7726110511974707129538091)
            ·
              refine ⟨11589165767962060694307137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7726110511974707129538091 11589165767962060694307137)
              ·
                refine ⟨8691874325971545520730353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11589165767962060694307137 8691874325971545520730353)
                ·
                  refine ⟨6518905744478659140547765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8691874325971545520730353 6518905744478659140547765)
                  ·
                    refine ⟨611147413544874294426353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6518905744478659140547765 611147413544874294426353)
                    ·
                      refine ⟨458360560158655720819765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 611147413544874294426353 458360560158655720819765)
                      ·
                        rfl

theorem cell23_892654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_892654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892654 prefixEnd_892654 := by exact prefixLift 892654
  have htrace : WordTrace (prefixWord ++ tailWord_892654) baseStart_892654 baseEnd_892654 := by
    simpa [prefixWord, tailWord_892654, baseEnd_892654] using wordTrace_append hprefix tailTrace_892654
  have hstable : (prefixWord ++ tailWord_892654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892654).length < 2 ^ (prefixWord ++ tailWord_892654).sum := by decide
  have hdescent : baseEnd_892654 < baseStart_892654 := by decide
  rcases family_descends (prefixWord ++ tailWord_892654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892667 : List Nat := [1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 4]
def baseStart_892667 : Nat := 118140960795 + 892667 * 2 ^ 59
def prefixEnd_892667 : Nat := 4983230072969 + 3 ^ 40 * 892667 * 2
def baseEnd_892667 : Nat := 458367235407164169957205

theorem tailTrace_892667 : CollatzResearch.WordTrace tailWord_892667 prefixEnd_892667 458367235407164169957205 := by
  unfold tailWord_892667
  simp only [CollatzResearch.WordTrace]
  refine ⟨32558240257027389231116255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21705493504684926154077503 32558240257027389231116255)
  ·
    refine ⟨48837360385541083846674383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32558240257027389231116255 48837360385541083846674383)
    ·
      refine ⟨73256040578311625770011575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48837360385541083846674383 73256040578311625770011575)
      ·
        refine ⟨109884060867467438655017363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73256040578311625770011575 109884060867467438655017363)
        ·
          refine ⟨164826091301201157982526045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109884060867467438655017363 164826091301201157982526045)
          ·
            refine ⟨61809784237950434243447267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164826091301201157982526045 61809784237950434243447267)
            ·
              refine ⟨92714676356925651365170901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61809784237950434243447267 92714676356925651365170901)
              ·
                refine ⟨2173000227115444953871193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 92714676356925651365170901 2173000227115444953871193)
                ·
                  refine ⟨1629750170336583715403395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2173000227115444953871193 1629750170336583715403395)
                  ·
                    refine ⟨2444625255504875573105093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1629750170336583715403395 2444625255504875573105093)
                    ·
                      refine ⟨458367235407164169957205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2444625255504875573105093 458367235407164169957205)
                      ·
                        rfl

theorem cell23_892667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 4].length) (baseStart_892667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892667 prefixEnd_892667 := by exact prefixLift 892667
  have htrace : WordTrace (prefixWord ++ tailWord_892667) baseStart_892667 baseEnd_892667 := by
    simpa [prefixWord, tailWord_892667, baseEnd_892667] using wordTrace_append hprefix tailTrace_892667
  have hstable : (prefixWord ++ tailWord_892667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892667).length < 2 ^ (prefixWord ++ tailWord_892667).sum := by decide
  have hdescent : baseEnd_892667 < baseStart_892667 := by decide
  rcases family_descends (prefixWord ++ tailWord_892667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892684 : List Nat := [2, 2, 1, 2, 2, 1, 3, 2, 2, 4, 2]
def baseStart_892684 : Nat := 118140960795 + 892684 * 2 ^ 59
def prefixEnd_892684 : Nat := 4983230072969 + 3 ^ 40 * 892684 * 2
def baseEnd_892684 : Nat := 458375964578290603444627

theorem tailTrace_892684 : CollatzResearch.WordTrace tailWord_892684 prefixEnd_892684 458375964578290603444627 := by
  unfold tailWord_892684
  simp only [CollatzResearch.WordTrace]
  refine ⟨16279430148982900567242553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21705906865310534089656737 16279430148982900567242553)
  ·
    refine ⟨12209572611737175425431915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16279430148982900567242553 12209572611737175425431915)
    ·
      refine ⟨18314358917605763138147873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12209572611737175425431915 18314358917605763138147873)
      ·
        refine ⟨13735769188204322353610905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18314358917605763138147873 13735769188204322353610905)
        ·
          refine ⟨10301826891153241765208179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13735769188204322353610905 10301826891153241765208179)
          ·
            refine ⟨15452740336729862647812269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10301826891153241765208179 15452740336729862647812269)
            ·
              refine ⟨5794777626273698492929601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15452740336729862647812269 5794777626273698492929601)
              ·
                refine ⟨4346083219705273869697201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5794777626273698492929601 4346083219705273869697201)
                ·
                  refine ⟨3259562414778955402272901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4346083219705273869697201 3259562414778955402272901)
                  ·
                    refine ⟨611167952771054137926169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3259562414778955402272901 611167952771054137926169)
                    ·
                      refine ⟨458375964578290603444627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 611167952771054137926169 458375964578290603444627)
                      ·
                        rfl

theorem cell23_892684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 2, 4, 2].length) (baseStart_892684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892684 prefixEnd_892684 := by exact prefixLift 892684
  have htrace : WordTrace (prefixWord ++ tailWord_892684) baseStart_892684 baseEnd_892684 := by
    simpa [prefixWord, tailWord_892684, baseEnd_892684] using wordTrace_append hprefix tailTrace_892684
  have hstable : (prefixWord ++ tailWord_892684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892684).length < 2 ^ (prefixWord ++ tailWord_892684).sum := by decide
  have hdescent : baseEnd_892684 < baseStart_892684 := by decide
  rcases family_descends (prefixWord ++ tailWord_892684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892685 : List Nat := [1, 7, 2, 1, 1, 1, 2, 1, 7]
def baseStart_892685 : Nat := 118140960795 + 892685 * 2 ^ 59
def prefixEnd_892685 : Nat := 4983230072969 + 3 ^ 40 * 892685 * 2
def baseEnd_892685 : Nat := 50930719784327233281347

theorem tailTrace_892685 : CollatzResearch.WordTrace tailWord_892685 prefixEnd_892685 50930719784327233281347 := by
  unfold tailWord_892685
  simp only [CollatzResearch.WordTrace]
  refine ⟨32558896770962178305271509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21705931180641452203514339 32558896770962178305271509)
  ·
    refine ⟨763099143069426054029801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 32558896770962178305271509 763099143069426054029801)
    ·
      refine ⟨572324357302069540522351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 763099143069426054029801 572324357302069540522351)
      ·
        refine ⟨858486535953104310783527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572324357302069540522351 858486535953104310783527)
        ·
          refine ⟨1287729803929656466175291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 858486535953104310783527 1287729803929656466175291)
          ·
            refine ⟨1931594705894484699262937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1287729803929656466175291 1931594705894484699262937)
            ·
              refine ⟨1448696029420863524447203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1931594705894484699262937 1448696029420863524447203)
              ·
                refine ⟨2173044044131295286670805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1448696029420863524447203 2173044044131295286670805)
                ·
                  refine ⟨50930719784327233281347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2173044044131295286670805 50930719784327233281347)
                  ·
                    rfl

theorem cell23_892685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_892685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892685 prefixEnd_892685 := by exact prefixLift 892685
  have htrace : WordTrace (prefixWord ++ tailWord_892685) baseStart_892685 baseEnd_892685 := by
    simpa [prefixWord, tailWord_892685, baseEnd_892685] using wordTrace_append hprefix tailTrace_892685
  have hstable : (prefixWord ++ tailWord_892685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892685).length < 2 ^ (prefixWord ++ tailWord_892685).sum := by decide
  have hdescent : baseEnd_892685 < baseStart_892685 := by decide
  rcases family_descends (prefixWord ++ tailWord_892685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892707 : List Nat := [1, 1, 1, 4, 2, 1, 2, 5, 6]
def baseStart_892707 : Nat := 118140960795 + 892707 * 2 ^ 59
def prefixEnd_892707 : Nat := 4983230072969 + 3 ^ 40 * 892707 * 2
def baseEnd_892707 : Nat := 50931974959260445939669

theorem tailTrace_892707 : CollatzResearch.WordTrace tailWord_892707 prefixEnd_892707 50931974959260445939669 := by
  unfold tailWord_892707
  simp only [CollatzResearch.WordTrace]
  refine ⟨32559699176882476062572375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21706466117921650708381583 32559699176882476062572375)
  ·
    refine ⟨48839548765323714093858563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32559699176882476062572375 48839548765323714093858563)
    ·
      refine ⟨73259323147985571140787845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48839548765323714093858563 73259323147985571140787845)
      ·
        refine ⟨13736123090247294588897721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73259323147985571140787845 13736123090247294588897721)
        ·
          refine ⟨10302092317685470941673291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13736123090247294588897721 10302092317685470941673291)
          ·
            refine ⟨15453138476528206412509937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10302092317685470941673291 15453138476528206412509937)
            ·
              refine ⟨11589853857396154809382453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15453138476528206412509937 11589853857396154809382453)
              ·
                refine ⟨1086548799130889513379605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11589853857396154809382453 1086548799130889513379605)
                ·
                  refine ⟨50931974959260445939669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1086548799130889513379605 50931974959260445939669)
                  ·
                    rfl

theorem cell23_892707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 6].length) (baseStart_892707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892707 prefixEnd_892707 := by exact prefixLift 892707
  have htrace : WordTrace (prefixWord ++ tailWord_892707) baseStart_892707 baseEnd_892707 := by
    simpa [prefixWord, tailWord_892707, baseEnd_892707] using wordTrace_append hprefix tailTrace_892707
  have hstable : (prefixWord ++ tailWord_892707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892707).length < 2 ^ (prefixWord ++ tailWord_892707).sum := by decide
  have hdescent : baseEnd_892707 < baseStart_892707 := by decide
  rcases family_descends (prefixWord ++ tailWord_892707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892724 : List Nat := [2, 5, 1, 1, 2, 1, 1, 2, 8]
def baseStart_892724 : Nat := 118140960795 + 892724 * 2 ^ 59
def prefixEnd_892724 : Nat := 4983230072969 + 3 ^ 40 * 892724 * 2
def baseEnd_892724 : Nat := 50932944867163382993827

theorem tailTrace_892724 : CollatzResearch.WordTrace tailWord_892724 prefixEnd_892724 50932944867163382993827 := by
  unfold tailWord_892724
  simp only [CollatzResearch.WordTrace]
  refine ⟨16280159608910443982970613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21706879478547258643960817 16280159608910443982970613)
  ·
    refine ⟨1526264963335354123403495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16280159608910443982970613 1526264963335354123403495)
    ·
      refine ⟨2289397445003031185105243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1526264963335354123403495 2289397445003031185105243)
      ·
        refine ⟨3434096167504546777657865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2289397445003031185105243 3434096167504546777657865)
        ·
          refine ⟨2575572125628410083243399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3434096167504546777657865 2575572125628410083243399)
          ·
            refine ⟨3863358188442615124865099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2575572125628410083243399 3863358188442615124865099)
            ·
              refine ⟨5795037282663922687297649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3863358188442615124865099 5795037282663922687297649)
              ·
                refine ⟨4346277961997942015473237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5795037282663922687297649 4346277961997942015473237)
                ·
                  refine ⟨50932944867163382993827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4346277961997942015473237 50932944867163382993827)
                  ·
                    rfl

theorem cell23_892724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_892724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892724 prefixEnd_892724 := by exact prefixLift 892724
  have htrace : WordTrace (prefixWord ++ tailWord_892724) baseStart_892724 baseEnd_892724 := by
    simpa [prefixWord, tailWord_892724, baseEnd_892724] using wordTrace_append hprefix tailTrace_892724
  have hstable : (prefixWord ++ tailWord_892724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892724).length < 2 ^ (prefixWord ++ tailWord_892724).sum := by decide
  have hdescent : baseEnd_892724 < baseStart_892724 := by decide
  rcases family_descends (prefixWord ++ tailWord_892724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892728 : List Nat := [2, 1, 2, 1, 3, 5, 1, 3, 1, 4]
def baseStart_892728 : Nat := 118140960795 + 892728 * 2 ^ 59
def prefixEnd_892728 : Nat := 4983230072969 + 3 ^ 40 * 892728 * 2
def baseEnd_892728 : Nat := 152799519242362810431475

theorem tailTrace_892728 : CollatzResearch.WordTrace tailWord_892728 prefixEnd_892728 152799519242362810431475 := by
  unfold tailWord_892728
  simp only [CollatzResearch.WordTrace]
  refine ⟨16280232554903198324543419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21706976739870931099391225 16280232554903198324543419)
  ·
    refine ⟨24420348832354797486815129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16280232554903198324543419 24420348832354797486815129)
    ·
      refine ⟨18315261624266098115111347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24420348832354797486815129 18315261624266098115111347)
      ·
        refine ⟨27472892436399147172667021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18315261624266098115111347 27472892436399147172667021)
        ·
          refine ⟨10302334663649680189750133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27472892436399147172667021 10302334663649680189750133)
          ·
            refine ⟨965843874717157517789075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10302334663649680189750133 965843874717157517789075)
            ·
              refine ⟨1448765812075736276683613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965843874717157517789075 1448765812075736276683613)
              ·
                refine ⟨543287179528401103756355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1448765812075736276683613 543287179528401103756355)
                ·
                  refine ⟨814930769292601655634533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 543287179528401103756355 814930769292601655634533)
                  ·
                    refine ⟨152799519242362810431475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 814930769292601655634533 152799519242362810431475)
                    ·
                      rfl

theorem cell23_892728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 3, 1, 4].length) (baseStart_892728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892728 prefixEnd_892728 := by exact prefixLift 892728
  have htrace : WordTrace (prefixWord ++ tailWord_892728) baseStart_892728 baseEnd_892728 := by
    simpa [prefixWord, tailWord_892728, baseEnd_892728] using wordTrace_append hprefix tailTrace_892728
  have hstable : (prefixWord ++ tailWord_892728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892728).length < 2 ^ (prefixWord ++ tailWord_892728).sum := by decide
  have hdescent : baseEnd_892728 < baseStart_892728 := by decide
  rcases family_descends (prefixWord ++ tailWord_892728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892777 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 3, 1, 5]
def baseStart_892777 : Nat := 118140960795 + 892777 * 2 ^ 59
def prefixEnd_892777 : Nat := 4983230072969 + 3 ^ 40 * 892777 * 2
def baseEnd_892777 : Nat := 458423718279158739581699

theorem tailTrace_892777 : CollatzResearch.WordTrace tailWord_892777 prefixEnd_892777 458423718279158739581699 := by
  unfold tailWord_892777
  simp only [CollatzResearch.WordTrace]
  refine ⟨32562252286628878017620585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21708168191085918678413723 32562252286628878017620585)
  ·
    refine ⟨24421689214971658513215439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32562252286628878017620585 24421689214971658513215439)
    ·
      refine ⟨36632533822457487769823159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24421689214971658513215439 36632533822457487769823159)
      ·
        refine ⟨54948800733686231654734739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36632533822457487769823159 54948800733686231654734739)
        ·
          refine ⟨82423201100529347482102109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54948800733686231654734739 82423201100529347482102109)
          ·
            refine ⟨30908700412698505305788291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82423201100529347482102109 30908700412698505305788291)
            ·
              refine ⟨46363050619047757958682437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30908700412698505305788291 46363050619047757958682437)
              ·
                refine ⟨8693071991071454617252957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46363050619047757958682437 8693071991071454617252957)
                ·
                  refine ⟨3259901996651795481469859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8693071991071454617252957 3259901996651795481469859)
                  ·
                    refine ⟨4889852994977693222204789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3259901996651795481469859 4889852994977693222204789)
                    ·
                      refine ⟨458423718279158739581699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4889852994977693222204789 458423718279158739581699)
                      ·
                        rfl

theorem cell23_892777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 1, 5].length) (baseStart_892777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892777 prefixEnd_892777 := by exact prefixLift 892777
  have htrace : WordTrace (prefixWord ++ tailWord_892777) baseStart_892777 baseEnd_892777 := by
    simpa [prefixWord, tailWord_892777, baseEnd_892777] using wordTrace_append hprefix tailTrace_892777
  have hstable : (prefixWord ++ tailWord_892777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892777).length < 2 ^ (prefixWord ++ tailWord_892777).sum := by decide
  have hdescent : baseEnd_892777 < baseStart_892777 := by decide
  rcases family_descends (prefixWord ++ tailWord_892777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892794 : List Nat := [3, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5]
def baseStart_892794 : Nat := 118140960795 + 892794 * 2 ^ 59
def prefixEnd_892794 : Nat := 4983230072969 + 3 ^ 40 * 892794 * 2
def baseEnd_892794 : Nat := 458432447450285173069121

theorem tailTrace_892794 : CollatzResearch.WordTrace tailWord_892794 prefixEnd_892794 458432447450285173069121 := by
  unfold tailWord_892794
  simp only [CollatzResearch.WordTrace]
  refine ⟨8140718081891822480247359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21708581551711526613992957 8140718081891822480247359)
  ·
    refine ⟨12211077122837733720371039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8140718081891822480247359 12211077122837733720371039)
    ·
      refine ⟨18316615684256600580556559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12211077122837733720371039 18316615684256600580556559)
      ·
        refine ⟨27474923526384900870834839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18316615684256600580556559 27474923526384900870834839)
        ·
          refine ⟨41212385289577351306252259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27474923526384900870834839 41212385289577351306252259)
          ·
            refine ⟨61818577934366026959378389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41212385289577351306252259 61818577934366026959378389)
            ·
              refine ⟨1448872920336703756860431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 61818577934366026959378389 1448872920336703756860431)
              ·
                refine ⟨2173309380505055635290647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1448872920336703756860431 2173309380505055635290647)
                ·
                  refine ⟨3259964070757583452935971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2173309380505055635290647 3259964070757583452935971)
                  ·
                    refine ⟨4889946106136375179403957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3259964070757583452935971 4889946106136375179403957)
                    ·
                      refine ⟨458432447450285173069121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4889946106136375179403957 458432447450285173069121)
                      ·
                        rfl

theorem cell23_892794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5].length) (baseStart_892794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892794 prefixEnd_892794 := by exact prefixLift 892794
  have htrace : WordTrace (prefixWord ++ tailWord_892794) baseStart_892794 baseEnd_892794 := by
    simpa [prefixWord, tailWord_892794, baseEnd_892794] using wordTrace_append hprefix tailTrace_892794
  have hstable : (prefixWord ++ tailWord_892794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892794).length < 2 ^ (prefixWord ++ tailWord_892794).sum := by decide
  have hdescent : baseEnd_892794 < baseStart_892794 := by decide
  rcases family_descends (prefixWord ++ tailWord_892794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892817 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 6]
def baseStart_892817 : Nat := 118140960795 + 892817 * 2 ^ 59
def prefixEnd_892817 : Nat := 4983230072969 + 3 ^ 40 * 892817 * 2
def baseEnd_892817 : Nat := 458444257505338583081515

theorem tailTrace_892817 : CollatzResearch.WordTrace tailWord_892817 prefixEnd_892817 458444257505338583081515 := by
  unfold tailWord_892817
  simp only [CollatzResearch.WordTrace]
  refine ⟨32563711206483964849076705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21709140804322643232717803 32563711206483964849076705)
  ·
    refine ⟨24422783404862973636807529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32563711206483964849076705 24422783404862973636807529)
    ·
      refine ⟨18317087553647230227605647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24422783404862973636807529 18317087553647230227605647)
      ·
        refine ⟨27475631330470845341408471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18317087553647230227605647 27475631330470845341408471)
        ·
          refine ⟨41213446995706268012112707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27475631330470845341408471 41213446995706268012112707)
          ·
            refine ⟨61820170493559402018169061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41213446995706268012112707 61820170493559402018169061)
            ·
              refine ⟨11591281967542387878406699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61820170493559402018169061 11591281967542387878406699)
              ·
                refine ⟨17386922951313581817610049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11591281967542387878406699 17386922951313581817610049)
                ·
                  refine ⟨13040192213485186363207537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17386922951313581817610049 13040192213485186363207537)
                  ·
                    refine ⟨9780144160113889772405653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13040192213485186363207537 9780144160113889772405653)
                    ·
                      refine ⟨458444257505338583081515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9780144160113889772405653 458444257505338583081515)
                      ·
                        rfl

theorem cell23_892817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_892817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892817 prefixEnd_892817 := by exact prefixLift 892817
  have htrace : WordTrace (prefixWord ++ tailWord_892817) baseStart_892817 baseEnd_892817 := by
    simpa [prefixWord, tailWord_892817, baseEnd_892817] using wordTrace_append hprefix tailTrace_892817
  have hstable : (prefixWord ++ tailWord_892817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892817).length < 2 ^ (prefixWord ++ tailWord_892817).sum := by decide
  have hdescent : baseEnd_892817 < baseStart_892817 := by decide
  rcases family_descends (prefixWord ++ tailWord_892817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892818 : List Nat := [3, 2, 3, 2, 1, 1, 2, 3, 2, 4]
def baseStart_892818 : Nat := 118140960795 + 892818 * 2 ^ 59
def prefixEnd_892818 : Nat := 4983230072969 + 3 ^ 40 * 892818 * 2
def baseEnd_892818 : Nat := 152814923661997693056337

theorem tailTrace_892818 : CollatzResearch.WordTrace tailWord_892818 prefixEnd_892818 152814923661997693056337 := by
  unfold tailWord_892818
  simp only [CollatzResearch.WordTrace]
  refine ⟨8140936919870085504965777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21709165119653561346575405 8140936919870085504965777)
  ·
    refine ⟨6105702689902564128724333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8140936919870085504965777 6105702689902564128724333)
    ·
      refine ⟨2289638508713461548271625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6105702689902564128724333 2289638508713461548271625)
      ·
        refine ⟨1717228881535096161203719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2289638508713461548271625 1717228881535096161203719)
        ·
          refine ⟨2575843322302644241805579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1717228881535096161203719 2575843322302644241805579)
          ·
            refine ⟨3863764983453966362708369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2575843322302644241805579 3863764983453966362708369)
            ·
              refine ⟨2897823737590474772031277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3863764983453966362708369 2897823737590474772031277)
              ·
                refine ⟨1086683901596428039511729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2897823737590474772031277 1086683901596428039511729)
                ·
                  refine ⟨815012926197321029633797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1086683901596428039511729 815012926197321029633797)
                  ·
                    refine ⟨152814923661997693056337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 815012926197321029633797 152814923661997693056337)
                    ·
                      rfl

theorem cell23_892818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_892818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892818 prefixEnd_892818 := by exact prefixLift 892818
  have htrace : WordTrace (prefixWord ++ tailWord_892818) baseStart_892818 baseEnd_892818 := by
    simpa [prefixWord, tailWord_892818, baseEnd_892818] using wordTrace_append hprefix tailTrace_892818
  have hstable : (prefixWord ++ tailWord_892818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892818).length < 2 ^ (prefixWord ++ tailWord_892818).sum := by decide
  have hdescent : baseEnd_892818 < baseStart_892818 := by decide
  rcases family_descends (prefixWord ++ tailWord_892818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892831 : List Nat := [1, 1, 2, 5, 3, 1, 3, 7]
def baseStart_892831 : Nat := 118140960795 + 892831 * 2 ^ 59
def prefixEnd_892831 : Nat := 4983230072969 + 3 ^ 40 * 892831 * 2
def baseEnd_892831 : Nat := 16979683193870426974313

theorem tailTrace_892831 : CollatzResearch.WordTrace tailWord_892831 prefixEnd_892831 16979683193870426974313 := by
  unfold tailWord_892831
  simp only [CollatzResearch.WordTrace]
  refine ⟨32564221828433245240086347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21709481218955496826724231 32564221828433245240086347)
  ·
    refine ⟨48846332742649867860129521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32564221828433245240086347 48846332742649867860129521)
    ·
      refine ⟨36634749556987400895097141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48846332742649867860129521 36634749556987400895097141)
      ·
        refine ⟨3434507770967568833915357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36634749556987400895097141 3434507770967568833915357)
        ·
          refine ⟨1287940414112838312718259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3434507770967568833915357 1287940414112838312718259)
          ·
            refine ⟨1931910621169257469077389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1287940414112838312718259 1931910621169257469077389)
            ·
              refine ⟨724466482938471550904021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1931910621169257469077389 724466482938471550904021)
              ·
                refine ⟨16979683193870426974313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 724466482938471550904021 16979683193870426974313)
                ·
                  rfl

theorem cell23_892831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 7].length) (baseStart_892831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892831 prefixEnd_892831 := by exact prefixLift 892831
  have htrace : WordTrace (prefixWord ++ tailWord_892831) baseStart_892831 baseEnd_892831 := by
    simpa [prefixWord, tailWord_892831, baseEnd_892831] using wordTrace_append hprefix tailTrace_892831
  have hstable : (prefixWord ++ tailWord_892831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892831).length < 2 ^ (prefixWord ++ tailWord_892831).sum := by decide
  have hdescent : baseEnd_892831 < baseStart_892831 := by decide
  rcases family_descends (prefixWord ++ tailWord_892831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892852 : List Nat := [2, 5, 2, 1, 2, 2, 1, 2, 2, 4]
def baseStart_892852 : Nat := 118140960795 + 892852 * 2 ^ 59
def prefixEnd_892852 : Nat := 4983230072969 + 3 ^ 40 * 892852 * 2
def baseEnd_892852 : Nat := 152820743109415315381285

theorem tailTrace_892852 : CollatzResearch.WordTrace tailWord_892852 prefixEnd_892852 152820743109415315381285 := by
  unfold tailWord_892852
  simp only [CollatzResearch.WordTrace]
  refine ⟨16282493880678582913300405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21709991840904777217733873 16282493880678582913300405)
  ·
    refine ⟨1526483801313617148121913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16282493880678582913300405 1526483801313617148121913)
    ·
      refine ⟨1144862850985212861091435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1526483801313617148121913 1144862850985212861091435)
      ·
        refine ⟨1717294276477819291637153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1144862850985212861091435 1717294276477819291637153)
        ·
          refine ⟨1287970707358364468727865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1717294276477819291637153 1287970707358364468727865)
          ·
            refine ⟨965978030518773351545899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1287970707358364468727865 965978030518773351545899)
            ·
              refine ⟨1448967045778160027318849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965978030518773351545899 1448967045778160027318849)
              ·
                refine ⟨1086725284333620020489137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1448967045778160027318849 1086725284333620020489137)
                ·
                  refine ⟨815043963250215015366853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1086725284333620020489137 815043963250215015366853)
                  ·
                    refine ⟨152820743109415315381285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 815043963250215015366853 152820743109415315381285)
                    ·
                      rfl

theorem cell23_892852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_892852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892852 prefixEnd_892852 := by exact prefixLift 892852
  have htrace : WordTrace (prefixWord ++ tailWord_892852) baseStart_892852 baseEnd_892852 := by
    simpa [prefixWord, tailWord_892852, baseEnd_892852] using wordTrace_append hprefix tailTrace_892852
  have hstable : (prefixWord ++ tailWord_892852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892852).length < 2 ^ (prefixWord ++ tailWord_892852).sum := by decide
  have hdescent : baseEnd_892852 < baseStart_892852 := by decide
  rcases family_descends (prefixWord ++ tailWord_892852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892874 : List Nat := [3, 1, 2, 1, 2, 1, 4, 1, 2, 6]
def baseStart_892874 : Nat := 118140960795 + 892874 * 2 ^ 59
def prefixEnd_892874 : Nat := 4983230072969 + 3 ^ 40 * 892874 * 2
def baseEnd_892874 : Nat := 152824508634214953356251

theorem tailTrace_892874 : CollatzResearch.WordTrace tailWord_892874 prefixEnd_892874 152824508634214953356251 := by
  unfold tailWord_892874
  simp only [CollatzResearch.WordTrace]
  refine ⟨8141447541819365895975419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21710526778184975722601117 8141447541819365895975419)
  ·
    refine ⟨12212171312729048843963129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8141447541819365895975419 12212171312729048843963129)
    ·
      refine ⟨9159128484546786632972347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12212171312729048843963129 9159128484546786632972347)
      ·
        refine ⟨13738692726820179949458521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9159128484546786632972347 13738692726820179949458521)
        ·
          refine ⟨10304019545115134962093891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13738692726820179949458521 10304019545115134962093891)
          ·
            refine ⟨15456029317672702443140837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10304019545115134962093891 15456029317672702443140837)
            ·
              refine ⟨2898005497063631708088907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15456029317672702443140837 2898005497063631708088907)
              ·
                refine ⟨4347008245595447562133361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2898005497063631708088907 4347008245595447562133361)
                ·
                  refine ⟨3260256184196585671600021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4347008245595447562133361 3260256184196585671600021)
                  ·
                    refine ⟨152824508634214953356251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3260256184196585671600021 152824508634214953356251)
                    ·
                      rfl

theorem cell23_892874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_892874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892874 prefixEnd_892874 := by exact prefixLift 892874
  have htrace : WordTrace (prefixWord ++ tailWord_892874) baseStart_892874 baseEnd_892874 := by
    simpa [prefixWord, tailWord_892874, baseEnd_892874] using wordTrace_append hprefix tailTrace_892874
  have hstable : (prefixWord ++ tailWord_892874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892874).length < 2 ^ (prefixWord ++ tailWord_892874).sum := by decide
  have hdescent : baseEnd_892874 < baseStart_892874 := by decide
  rcases family_descends (prefixWord ++ tailWord_892874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892881 : List Nat := [1, 2, 2, 1, 2, 1, 2, 5, 1, 4, 2]
def baseStart_892881 : Nat := 118140960795 + 892881 * 2 ^ 59
def prefixEnd_892881 : Nat := 4983230072969 + 3 ^ 40 * 892881 * 2
def baseEnd_892881 : Nat := 458477120267226332681221

theorem tailTrace_892881 : CollatzResearch.WordTrace tailWord_892881 prefixEnd_892881 458477120267226332681221 := by
  unfold tailWord_892881
  simp only [CollatzResearch.WordTrace]
  refine ⟨32566045478252103779406497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21710696985501402519604331 32566045478252103779406497)
  ·
    refine ⟨24424534108689077834554873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32566045478252103779406497 24424534108689077834554873)
    ·
      refine ⟨18318400581516808375916155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24424534108689077834554873 18318400581516808375916155)
      ·
        refine ⟨27477600872275212563874233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18318400581516808375916155 27477600872275212563874233)
        ·
          refine ⟨20608200654206409422905675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27477600872275212563874233 20608200654206409422905675)
          ·
            refine ⟨30912300981309614134358513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20608200654206409422905675 30912300981309614134358513)
            ·
              refine ⟨23184225735982210600768885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30912300981309614134358513 23184225735982210600768885)
              ·
                refine ⟨2173521162748332243822083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23184225735982210600768885 2173521162748332243822083)
                ·
                  refine ⟨3260281744122498365733125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2173521162748332243822083 3260281744122498365733125)
                  ·
                    refine ⟨611302827022968443574961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3260281744122498365733125 611302827022968443574961)
                    ·
                      refine ⟨458477120267226332681221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 611302827022968443574961 458477120267226332681221)
                      ·
                        rfl

theorem cell23_892881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 4, 2].length) (baseStart_892881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892881 prefixEnd_892881 := by exact prefixLift 892881
  have htrace : WordTrace (prefixWord ++ tailWord_892881) baseStart_892881 baseEnd_892881 := by
    simpa [prefixWord, tailWord_892881, baseEnd_892881] using wordTrace_append hprefix tailTrace_892881
  have hstable : (prefixWord ++ tailWord_892881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892881).length < 2 ^ (prefixWord ++ tailWord_892881).sum := by decide
  have hdescent : baseEnd_892881 < baseStart_892881 := by decide
  rcases family_descends (prefixWord ++ tailWord_892881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892885 : List Nat := [1, 3, 2, 3, 2, 2, 2, 2, 1, 3, 2]
def baseStart_892885 : Nat := 118140960795 + 892885 * 2 ^ 59
def prefixEnd_892885 : Nat := 4983230072969 + 3 ^ 40 * 892885 * 2
def baseEnd_892885 : Nat := 458479174189844317031203

theorem tailTrace_892885 : CollatzResearch.WordTrace tailWord_892885 prefixEnd_892885 458479174189844317031203 := by
  unfold tailWord_892885
  simp only [CollatzResearch.WordTrace]
  refine ⟨32566191370237612462552109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21710794246825074975034739 32566191370237612462552109)
  ·
    refine ⟨12212321763839104673457041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32566191370237612462552109 12212321763839104673457041)
    ·
      refine ⟨9159241322879328505092781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12212321763839104673457041 9159241322879328505092781)
      ·
        refine ⟨3434715496079748189409793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9159241322879328505092781 3434715496079748189409793)
        ·
          refine ⟨2576036622059811142057345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3434715496079748189409793 2576036622059811142057345)
          ·
            refine ⟨1932027466544858356543009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2576036622059811142057345 1932027466544858356543009)
            ·
              refine ⟨1449020599908643767407257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1932027466544858356543009 1449020599908643767407257)
              ·
                refine ⟨1086765449931482825555443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1449020599908643767407257 1086765449931482825555443)
                ·
                  refine ⟨1630148174897224238333165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1086765449931482825555443 1630148174897224238333165)
                  ·
                    refine ⟨611305565586459089374937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1630148174897224238333165 611305565586459089374937)
                    ·
                      refine ⟨458479174189844317031203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 611305565586459089374937 458479174189844317031203)
                      ·
                        rfl

theorem cell23_892885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_892885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892885 prefixEnd_892885 := by exact prefixLift 892885
  have htrace : WordTrace (prefixWord ++ tailWord_892885) baseStart_892885 baseEnd_892885 := by
    simpa [prefixWord, tailWord_892885, baseEnd_892885] using wordTrace_append hprefix tailTrace_892885
  have hstable : (prefixWord ++ tailWord_892885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892885).length < 2 ^ (prefixWord ++ tailWord_892885).sum := by decide
  have hdescent : baseEnd_892885 < baseStart_892885 := by decide
  rcases family_descends (prefixWord ++ tailWord_892885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892921 : List Nat := [1, 2, 1, 3, 1, 6, 1, 1, 7]
def baseStart_892921 : Nat := 118140960795 + 892921 * 2 ^ 59
def prefixEnd_892921 : Nat := 4983230072969 + 3 ^ 40 * 892921 * 2
def baseEnd_892921 : Nat := 50944184388156241797893

theorem tailTrace_892921 : CollatzResearch.WordTrace tailWord_892921 prefixEnd_892921 50944184388156241797893 := by
  unfold tailWord_892921
  simp only [CollatzResearch.WordTrace]
  refine ⟨32567504398107190610862617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21711669598738127073908411 32567504398107190610862617)
  ·
    refine ⟨24425628298580392958146963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32567504398107190610862617 24425628298580392958146963)
    ·
      refine ⟨36638442447870589437220445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24425628298580392958146963 36638442447870589437220445)
      ·
        refine ⟨13739415917951471038957667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36638442447870589437220445 13739415917951471038957667)
        ·
          refine ⟨20609123876927206558436501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13739415917951471038957667 20609123876927206558436501)
          ·
            refine ⟨966052681730962807426711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20609123876927206558436501 966052681730962807426711)
            ·
              refine ⟨1449079022596444211140067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 966052681730962807426711 1449079022596444211140067)
              ·
                refine ⟨2173618533894666316710101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1449079022596444211140067 2173618533894666316710101)
                ·
                  refine ⟨50944184388156241797893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2173618533894666316710101 50944184388156241797893)
                  ·
                    rfl

theorem cell23_892921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 7].length) (baseStart_892921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892921 prefixEnd_892921 := by exact prefixLift 892921
  have htrace : WordTrace (prefixWord ++ tailWord_892921) baseStart_892921 baseEnd_892921 := by
    simpa [prefixWord, tailWord_892921, baseEnd_892921] using wordTrace_append hprefix tailTrace_892921
  have hstable : (prefixWord ++ tailWord_892921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892921).length < 2 ^ (prefixWord ++ tailWord_892921).sum := by decide
  have hdescent : baseEnd_892921 < baseStart_892921 := by decide
  rcases family_descends (prefixWord ++ tailWord_892921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892988 : List Nat := [2, 2, 2, 2, 2, 1, 3, 1, 2, 4, 2]
def baseStart_892988 : Nat := 118140960795 + 892988 * 2 ^ 59
def prefixEnd_892988 : Nat := 4983230072969 + 3 ^ 40 * 892988 * 2
def baseEnd_892988 : Nat := 458532062697257414043229

theorem tailTrace_892988 : CollatzResearch.WordTrace tailWord_892988 prefixEnd_892988 458532062697257414043229 := by
  unfold tailWord_892988
  simp only [CollatzResearch.WordTrace]
  refine ⟨16284974044432230526775809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21713298725909640702367745 16284974044432230526775809)
  ·
    refine ⟨12213730533324172895081857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16284974044432230526775809 12213730533324172895081857)
    ·
      refine ⟨9160297899993129671311393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12213730533324172895081857 9160297899993129671311393)
      ·
        refine ⟨6870223424994847253483545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9160297899993129671311393 6870223424994847253483545)
        ·
          refine ⟨5152667568746135440112659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6870223424994847253483545 5152667568746135440112659)
          ·
            refine ⟨7729001353119203160168989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5152667568746135440112659 7729001353119203160168989)
            ·
              refine ⟨2898375507419701185063371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7729001353119203160168989 2898375507419701185063371)
              ·
                refine ⟨4347563261129551777595057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2898375507419701185063371 4347563261129551777595057)
                ·
                  refine ⟨3260672445847163833196293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4347563261129551777595057 3260672445847163833196293)
                  ·
                    refine ⟨611376083596343218724305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3260672445847163833196293 611376083596343218724305)
                    ·
                      refine ⟨458532062697257414043229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 611376083596343218724305 458532062697257414043229)
                      ·
                        rfl

theorem cell23_892988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_892988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892988 prefixEnd_892988 := by exact prefixLift 892988
  have htrace : WordTrace (prefixWord ++ tailWord_892988) baseStart_892988 baseEnd_892988 := by
    simpa [prefixWord, tailWord_892988, baseEnd_892988] using wordTrace_append hprefix tailTrace_892988
  have hstable : (prefixWord ++ tailWord_892988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892988).length < 2 ^ (prefixWord ++ tailWord_892988).sum := by decide
  have hdescent : baseEnd_892988 < baseStart_892988 := by decide
  rcases family_descends (prefixWord ++ tailWord_892988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892991 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 4, 2, 3]
def baseStart_892991 : Nat := 118140960795 + 892991 * 2 ^ 59
def prefixEnd_892991 : Nat := 4983230072969 + 3 ^ 40 * 892991 * 2
def baseEnd_892991 : Nat := 458533603139220902305715

theorem tailTrace_892991 : CollatzResearch.WordTrace tailWord_892991 prefixEnd_892991 458533603139220902305715 := by
  unfold tailWord_892991
  simp only [CollatzResearch.WordTrace]
  refine ⟨32570057507853592565910827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21713371671902395043940551 32570057507853592565910827)
  ·
    refine ⟨48855086261780388848866241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32570057507853592565910827 48855086261780388848866241)
    ·
      refine ⟨36641314696335291636649681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48855086261780388848866241 36641314696335291636649681)
      ·
        refine ⟨27480986022251468727487261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36641314696335291636649681 27480986022251468727487261)
        ·
          refine ⟨10305369758344300772807723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27480986022251468727487261 10305369758344300772807723)
          ·
            refine ⟨15458054637516451159211585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10305369758344300772807723 15458054637516451159211585)
            ·
              refine ⟨11593540978137338369408689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15458054637516451159211585 11593540978137338369408689)
              ·
                refine ⟨8695155733603003777056517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11593540978137338369408689 8695155733603003777056517)
                ·
                  refine ⟨1630341700050563208198097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8695155733603003777056517 1630341700050563208198097)
                  ·
                    refine ⟨1222756275037922406148573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1630341700050563208198097 1222756275037922406148573)
                    ·
                      refine ⟨458533603139220902305715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1222756275037922406148573 458533603139220902305715)
                      ·
                        rfl

theorem cell23_892991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 2, 3].length) (baseStart_892991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_892991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_892991 prefixEnd_892991 := by exact prefixLift 892991
  have htrace : WordTrace (prefixWord ++ tailWord_892991) baseStart_892991 baseEnd_892991 := by
    simpa [prefixWord, tailWord_892991, baseEnd_892991] using wordTrace_append hprefix tailTrace_892991
  have hstable : (prefixWord ++ tailWord_892991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892991).length < 2 ^ (prefixWord ++ tailWord_892991).sum := by decide
  have hdescent : baseEnd_892991 < baseStart_892991 := by decide
  rcases family_descends (prefixWord ++ tailWord_892991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893082 : List Nat := [3, 1, 1, 5, 2, 1, 1, 2, 2, 3, 2]
def baseStart_893082 : Nat := 118140960795 + 893082 * 2 ^ 59
def prefixEnd_893082 : Nat := 4983230072969 + 3 ^ 40 * 893082 * 2
def baseEnd_893082 : Nat := 458580329878780046267797

theorem tailTrace_893082 : CollatzResearch.WordTrace tailWord_893082 prefixEnd_893082 458580329878780046267797 := by
  unfold tailWord_893082
  simp only [CollatzResearch.WordTrace]
  refine ⟨8143344137630978776868375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21715584367015943404982333 8143344137630978776868375)
  ·
    refine ⟨12215016206446468165302563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8143344137630978776868375 12215016206446468165302563)
    ·
      refine ⟨18322524309669702247953845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12215016206446468165302563 18322524309669702247953845)
      ·
        refine ⟨1717736654031534585745673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18322524309669702247953845 1717736654031534585745673)
        ·
          refine ⟨1288302490523650939309255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1717736654031534585745673 1288302490523650939309255)
          ·
            refine ⟨1932453735785476408963883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1288302490523650939309255 1932453735785476408963883)
            ·
              refine ⟨2898680603678214613445825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1932453735785476408963883 2898680603678214613445825)
              ·
                refine ⟨2174010452758660960084369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2898680603678214613445825 2174010452758660960084369)
                ·
                  refine ⟨1630507839568995720063277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2174010452758660960084369 1630507839568995720063277)
                  ·
                    refine ⟨611440439838373395023729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1630507839568995720063277 611440439838373395023729)
                    ·
                      refine ⟨458580329878780046267797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 611440439838373395023729 458580329878780046267797)
                      ·
                        rfl

theorem cell23_893082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_893082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893082 prefixEnd_893082 := by exact prefixLift 893082
  have htrace : WordTrace (prefixWord ++ tailWord_893082) baseStart_893082 baseEnd_893082 := by
    simpa [prefixWord, tailWord_893082, baseEnd_893082] using wordTrace_append hprefix tailTrace_893082
  have hstable : (prefixWord ++ tailWord_893082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893082).length < 2 ^ (prefixWord ++ tailWord_893082).sum := by decide
  have hdescent : baseEnd_893082 < baseStart_893082 := by decide
  rcases family_descends (prefixWord ++ tailWord_893082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893088 : List Nat := [2, 1, 1, 4, 2, 2, 2, 1, 4, 4]
def baseStart_893088 : Nat := 118140960795 + 893088 * 2 ^ 59
def prefixEnd_893088 : Nat := 4983230072969 + 3 ^ 40 * 893088 * 2
def baseEnd_893088 : Nat := 152861136920902340930923

theorem tailTrace_893088 : CollatzResearch.WordTrace tailWord_893088 prefixEnd_893088 152861136920902340930923 := by
  unfold tailWord_893088
  simp only [CollatzResearch.WordTrace]
  refine ⟨16286797694251089066095959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21715730259001452088127945 16286797694251089066095959)
  ·
    refine ⟨24430196541376633599143939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16286797694251089066095959 24430196541376633599143939)
    ·
      refine ⟨36645294812064950398715909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24430196541376633599143939 36645294812064950398715909)
      ·
        refine ⟨6870992777262178199759233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36645294812064950398715909 6870992777262178199759233)
        ·
          refine ⟨5153244582946633649819425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6870992777262178199759233 5153244582946633649819425)
          ·
            refine ⟨3864933437209975237364569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5153244582946633649819425 3864933437209975237364569)
            ·
              refine ⟨2898700077907481428023427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3864933437209975237364569 2898700077907481428023427)
              ·
                refine ⟨4348050116861222142035141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2898700077907481428023427 4348050116861222142035141)
                ·
                  refine ⟨815259396911479151631589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4348050116861222142035141 815259396911479151631589)
                  ·
                    refine ⟨152861136920902340930923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 815259396911479151631589 152861136920902340930923)
                    ·
                      rfl

theorem cell23_893088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 4, 4].length) (baseStart_893088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893088 prefixEnd_893088 := by exact prefixLift 893088
  have htrace : WordTrace (prefixWord ++ tailWord_893088) baseStart_893088 baseEnd_893088 := by
    simpa [prefixWord, tailWord_893088, baseEnd_893088] using wordTrace_append hprefix tailTrace_893088
  have hstable : (prefixWord ++ tailWord_893088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893088).length < 2 ^ (prefixWord ++ tailWord_893088).sum := by decide
  have hdescent : baseEnd_893088 < baseStart_893088 := by decide
  rcases family_descends (prefixWord ++ tailWord_893088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893089 : List Nat := [1, 2, 3, 3, 1, 3, 3, 2, 1, 1, 3]
def baseStart_893089 : Nat := 118140960795 + 893089 * 2 ^ 59
def prefixEnd_893089 : Nat := 4983230072969 + 3 ^ 40 * 893089 * 2
def baseEnd_893089 : Nat := 458583924243361518880265

theorem tailTrace_893089 : CollatzResearch.WordTrace tailWord_893089 prefixEnd_893089 458583924243361518880265 := by
  unfold tailWord_893089
  simp only [CollatzResearch.WordTrace]
  refine ⟨32573631861498555302978321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21715754574332370201985547 32573631861498555302978321)
  ·
    refine ⟨24430223896123916477233741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32573631861498555302978321 24430223896123916477233741)
    ·
      refine ⟨9161333961046468678962653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24430223896123916477233741 9161333961046468678962653)
      ·
        refine ⟨3435500235392425754610995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9161333961046468678962653 3435500235392425754610995)
        ·
          refine ⟨5153250353088638631916493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3435500235392425754610995 5153250353088638631916493)
          ·
            refine ⟨1932468882408239486968685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5153250353088638631916493 1932468882408239486968685)
            ·
              refine ⟨724675830903089807613257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1932468882408239486968685 724675830903089807613257)
              ·
                refine ⟨543506873177317355709943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 724675830903089807613257 543506873177317355709943)
                ·
                  refine ⟨815260309765976033564915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 543506873177317355709943 815260309765976033564915)
                  ·
                    refine ⟨1222890464648964050347373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 815260309765976033564915 1222890464648964050347373)
                    ·
                      refine ⟨458583924243361518880265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1222890464648964050347373 458583924243361518880265)
                      ·
                        rfl

theorem cell23_893089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_893089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893089 prefixEnd_893089 := by exact prefixLift 893089
  have htrace : WordTrace (prefixWord ++ tailWord_893089) baseStart_893089 baseEnd_893089 := by
    simpa [prefixWord, tailWord_893089, baseEnd_893089] using wordTrace_append hprefix tailTrace_893089
  have hstable : (prefixWord ++ tailWord_893089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893089).length < 2 ^ (prefixWord ++ tailWord_893089).sum := by decide
  have hdescent : baseEnd_893089 < baseStart_893089 := by decide
  rcases family_descends (prefixWord ++ tailWord_893089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893109 : List Nat := [1, 3, 3, 4, 2, 1, 1, 2, 1, 5]
def baseStart_893109 : Nat := 118140960795 + 893109 * 2 ^ 59
def prefixEnd_893109 : Nat := 4983230072969 + 3 ^ 40 * 893109 * 2
def baseEnd_893109 : Nat := 152864731285483813543391

theorem tailTrace_893109 : CollatzResearch.WordTrace tailWord_893109 prefixEnd_893109 152864731285483813543391 := by
  unfold tailWord_893109
  simp only [CollatzResearch.WordTrace]
  refine ⟨32574361321426098718706381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21716240880950732479137587 32574361321426098718706381)
  ·
    refine ⟨12215385495534787019514893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32574361321426098718706381 12215385495534787019514893)
    ·
      refine ⟨4580769560825545132318085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12215385495534787019514893 4580769560825545132318085)
      ·
        refine ⟨858894292654789712309641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4580769560825545132318085 858894292654789712309641)
        ·
          refine ⟨644170719491092284232231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 858894292654789712309641 644170719491092284232231)
          ·
            refine ⟨966256079236638426348347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644170719491092284232231 966256079236638426348347)
            ·
              refine ⟨1449384118854957639522521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 966256079236638426348347 1449384118854957639522521)
              ·
                refine ⟨1087038089141218229641891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1449384118854957639522521 1087038089141218229641891)
                ·
                  refine ⟨1630557133711827344462837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1087038089141218229641891 1630557133711827344462837)
                  ·
                    refine ⟨152864731285483813543391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1630557133711827344462837 152864731285483813543391)
                    ·
                      rfl

theorem cell23_893109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_893109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893109 prefixEnd_893109 := by exact prefixLift 893109
  have htrace : WordTrace (prefixWord ++ tailWord_893109) baseStart_893109 baseEnd_893109 := by
    simpa [prefixWord, tailWord_893109, baseEnd_893109] using wordTrace_append hprefix tailTrace_893109
  have hstable : (prefixWord ++ tailWord_893109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893109).length < 2 ^ (prefixWord ++ tailWord_893109).sum := by decide
  have hdescent : baseEnd_893109 < baseStart_893109 := by decide
  rcases family_descends (prefixWord ++ tailWord_893109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893122 : List Nat := [3, 5, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_893122 : Nat := 118140960795 + 893122 * 2 ^ 59
def prefixEnd_893122 : Nat := 4983230072969 + 3 ^ 40 * 893122 * 2
def baseEnd_893122 : Nat := 152866956368319963255871

theorem tailTrace_893122 : CollatzResearch.WordTrace tailWord_893122 prefixEnd_893122 152866956368319963255871 := by
  unfold tailWord_893122
  simp only [CollatzResearch.WordTrace]
  refine ⟨8143708867594750484732405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21716556980252667959286413 8143708867594750484732405)
  ·
    refine ⟨763472706337007857943663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8143708867594750484732405 763472706337007857943663)
    ·
      refine ⟨1145209059505511786915495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 763472706337007857943663 1145209059505511786915495)
      ·
        refine ⟨1717813589258267680373243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1145209059505511786915495 1717813589258267680373243)
        ·
          refine ⟨2576720383887401520559865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1717813589258267680373243 2576720383887401520559865)
          ·
            refine ⟨1932540287915551140419899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2576720383887401520559865 1932540287915551140419899)
            ·
              refine ⟨2898810431873326710629849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1932540287915551140419899 2898810431873326710629849)
              ·
                refine ⟨2174107823904995032972387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2898810431873326710629849 2174107823904995032972387)
                ·
                  refine ⟨3261161735857492549458581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2174107823904995032972387 3261161735857492549458581)
                  ·
                    refine ⟨152866956368319963255871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3261161735857492549458581 152866956368319963255871)
                    ·
                      rfl

theorem cell23_893122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_893122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893122 prefixEnd_893122 := by exact prefixLift 893122
  have htrace : WordTrace (prefixWord ++ tailWord_893122) baseStart_893122 baseEnd_893122 := by
    simpa [prefixWord, tailWord_893122, baseEnd_893122] using wordTrace_append hprefix tailTrace_893122
  have hstable : (prefixWord ++ tailWord_893122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893122).length < 2 ^ (prefixWord ++ tailWord_893122).sum := by decide
  have hdescent : baseEnd_893122 < baseStart_893122 := by decide
  rcases family_descends (prefixWord ++ tailWord_893122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893132 : List Nat := [2, 2, 1, 6, 1, 2, 1, 1, 1, 1, 5]
def baseStart_893132 : Nat := 118140960795 + 893132 * 2 ^ 59
def prefixEnd_893132 : Nat := 4983230072969 + 3 ^ 40 * 893132 * 2
def baseEnd_893132 : Nat := 458606003911504850642567

theorem tailTrace_893132 : CollatzResearch.WordTrace tailWord_893132 prefixEnd_893132 458606003911504850642567 := by
  unfold tailWord_893132
  simp only [CollatzResearch.WordTrace]
  refine ⟨16287600100171386823396825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21716800133561849097862433 16287600100171386823396825)
  ·
    refine ⟨12215700075128540117547619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16287600100171386823396825 12215700075128540117547619)
    ·
      refine ⟨18323550112692810176321429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12215700075128540117547619 18323550112692810176321429)
      ·
        refine ⟨858916411532475477015067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18323550112692810176321429 858916411532475477015067)
        ·
          refine ⟨1288374617298713215522601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 858916411532475477015067 1288374617298713215522601)
          ·
            refine ⟨966280962974034911641951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1288374617298713215522601 966280962974034911641951)
            ·
              refine ⟨1449421444461052367462927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 966280962974034911641951 1449421444461052367462927)
              ·
                refine ⟨2174132166691578551194391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1449421444461052367462927 2174132166691578551194391)
                ·
                  refine ⟨3261198250037367826791587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2174132166691578551194391 3261198250037367826791587)
                  ·
                    refine ⟨4891797375056051740187381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3261198250037367826791587 4891797375056051740187381)
                    ·
                      refine ⟨458606003911504850642567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4891797375056051740187381 458606003911504850642567)
                      ·
                        rfl

theorem cell23_893132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_893132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893132 prefixEnd_893132 := by exact prefixLift 893132
  have htrace : WordTrace (prefixWord ++ tailWord_893132) baseStart_893132 baseEnd_893132 := by
    simpa [prefixWord, tailWord_893132, baseEnd_893132] using wordTrace_append hprefix tailTrace_893132
  have hstable : (prefixWord ++ tailWord_893132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893132).length < 2 ^ (prefixWord ++ tailWord_893132).sum := by decide
  have hdescent : baseEnd_893132 < baseStart_893132 := by decide
  rcases family_descends (prefixWord ++ tailWord_893132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893145 : List Nat := [1, 2, 1, 2, 3, 1, 3, 4, 2, 1, 3]
def baseStart_893145 : Nat := 118140960795 + 893145 * 2 ^ 59
def prefixEnd_893145 : Nat := 4983230072969 + 3 ^ 40 * 893145 * 2
def baseEnd_893145 : Nat := 458612679160013299780007

theorem tailTrace_893145 : CollatzResearch.WordTrace tailWord_893145 prefixEnd_893145 458612679160013299780007 := by
  unfold tailWord_893145
  simp only [CollatzResearch.WordTrace]
  refine ⟨32575674349295676867016889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21717116232863784578011259 32575674349295676867016889)
  ·
    refine ⟨24431755761971757650262667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32575674349295676867016889 24431755761971757650262667)
    ·
      refine ⟨36647633642957636475394001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24431755761971757650262667 36647633642957636475394001)
      ·
        refine ⟨27485725232218227356545501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36647633642957636475394001 27485725232218227356545501)
        ·
          refine ⟨10307146962081835258704563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27485725232218227356545501 10307146962081835258704563)
          ·
            refine ⟨15460720443122752888056845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10307146962081835258704563 15460720443122752888056845)
            ·
              refine ⟨5797770166171032333021317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15460720443122752888056845 5797770166171032333021317)
              ·
                refine ⟨1087081906157068562441497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5797770166171032333021317 1087081906157068562441497)
                ·
                  refine ⟨815311429617801421831123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1087081906157068562441497 815311429617801421831123)
                  ·
                    refine ⟨1222967144426702132746685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 815311429617801421831123 1222967144426702132746685)
                    ·
                      refine ⟨458612679160013299780007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1222967144426702132746685 458612679160013299780007)
                      ·
                        rfl

theorem cell23_893145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 2, 1, 3].length) (baseStart_893145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893145 prefixEnd_893145 := by exact prefixLift 893145
  have htrace : WordTrace (prefixWord ++ tailWord_893145) baseStart_893145 baseEnd_893145 := by
    simpa [prefixWord, tailWord_893145, baseEnd_893145] using wordTrace_append hprefix tailTrace_893145
  have hstable : (prefixWord ++ tailWord_893145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893145).length < 2 ^ (prefixWord ++ tailWord_893145).sum := by decide
  have hdescent : baseEnd_893145 < baseStart_893145 := by decide
  rcases family_descends (prefixWord ++ tailWord_893145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893161 : List Nat := [1, 2, 1, 1, 1, 2, 2, 5, 2, 6]
def baseStart_893161 : Nat := 118140960795 + 893161 * 2 ^ 59
def prefixEnd_893161 : Nat := 4983230072969 + 3 ^ 40 * 893161 * 2
def baseEnd_893161 : Nat := 152873631616828412393311

theorem tailTrace_893161 : CollatzResearch.WordTrace tailWord_893161 prefixEnd_893161 152873631616828412393311 := by
  unfold tailWord_893161
  simp only [CollatzResearch.WordTrace]
  refine ⟨32576257917237711599599337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21717505278158474399732891 32576257917237711599599337)
  ·
    refine ⟨24432193437928283699699503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32576257917237711599599337 24432193437928283699699503)
    ·
      refine ⟨36648290156892425549549255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24432193437928283699699503 36648290156892425549549255)
      ·
        refine ⟨54972435235338638324323883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36648290156892425549549255 54972435235338638324323883)
        ·
          refine ⟨82458652853007957486485825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54972435235338638324323883 82458652853007957486485825)
          ·
            refine ⟨61843989639755968114864369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82458652853007957486485825 61843989639755968114864369)
            ·
              refine ⟨46382992229816976086148277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61843989639755968114864369 46382992229816976086148277)
              ·
                refine ⟨4348405521545341508076401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46382992229816976086148277 4348405521545341508076401)
                ·
                  refine ⟨3261304141159006131057301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4348405521545341508076401 3261304141159006131057301)
                  ·
                    refine ⟨152873631616828412393311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3261304141159006131057301 152873631616828412393311)
                    ·
                      rfl

theorem cell23_893161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 6].length) (baseStart_893161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893161 prefixEnd_893161 := by exact prefixLift 893161
  have htrace : WordTrace (prefixWord ++ tailWord_893161) baseStart_893161 baseEnd_893161 := by
    simpa [prefixWord, tailWord_893161, baseEnd_893161] using wordTrace_append hprefix tailTrace_893161
  have hstable : (prefixWord ++ tailWord_893161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893161).length < 2 ^ (prefixWord ++ tailWord_893161).sum := by decide
  have hdescent : baseEnd_893161 < baseStart_893161 := by decide
  rcases family_descends (prefixWord ++ tailWord_893161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893185 : List Nat := [1, 2, 4, 1, 1, 2, 1, 4, 1, 4, 2]
def baseStart_893185 : Nat := 118140960795 + 893185 * 2 ^ 59
def prefixEnd_893185 : Nat := 4983230072969 + 3 ^ 40 * 893185 * 2
def baseEnd_893185 : Nat := 458633218386193143279823

theorem tailTrace_893185 : CollatzResearch.WordTrace tailWord_893185 prefixEnd_893185 458633218386193143279823 := by
  unfold tailWord_893185
  simp only [CollatzResearch.WordTrace]
  refine ⟨32577133269150763698473009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21718088846100509132315339 32577133269150763698473009)
  ·
    refine ⟨24432849951863072773854757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32577133269150763698473009 24432849951863072773854757)
    ·
      refine ⟨4581159365974326145097767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24432849951863072773854757 4581159365974326145097767)
      ·
        refine ⟨6871739048961489217646651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4581159365974326145097767 6871739048961489217646651)
        ·
          refine ⟨10307608573442233826469977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6871739048961489217646651 10307608573442233826469977)
          ·
            refine ⟨7730706430081675369852483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10307608573442233826469977 7730706430081675369852483)
            ·
              refine ⟨11596059645122513054778725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7730706430081675369852483 11596059645122513054778725)
              ·
                refine ⟨2174261183460471197771011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11596059645122513054778725 2174261183460471197771011)
                ·
                  refine ⟨3261391775190706796656517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2174261183460471197771011 3261391775190706796656517)
                  ·
                    refine ⟨611510957848257524373097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3261391775190706796656517 611510957848257524373097)
                    ·
                      refine ⟨458633218386193143279823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 611510957848257524373097 458633218386193143279823)
                      ·
                        rfl

theorem cell23_893185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_893185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893185 prefixEnd_893185 := by exact prefixLift 893185
  have htrace : WordTrace (prefixWord ++ tailWord_893185) baseStart_893185 baseEnd_893185 := by
    simpa [prefixWord, tailWord_893185, baseEnd_893185] using wordTrace_append hprefix tailTrace_893185
  have hstable : (prefixWord ++ tailWord_893185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893185).length < 2 ^ (prefixWord ++ tailWord_893185).sum := by decide
  have hdescent : baseEnd_893185 < baseStart_893185 := by decide
  rcases family_descends (prefixWord ++ tailWord_893185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893198 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4]
def baseStart_893198 : Nat := 118140960795 + 893198 * 2 ^ 59
def prefixEnd_893198 : Nat := 4983230072969 + 3 ^ 40 * 893198 * 2
def baseEnd_893198 : Nat := 458639893634701592417263

theorem tailTrace_893198 : CollatzResearch.WordTrace tailWord_893198 prefixEnd_893198 458639893634701592417263 := by
  unfold tailWord_893198
  simp only [CollatzResearch.WordTrace]
  refine ⟨4072200927262958364837031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21718404945402444612464165 4072200927262958364837031)
  ·
    refine ⟨6108301390894437547255547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4072200927262958364837031 6108301390894437547255547)
    ·
      refine ⟨9162452086341656320883321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6108301390894437547255547 9162452086341656320883321)
      ·
        refine ⟨6871839064756242240662491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9162452086341656320883321 6871839064756242240662491)
        ·
          refine ⟨10307758597134363360993737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6871839064756242240662491 10307758597134363360993737)
          ·
            refine ⟨7730818947850772520745303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10307758597134363360993737 7730818947850772520745303)
            ·
              refine ⟨11596228421776158781117955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7730818947850772520745303 11596228421776158781117955)
              ·
                refine ⟨17394342632664238171676933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11596228421776158781117955 17394342632664238171676933)
                ·
                  refine ⟨3261439243624544657189425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17394342632664238171676933 3261439243624544657189425)
                  ·
                    refine ⟨2446079432718408492892069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3261439243624544657189425 2446079432718408492892069)
                    ·
                      refine ⟨458639893634701592417263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2446079432718408492892069 458639893634701592417263)
                      ·
                        rfl

theorem cell23_893198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_893198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893198 prefixEnd_893198 := by exact prefixLift 893198
  have htrace : WordTrace (prefixWord ++ tailWord_893198) baseStart_893198 baseEnd_893198 := by
    simpa [prefixWord, tailWord_893198, baseEnd_893198] using wordTrace_append hprefix tailTrace_893198
  have hstable : (prefixWord ++ tailWord_893198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893198).length < 2 ^ (prefixWord ++ tailWord_893198).sum := by decide
  have hdescent : baseEnd_893198 < baseStart_893198 := by decide
  rcases family_descends (prefixWord ++ tailWord_893198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893208 : List Nat := [2, 1, 2, 3, 1, 2, 4, 1, 7]
def baseStart_893208 : Nat := 118140960795 + 893208 * 2 ^ 59
def prefixEnd_893208 : Nat := 4983230072969 + 3 ^ 40 * 893208 * 2
def baseEnd_893208 : Nat := 50960558715694061476913

theorem tailTrace_893208 : CollatzResearch.WordTrace tailWord_893208 prefixEnd_893208 50960558715694061476913 := by
  unfold tailWord_893208
  simp only [CollatzResearch.WordTrace]
  refine ⟨16288986074033719313280139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21718648098711625751040185 16288986074033719313280139)
  ·
    refine ⟨24433479111050578969920209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16288986074033719313280139 24433479111050578969920209)
    ·
      refine ⟨18325109333287934227440157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24433479111050578969920209 18325109333287934227440157)
      ·
        refine ⟨6871915999982975335290059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18325109333287934227440157 6871915999982975335290059)
        ·
          refine ⟨10307873999974463002935089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6871915999982975335290059 10307873999974463002935089)
          ·
            refine ⟨7730905499980847252201317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10307873999974463002935089 7730905499980847252201317)
            ·
              refine ⟨1449544781246408859787747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7730905499980847252201317 1449544781246408859787747)
              ·
                refine ⟨2174317171869613289681621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1449544781246408859787747 2174317171869613289681621)
                ·
                  refine ⟨50960558715694061476913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2174317171869613289681621 50960558715694061476913)
                  ·
                    rfl

theorem cell23_893208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 7].length) (baseStart_893208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893208 prefixEnd_893208 := by exact prefixLift 893208
  have htrace : WordTrace (prefixWord ++ tailWord_893208) baseStart_893208 baseEnd_893208 := by
    simpa [prefixWord, tailWord_893208, baseEnd_893208] using wordTrace_append hprefix tailTrace_893208
  have hstable : (prefixWord ++ tailWord_893208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893208).length < 2 ^ (prefixWord ++ tailWord_893208).sum := by decide
  have hdescent : baseEnd_893208 < baseStart_893208 := by decide
  rcases family_descends (prefixWord ++ tailWord_893208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893219 : List Nat := [1, 1, 1, 4, 2, 2, 5, 1, 2, 2, 2]
def baseStart_893219 : Nat := 118140960795 + 893219 * 2 ^ 59
def prefixEnd_893219 : Nat := 4983230072969 + 3 ^ 40 * 893219 * 2
def baseEnd_893219 : Nat := 458650676728446010254667

theorem tailTrace_893219 : CollatzResearch.WordTrace tailWord_893219 prefixEnd_893219 458650676728446010254667 := by
  unfold tailWord_893219
  simp only [CollatzResearch.WordTrace]
  refine ⟨32578373351027587505210711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21718915567351725003473807 32578373351027587505210711)
  ·
    refine ⟨48867560026541381257816067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32578373351027587505210711 48867560026541381257816067)
    ·
      refine ⟨73301340039812071886724101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48867560026541381257816067 73301340039812071886724101)
      ·
        refine ⟨13744001257464763478760769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73301340039812071886724101 13744001257464763478760769)
        ·
          refine ⟨10308000943098572609070577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13744001257464763478760769 10308000943098572609070577)
          ·
            refine ⟨7731000707323929456802933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10308000943098572609070577 7731000707323929456802933)
            ·
              refine ⟨724781316311618386575275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7731000707323929456802933 724781316311618386575275)
              ·
                refine ⟨1087171974467427579862913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 724781316311618386575275 1087171974467427579862913)
                ·
                  refine ⟨815378980850570684897185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1087171974467427579862913 815378980850570684897185)
                  ·
                    refine ⟨611534235637928013672889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 815378980850570684897185 611534235637928013672889)
                    ·
                      refine ⟨458650676728446010254667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 611534235637928013672889 458650676728446010254667)
                      ·
                        rfl

theorem cell23_893219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 2, 2, 2].length) (baseStart_893219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893219 prefixEnd_893219 := by exact prefixLift 893219
  have htrace : WordTrace (prefixWord ++ tailWord_893219) baseStart_893219 baseEnd_893219 := by
    simpa [prefixWord, tailWord_893219, baseEnd_893219] using wordTrace_append hprefix tailTrace_893219
  have hstable : (prefixWord ++ tailWord_893219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893219).length < 2 ^ (prefixWord ++ tailWord_893219).sum := by decide
  have hdescent : baseEnd_893219 < baseStart_893219 := by decide
  rcases family_descends (prefixWord ++ tailWord_893219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893223 : List Nat := [1, 1, 8, 1, 1, 1, 2, 2, 1, 3, 2]
def baseStart_893223 : Nat := 118140960795 + 893223 * 2 ^ 59
def prefixEnd_893223 : Nat := 4983230072969 + 3 ^ 40 * 893223 * 2
def baseEnd_893223 : Nat := 458652730651063994604649

theorem tailTrace_893223 : CollatzResearch.WordTrace tailWord_893223 prefixEnd_893223 458652730651063994604649 := by
  unfold tailWord_893223
  simp only [CollatzResearch.WordTrace]
  refine ⟨32578519243013096188356323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21719012828675397458904215 32578519243013096188356323)
  ·
    refine ⟨48867778864519644282534485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32578519243013096188356323 48867778864519644282534485)
    ·
      refine ⟨572669283568589581435951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 48867778864519644282534485 572669283568589581435951)
      ·
        refine ⟨859003925352884372153927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572669283568589581435951 859003925352884372153927)
        ·
          refine ⟨1288505888029326558230891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859003925352884372153927 1288505888029326558230891)
          ·
            refine ⟨1932758832043989837346337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1288505888029326558230891 1932758832043989837346337)
            ·
              refine ⟨1449569124032992378009753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1932758832043989837346337 1449569124032992378009753)
              ·
                refine ⟨1087176843024744283507315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1449569124032992378009753 1087176843024744283507315)
                ·
                  refine ⟨1630765264537116425260973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1087176843024744283507315 1630765264537116425260973)
                  ·
                    refine ⟨611536974201418659472865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1630765264537116425260973 611536974201418659472865)
                    ·
                      refine ⟨458652730651063994604649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 611536974201418659472865 458652730651063994604649)
                      ·
                        rfl

theorem cell23_893223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_893223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893223 prefixEnd_893223 := by exact prefixLift 893223
  have htrace : WordTrace (prefixWord ++ tailWord_893223) baseStart_893223 baseEnd_893223 := by
    simpa [prefixWord, tailWord_893223, baseEnd_893223] using wordTrace_append hprefix tailTrace_893223
  have hstable : (prefixWord ++ tailWord_893223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893223).length < 2 ^ (prefixWord ++ tailWord_893223).sum := by decide
  have hdescent : baseEnd_893223 < baseStart_893223 := by decide
  rcases family_descends (prefixWord ++ tailWord_893223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893242 : List Nat := [3, 1, 1, 1, 4, 4, 1, 3, 5]
def baseStart_893242 : Nat := 118140960795 + 893242 * 2 ^ 59
def prefixEnd_893242 : Nat := 4983230072969 + 3 ^ 40 * 893242 * 2
def baseEnd_893242 : Nat := 50962498531499935585229

theorem tailTrace_893242 : CollatzResearch.WordTrace tailWord_893242 prefixEnd_893242 50962498531499935585229 := by
  unfold tailWord_893242
  simp only [CollatzResearch.WordTrace]
  refine ⟨8144803057486065608324495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21719474819962841622198653 8144803057486065608324495)
  ·
    refine ⟨12217204586229098412486743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8144803057486065608324495 12217204586229098412486743)
    ·
      refine ⟨18325806879343647618730115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12217204586229098412486743 18325806879343647618730115)
      ·
        refine ⟨27488710319015471428095173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18325806879343647618730115 27488710319015471428095173)
        ·
          refine ⟨5154133184815400892767845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27488710319015471428095173 5154133184815400892767845)
          ·
            refine ⟨966399972152887667393971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5154133184815400892767845 966399972152887667393971)
            ·
              refine ⟨1449599958229331501090957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 966399972152887667393971 1449599958229331501090957)
              ·
                refine ⟨543599984335999312909109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1449599958229331501090957 543599984335999312909109)
                ·
                  refine ⟨50962498531499935585229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 543599984335999312909109 50962498531499935585229)
                  ·
                    rfl

theorem cell23_893242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 3, 5].length) (baseStart_893242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893242 prefixEnd_893242 := by exact prefixLift 893242
  have htrace : WordTrace (prefixWord ++ tailWord_893242) baseStart_893242 baseEnd_893242 := by
    simpa [prefixWord, tailWord_893242, baseEnd_893242] using wordTrace_append hprefix tailTrace_893242
  have hstable : (prefixWord ++ tailWord_893242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893242).length < 2 ^ (prefixWord ++ tailWord_893242).sum := by decide
  have hdescent : baseEnd_893242 < baseStart_893242 := by decide
  rcases family_descends (prefixWord ++ tailWord_893242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893292 : List Nat := [2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 4]
def baseStart_893292 : Nat := 118140960795 + 893292 * 2 ^ 59
def prefixEnd_893292 : Nat := 4983230072969 + 3 ^ 40 * 893292 * 2
def baseEnd_893292 : Nat := 458688160816224224641831

theorem tailTrace_893292 : CollatzResearch.WordTrace tailWord_893292 prefixEnd_893292 458688160816224224641831 := by
  unfold tailWord_893292
  simp only [CollatzResearch.WordTrace]
  refine ⟨16290517939881560486309065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21720690586508747315078753 16290517939881560486309065)
  ·
    refine ⟨12217888454911170364731799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16290517939881560486309065 12217888454911170364731799)
    ·
      refine ⟨18326832682366755547097699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12217888454911170364731799 18326832682366755547097699)
      ·
        refine ⟨27490249023550133320646549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18326832682366755547097699 27490249023550133320646549)
        ·
          refine ⟨1288605422978912499405307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27490249023550133320646549 1288605422978912499405307)
          ·
            refine ⟨1932908134468368749107961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1288605422978912499405307 1932908134468368749107961)
            ·
              refine ⟨1449681100851276561830971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1932908134468368749107961 1449681100851276561830971)
              ·
                refine ⟨2174521651276914842746457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1449681100851276561830971 2174521651276914842746457)
                ·
                  refine ⟨1630891238457686132059843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2174521651276914842746457 1630891238457686132059843)
                  ·
                    refine ⟨2446336857686529198089765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1630891238457686132059843 2446336857686529198089765)
                    ·
                      refine ⟨458688160816224224641831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2446336857686529198089765 458688160816224224641831)
                      ·
                        rfl

theorem cell23_893292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 4].length) (baseStart_893292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893292 prefixEnd_893292 := by exact prefixLift 893292
  have htrace : WordTrace (prefixWord ++ tailWord_893292) baseStart_893292 baseEnd_893292 := by
    simpa [prefixWord, tailWord_893292, baseEnd_893292] using wordTrace_append hprefix tailTrace_893292
  have hstable : (prefixWord ++ tailWord_893292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893292).length < 2 ^ (prefixWord ++ tailWord_893292).sum := by decide
  have hdescent : baseEnd_893292 < baseStart_893292 := by decide
  rcases family_descends (prefixWord ++ tailWord_893292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893385 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 5, 2, 3]
def baseStart_893385 : Nat := 118140960795 + 893385 * 2 ^ 59
def prefixEnd_893385 : Nat := 4983230072969 + 3 ^ 40 * 893385 * 2
def baseEnd_893385 : Nat := 458735914517092360778903

theorem tailTrace_893385 : CollatzResearch.WordTrace tailWord_893385 prefixEnd_893385 458735914517092360778903 := by
  unfold tailWord_893385
  simp only [CollatzResearch.WordTrace]
  refine ⟨32584427868426197855753609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21722951912284131903835739 32584427868426197855753609)
  ·
    refine ⟨24438320901319648391815207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32584427868426197855753609 24438320901319648391815207)
    ·
      refine ⟨36657481351979472587722811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24438320901319648391815207 36657481351979472587722811)
      ·
        refine ⟨54986222027969208881584217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36657481351979472587722811 54986222027969208881584217)
        ·
          refine ⟨41239666520976906661188163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54986222027969208881584217 41239666520976906661188163)
          ·
            refine ⟨61859499781465359991782245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41239666520976906661188163 61859499781465359991782245)
            ·
              refine ⟨11598656209024754998459171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61859499781465359991782245 11598656209024754998459171)
              ·
                refine ⟨17397984313537132497688757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11598656209024754998459171 17397984313537132497688757)
                ·
                  refine ⟨1631061029394106171658321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17397984313537132497688757 1631061029394106171658321)
                  ·
                    refine ⟨1223295772045579628743741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1631061029394106171658321 1223295772045579628743741)
                    ·
                      refine ⟨458735914517092360778903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1223295772045579628743741 458735914517092360778903)
                      ·
                        rfl

theorem cell23_893385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 2, 3].length) (baseStart_893385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893385 prefixEnd_893385 := by exact prefixLift 893385
  have htrace : WordTrace (prefixWord ++ tailWord_893385) baseStart_893385 baseEnd_893385 := by
    simpa [prefixWord, tailWord_893385, baseEnd_893385] using wordTrace_append hprefix tailTrace_893385
  have hstable : (prefixWord ++ tailWord_893385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893385).length < 2 ^ (prefixWord ++ tailWord_893385).sum := by decide
  have hdescent : baseEnd_893385 < baseStart_893385 := by decide
  rcases family_descends (prefixWord ++ tailWord_893385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893405 : List Nat := [1, 4, 3, 1, 1, 1, 3, 9]
def baseStart_893405 : Nat := 118140960795 + 893405 * 2 ^ 59
def prefixEnd_893405 : Nat := 4983230072969 + 3 ^ 40 * 893405 * 2
def baseEnd_893405 : Nat := 16990599412228973426993

theorem tailTrace_893405 : CollatzResearch.WordTrace tailWord_893405 prefixEnd_893405 16990599412228973426993 := by
  unfold tailWord_893405
  simp only [CollatzResearch.WordTrace]
  refine ⟨32585157328353741271481669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21723438218902494180987779 32585157328353741271481669)
  ·
    refine ⟨6109716999066326488402813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32585157328353741271481669 6109716999066326488402813)
    ·
      refine ⟨2291143874649872433151055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6109716999066326488402813 2291143874649872433151055)
      ·
        refine ⟨3436715811974808649726583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2291143874649872433151055 3436715811974808649726583)
        ·
          refine ⟨5155073717962212974589875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3436715811974808649726583 5155073717962212974589875)
          ·
            refine ⟨7732610576943319461884813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5155073717962212974589875 7732610576943319461884813)
            ·
              refine ⟨2899728966353744798206805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7732610576943319461884813 2899728966353744798206805)
              ·
                refine ⟨16990599412228973426993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2899728966353744798206805 16990599412228973426993)
                ·
                  rfl

theorem cell23_893405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 9].length) (baseStart_893405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893405 prefixEnd_893405 := by exact prefixLift 893405
  have htrace : WordTrace (prefixWord ++ tailWord_893405) baseStart_893405 baseEnd_893405 := by
    simpa [prefixWord, tailWord_893405, baseEnd_893405] using wordTrace_append hprefix tailTrace_893405
  have hstable : (prefixWord ++ tailWord_893405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893405).length < 2 ^ (prefixWord ++ tailWord_893405).sum := by decide
  have hdescent : baseEnd_893405 < baseStart_893405 := by decide
  rcases family_descends (prefixWord ++ tailWord_893405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893432 : List Nat := [2, 1, 2, 1, 1, 4, 1, 3, 4, 1, 3]
def baseStart_893432 : Nat := 118140960795 + 893432 * 2 ^ 59
def prefixEnd_893432 : Nat := 4983230072969 + 3 ^ 40 * 893432 * 2
def baseEnd_893432 : Nat := 458760048107853676891187

theorem tailTrace_893432 : CollatzResearch.WordTrace tailWord_893432 prefixEnd_893432 458760048107853676891187 := by
  unfold tailWord_893432
  simp only [CollatzResearch.WordTrace]
  refine ⟨16293071049627962441357275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21724094732837283255143033 16293071049627962441357275)
  ·
    refine ⟨24439606574441943662035913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16293071049627962441357275 24439606574441943662035913)
    ·
      refine ⟨18329704930831457746526935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24439606574441943662035913 18329704930831457746526935)
      ·
        refine ⟨27494557396247186619790403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18329704930831457746526935 27494557396247186619790403)
        ·
          refine ⟨41241836094370779929685605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27494557396247186619790403 41241836094370779929685605)
          ·
            refine ⟨7732844267694521236816051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41241836094370779929685605 7732844267694521236816051)
            ·
              refine ⟨11599266401541781855224077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7732844267694521236816051 11599266401541781855224077)
              ·
                refine ⟨4349724900578168195709029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11599266401541781855224077 4349724900578168195709029)
                ·
                  refine ⟨815573418858406536695443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4349724900578168195709029 815573418858406536695443)
                  ·
                    refine ⟨1223360128287609805043165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 815573418858406536695443 1223360128287609805043165)
                    ·
                      refine ⟨458760048107853676891187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1223360128287609805043165 458760048107853676891187)
                      ·
                        rfl

theorem cell23_893432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 4, 1, 3].length) (baseStart_893432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893432 prefixEnd_893432 := by exact prefixLift 893432
  have htrace : WordTrace (prefixWord ++ tailWord_893432) baseStart_893432 baseEnd_893432 := by
    simpa [prefixWord, tailWord_893432, baseEnd_893432] using wordTrace_append hprefix tailTrace_893432
  have hstable : (prefixWord ++ tailWord_893432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893432).length < 2 ^ (prefixWord ++ tailWord_893432).sum := by decide
  have hdescent : baseEnd_893432 < baseStart_893432 := by decide
  rcases family_descends (prefixWord ++ tailWord_893432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893446 : List Nat := [6, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_893446 : Nat := 118140960795 + 893446 * 2 ^ 59
def prefixEnd_893446 : Nat := 4983230072969 + 3 ^ 40 * 893446 * 2
def baseEnd_893446 : Nat := 458767236837016622116123

theorem tailTrace_893446 : CollatzResearch.WordTrace tailWord_893446 prefixEnd_893446 458767236837016622116123 := by
  unfold tailWord_893446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1018332897537662664803881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21724435147470136849149461 1018332897537662664803881)
  ·
    refine ⟨763749673153246998602911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1018332897537662664803881 763749673153246998602911)
    ·
      refine ⟨1145624509729870497904367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 763749673153246998602911 1145624509729870497904367)
      ·
        refine ⟨1718436764594805746856551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1145624509729870497904367 1718436764594805746856551)
        ·
          refine ⟨2577655146892208620284827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1718436764594805746856551 2577655146892208620284827)
          ·
            refine ⟨3866482720338312930427241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2577655146892208620284827 3866482720338312930427241)
            ·
              refine ⟨2899862040253734697820431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3866482720338312930427241 2899862040253734697820431)
              ·
                refine ⟨4349793060380602046730647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2899862040253734697820431 4349793060380602046730647)
                ·
                  refine ⟨6524689590570903070095971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4349793060380602046730647 6524689590570903070095971)
                  ·
                    refine ⟨9787034385856354605143957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6524689590570903070095971 9787034385856354605143957)
                    ·
                      refine ⟨458767236837016622116123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9787034385856354605143957 458767236837016622116123)
                      ·
                        rfl

theorem cell23_893446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_893446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893446 prefixEnd_893446 := by exact prefixLift 893446
  have htrace : WordTrace (prefixWord ++ tailWord_893446) baseStart_893446 baseEnd_893446 := by
    simpa [prefixWord, tailWord_893446, baseEnd_893446] using wordTrace_append hprefix tailTrace_893446
  have hstable : (prefixWord ++ tailWord_893446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893446).length < 2 ^ (prefixWord ++ tailWord_893446).sum := by decide
  have hdescent : baseEnd_893446 < baseStart_893446 := by decide
  rcases family_descends (prefixWord ++ tailWord_893446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893453 : List Nat := [1, 7, 1, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_893453 : Nat := 118140960795 + 893453 * 2 ^ 59
def prefixEnd_893453 : Nat := 4983230072969 + 3 ^ 40 * 893453 * 2
def baseEnd_893453 : Nat := 458770831201598094728591

theorem tailTrace_893453 : CollatzResearch.WordTrace tailWord_893453 prefixEnd_893453 458770831201598094728591 := by
  unfold tailWord_893453
  simp only [CollatzResearch.WordTrace]
  refine ⟨32586908032179845469229013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21724605354786563646152675 32586908032179845469229013)
  ·
    refine ⟨763755657004215128185055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 32586908032179845469229013 763755657004215128185055)
    ·
      refine ⟨1145633485506322692277583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 763755657004215128185055 1145633485506322692277583)
      ·
        refine ⟨1718450228259484038416375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1145633485506322692277583 1718450228259484038416375)
        ·
          refine ⟨2577675342389226057624563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1718450228259484038416375 2577675342389226057624563)
          ·
            refine ⟨3866513013583839086436845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2577675342389226057624563 3866513013583839086436845)
            ·
              refine ⟨1449942380093939657413817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3866513013583839086436845 1449942380093939657413817)
              ·
                refine ⟨1087456785070454743060363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1449942380093939657413817 1087456785070454743060363)
                ·
                  refine ⟨1631185177605682114590545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1087456785070454743060363 1631185177605682114590545)
                  ·
                    refine ⟨1223388883204261585942909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1631185177605682114590545 1223388883204261585942909)
                    ·
                      refine ⟨458770831201598094728591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1223388883204261585942909 458770831201598094728591)
                      ·
                        rfl

theorem cell23_893453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_893453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893453 prefixEnd_893453 := by exact prefixLift 893453
  have htrace : WordTrace (prefixWord ++ tailWord_893453) baseStart_893453 baseEnd_893453 := by
    simpa [prefixWord, tailWord_893453, baseEnd_893453] using wordTrace_append hprefix tailTrace_893453
  have hstable : (prefixWord ++ tailWord_893453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893453).length < 2 ^ (prefixWord ++ tailWord_893453).sum := by decide
  have hdescent : baseEnd_893453 < baseStart_893453 := by decide
  rcases family_descends (prefixWord ++ tailWord_893453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893489 : List Nat := [1, 2, 2, 3, 1, 1, 2, 3, 4, 2, 2]
def baseStart_893489 : Nat := 118140960795 + 893489 * 2 ^ 59
def prefixEnd_893489 : Nat := 4983230072969 + 3 ^ 40 * 893489 * 2
def baseEnd_893489 : Nat := 458789316505159953878425

theorem tailTrace_893489 : CollatzResearch.WordTrace tailWord_893489 prefixEnd_893489 458789316505159953878425 := by
  unfold tailWord_893489
  simp only [CollatzResearch.WordTrace]
  refine ⟨32588221060049423617539521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21725480706699615745026347 32588221060049423617539521)
  ·
    refine ⟨24441165795037067713154641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32588221060049423617539521 24441165795037067713154641)
    ·
      refine ⟨18330874346277800784865981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24441165795037067713154641 18330874346277800784865981)
      ·
        refine ⟨6874077879854175294324743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18330874346277800784865981 6874077879854175294324743)
        ·
          refine ⟨10311116819781262941487115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6874077879854175294324743 10311116819781262941487115)
          ·
            refine ⟨15466675229671894412230673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10311116819781262941487115 15466675229671894412230673)
            ·
              refine ⟨11600006422253920809173005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15466675229671894412230673 11600006422253920809173005)
              ·
                refine ⟨4350002408345220303439877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11600006422253920809173005 4350002408345220303439877)
                ·
                  refine ⟨815625451564728806894977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4350002408345220303439877 815625451564728806894977)
                  ·
                    refine ⟨611719088673546605171233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 815625451564728806894977 611719088673546605171233)
                    ·
                      refine ⟨458789316505159953878425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 611719088673546605171233 458789316505159953878425)
                      ·
                        rfl

theorem cell23_893489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_893489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893489 prefixEnd_893489 := by exact prefixLift 893489
  have htrace : WordTrace (prefixWord ++ tailWord_893489) baseStart_893489 baseEnd_893489 := by
    simpa [prefixWord, tailWord_893489, baseEnd_893489] using wordTrace_append hprefix tailTrace_893489
  have hstable : (prefixWord ++ tailWord_893489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893489).length < 2 ^ (prefixWord ++ tailWord_893489).sum := by decide
  have hdescent : baseEnd_893489 < baseStart_893489 := by decide
  rcases family_descends (prefixWord ++ tailWord_893489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893495 : List Nat := [1, 1, 3, 1, 2, 3, 2, 3, 7]
def baseStart_893495 : Nat := 118140960795 + 893495 * 2 ^ 59
def prefixEnd_893495 : Nat := 4983230072969 + 3 ^ 40 * 893495 * 2
def baseEnd_893495 : Nat := 50976933043231881155933

theorem tailTrace_893495 : CollatzResearch.WordTrace tailWord_893495 prefixEnd_893495 50976933043231881155933 := by
  unfold tailWord_893495
  simp only [CollatzResearch.WordTrace]
  refine ⟨32588439898027686642257939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21725626598685124428171959 32588439898027686642257939)
  ·
    refine ⟨48882659847041529963386909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32588439898027686642257939 48882659847041529963386909)
    ·
      refine ⟨18330997442640573736270091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48882659847041529963386909 18330997442640573736270091)
      ·
        refine ⟨27496496163960860604405137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18330997442640573736270091 27496496163960860604405137)
        ·
          refine ⟨20622372122970645453303853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27496496163960860604405137 20622372122970645453303853)
          ·
            refine ⟨7733389546113992044988945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20622372122970645453303853 7733389546113992044988945)
            ·
              refine ⟨5800042159585494033741709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7733389546113992044988945 5800042159585494033741709)
              ·
                refine ⟨2175015809844560262653141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5800042159585494033741709 2175015809844560262653141)
                ·
                  refine ⟨50976933043231881155933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2175015809844560262653141 50976933043231881155933)
                  ·
                    rfl

theorem cell23_893495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 7].length) (baseStart_893495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893495 prefixEnd_893495 := by exact prefixLift 893495
  have htrace : WordTrace (prefixWord ++ tailWord_893495) baseStart_893495 baseEnd_893495 := by
    simpa [prefixWord, tailWord_893495, baseEnd_893495] using wordTrace_append hprefix tailTrace_893495
  have hstable : (prefixWord ++ tailWord_893495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893495).length < 2 ^ (prefixWord ++ tailWord_893495).sum := by decide
  have hdescent : baseEnd_893495 < baseStart_893495 := by decide
  rcases family_descends (prefixWord ++ tailWord_893495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893522 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 1, 5, 3]
def baseStart_893522 : Nat := 118140960795 + 893522 * 2 ^ 59
def prefixEnd_893522 : Nat := 4983230072969 + 3 ^ 40 * 893522 * 2
def baseEnd_893522 : Nat := 458806261366758324765773

theorem tailTrace_893522 : CollatzResearch.WordTrace tailWord_893522 prefixEnd_893522 458806261366758324765773 := by
  unfold tailWord_893522
  simp only [CollatzResearch.WordTrace]
  refine ⟨8147356167232467563372705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21726283112619913502327213 8147356167232467563372705)
  ·
    refine ⟨6110517125424350672529529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8147356167232467563372705 6110517125424350672529529)
    ·
      refine ⟨4582887844068263004397147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6110517125424350672529529 4582887844068263004397147)
      ·
        refine ⟨6874331766102394506595721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4582887844068263004397147 6874331766102394506595721)
        ·
          refine ⟨5155748824576795879946791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6874331766102394506595721 5155748824576795879946791)
          ·
            refine ⟨7733623236865193819920187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5155748824576795879946791 7733623236865193819920187)
            ·
              refine ⟨11600434855297790729880281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7733623236865193819920187 11600434855297790729880281)
              ·
                refine ⟨8700326141473343047410211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11600434855297790729880281 8700326141473343047410211)
                ·
                  refine ⟨13050489212210014571115317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8700326141473343047410211 13050489212210014571115317)
                  ·
                    refine ⟨1223483363644688866042061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13050489212210014571115317 1223483363644688866042061)
                    ·
                      refine ⟨458806261366758324765773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1223483363644688866042061 458806261366758324765773)
                      ·
                        rfl

theorem cell23_893522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_893522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893522 prefixEnd_893522 := by exact prefixLift 893522
  have htrace : WordTrace (prefixWord ++ tailWord_893522) baseStart_893522 baseEnd_893522 := by
    simpa [prefixWord, tailWord_893522, baseEnd_893522] using wordTrace_append hprefix tailTrace_893522
  have hstable : (prefixWord ++ tailWord_893522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893522).length < 2 ^ (prefixWord ++ tailWord_893522).sum := by decide
  have hdescent : baseEnd_893522 < baseStart_893522 := by decide
  rcases family_descends (prefixWord ++ tailWord_893522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893534 : List Nat := [4, 4, 1, 2, 2, 1, 1, 2, 2, 1, 3]
def baseStart_893534 : Nat := 118140960795 + 893534 * 2 ^ 59
def prefixEnd_893534 : Nat := 4983230072969 + 3 ^ 40 * 893534 * 2
def baseEnd_893534 : Nat := 458812423134612277815719

theorem tailTrace_893534 : CollatzResearch.WordTrace tailWord_893534 prefixEnd_893534 458812423134612277815719 := by
  unfold tailWord_893534
  simp only [CollatzResearch.WordTrace]
  refine ⟨4073732793110799537865957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21726574896590930868618437 4073732793110799537865957)
  ·
    refine ⟨763824898708274913349867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4073732793110799537865957 763824898708274913349867)
    ·
      refine ⟨1145737348062412370024801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 763824898708274913349867 1145737348062412370024801)
      ·
        refine ⟨859303011046809277518601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1145737348062412370024801 859303011046809277518601)
        ·
          refine ⟨644477258285106958138951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 859303011046809277518601 644477258285106958138951)
          ·
            refine ⟨966715887427660437208427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644477258285106958138951 966715887427660437208427)
            ·
              refine ⟨1450073831141490655812641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 966715887427660437208427 1450073831141490655812641)
              ·
                refine ⟨1087555373356117991859481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1450073831141490655812641 1087555373356117991859481)
                ·
                  refine ⟨815666530017088493894611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1087555373356117991859481 815666530017088493894611)
                  ·
                    refine ⟨1223499795025632740841917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 815666530017088493894611 1223499795025632740841917)
                    ·
                      refine ⟨458812423134612277815719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1223499795025632740841917 458812423134612277815719)
                      ·
                        rfl

theorem cell23_893534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_893534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893534 prefixEnd_893534 := by exact prefixLift 893534
  have htrace : WordTrace (prefixWord ++ tailWord_893534) baseStart_893534 baseEnd_893534 := by
    simpa [prefixWord, tailWord_893534, baseEnd_893534] using wordTrace_append hprefix tailTrace_893534
  have hstable : (prefixWord ++ tailWord_893534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893534).length < 2 ^ (prefixWord ++ tailWord_893534).sum := by decide
  have hdescent : baseEnd_893534 < baseStart_893534 := by decide
  rcases family_descends (prefixWord ++ tailWord_893534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893535 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 5]
def baseStart_893535 : Nat := 118140960795 + 893535 * 2 ^ 59
def prefixEnd_893535 : Nat := 4983230072969 + 3 ^ 40 * 893535 * 2
def baseEnd_893535 : Nat := 458812936615266773903213

theorem tailTrace_893535 : CollatzResearch.WordTrace tailWord_893535 prefixEnd_893535 458812936615266773903213 := by
  unfold tailWord_893535
  simp only [CollatzResearch.WordTrace]
  refine ⟨32589898817882773473714059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21726599211921848982476039 32589898817882773473714059)
  ·
    refine ⟨48884848226824160210571089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32589898817882773473714059 48884848226824160210571089)
    ·
      refine ⟨36663636170118120157928317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48884848226824160210571089 36663636170118120157928317)
      ·
        refine ⟨13748863563794295059223119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36663636170118120157928317 13748863563794295059223119)
        ·
          refine ⟨20623295345691442588834679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13748863563794295059223119 20623295345691442588834679)
          ·
            refine ⟨30934943018537163883252019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20623295345691442588834679 30934943018537163883252019)
            ·
              refine ⟨46402414527805745824878029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30934943018537163883252019 46402414527805745824878029)
              ·
                refine ⟨17400905447927154684329261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46402414527805745824878029 17400905447927154684329261)
                ·
                  refine ⟨6525339542972683006623473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17400905447927154684329261 6525339542972683006623473)
                  ·
                    refine ⟨4894004657229512254967605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6525339542972683006623473 4894004657229512254967605)
                    ·
                      refine ⟨458812936615266773903213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4894004657229512254967605 458812936615266773903213)
                      ·
                        rfl

theorem cell23_893535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_893535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893535 prefixEnd_893535 := by exact prefixLift 893535
  have htrace : WordTrace (prefixWord ++ tailWord_893535) baseStart_893535 baseEnd_893535 := by
    simpa [prefixWord, tailWord_893535, baseEnd_893535] using wordTrace_append hprefix tailTrace_893535
  have hstable : (prefixWord ++ tailWord_893535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893535).length < 2 ^ (prefixWord ++ tailWord_893535).sum := by decide
  have hdescent : baseEnd_893535 < baseStart_893535 := by decide
  rcases family_descends (prefixWord ++ tailWord_893535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893619 : List Nat := [1, 1, 1, 2, 3, 4, 4, 1, 6]
def baseStart_893619 : Nat := 118140960795 + 893619 * 2 ^ 59
def prefixEnd_893619 : Nat := 4983230072969 + 3 ^ 40 * 893619 * 2
def baseEnd_893619 : Nat := 50984007665582716139203

theorem tailTrace_893619 : CollatzResearch.WordTrace tailWord_893619 prefixEnd_893619 50984007665582716139203 := by
  unfold tailWord_893619
  simp only [CollatzResearch.WordTrace]
  refine ⟨32592962549578455819771911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21728641699718970546514607 32592962549578455819771911)
  ·
    refine ⟨48889443824367683729657867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32592962549578455819771911 48889443824367683729657867)
    ·
      refine ⟨73334165736551525594486801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48889443824367683729657867 73334165736551525594486801)
      ·
        refine ⟨55000624302413644195865101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73334165736551525594486801 55000624302413644195865101)
        ·
          refine ⟨20625234113405116573449413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55000624302413644195865101 20625234113405116573449413)
          ·
            refine ⟨3867231396263459357521765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20625234113405116573449413 3867231396263459357521765)
            ·
              refine ⟨725105886799398629535331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3867231396263459357521765 725105886799398629535331)
              ·
                refine ⟨1087658830199097944302997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 725105886799398629535331 1087658830199097944302997)
                ·
                  refine ⟨50984007665582716139203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1087658830199097944302997 50984007665582716139203)
                  ·
                    rfl

theorem cell23_893619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 6].length) (baseStart_893619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893619 prefixEnd_893619 := by exact prefixLift 893619
  have htrace : WordTrace (prefixWord ++ tailWord_893619) baseStart_893619 baseEnd_893619 := by
    simpa [prefixWord, tailWord_893619, baseEnd_893619] using wordTrace_append hprefix tailTrace_893619
  have hstable : (prefixWord ++ tailWord_893619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893619).length < 2 ^ (prefixWord ++ tailWord_893619).sum := by decide
  have hdescent : baseEnd_893619 < baseStart_893619 := by decide
  rcases family_descends (prefixWord ++ tailWord_893619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893656 : List Nat := [2, 1, 2, 2, 3, 2, 2, 2, 2, 3, 2]
def baseStart_893656 : Nat := 118140960795 + 893656 * 2 ^ 59
def prefixEnd_893656 : Nat := 4983230072969 + 3 ^ 40 * 893656 * 2
def baseEnd_893656 : Nat := 458875067774460800490157

theorem tailTrace_893656 : CollatzResearch.WordTrace tailWord_893656 prefixEnd_893656 458875067774460800490157 := by
  unfold tailWord_893656
  simp only [CollatzResearch.WordTrace]
  refine ⟨16297156025222205569434411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21729541366962940759245881 16297156025222205569434411)
  ·
    refine ⟨24445734037833308354151617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16297156025222205569434411 24445734037833308354151617)
    ·
      refine ⟨18334300528374981265613713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24445734037833308354151617 18334300528374981265613713)
      ·
        refine ⟨13750725396281235949210285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18334300528374981265613713 13750725396281235949210285)
        ·
          refine ⟨5156522023605463480953857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13750725396281235949210285 5156522023605463480953857)
          ·
            refine ⟨3867391517704097610715393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5156522023605463480953857 3867391517704097610715393)
            ·
              refine ⟨2900543638278073208036545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3867391517704097610715393 2900543638278073208036545)
              ·
                refine ⟨2175407728708554906027409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2900543638278073208036545 2175407728708554906027409)
                ·
                  refine ⟨1631555796531416179520557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2175407728708554906027409 1631555796531416179520557)
                  ·
                    refine ⟨611833423699281067320209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1631555796531416179520557 611833423699281067320209)
                    ·
                      refine ⟨458875067774460800490157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 611833423699281067320209 458875067774460800490157)
                      ·
                        rfl

theorem cell23_893656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 2, 3, 2].length) (baseStart_893656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893656 prefixEnd_893656 := by exact prefixLift 893656
  have htrace : WordTrace (prefixWord ++ tailWord_893656) baseStart_893656 baseEnd_893656 := by
    simpa [prefixWord, tailWord_893656, baseEnd_893656] using wordTrace_append hprefix tailTrace_893656
  have hstable : (prefixWord ++ tailWord_893656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893656).length < 2 ^ (prefixWord ++ tailWord_893656).sum := by decide
  have hdescent : baseEnd_893656 < baseStart_893656 := by decide
  rcases family_descends (prefixWord ++ tailWord_893656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893663 : List Nat := [1, 1, 2, 3, 2, 4, 1, 4, 1, 1, 3]
def baseStart_893663 : Nat := 118140960795 + 893663 * 2 ^ 59
def prefixEnd_893663 : Nat := 4983230072969 + 3 ^ 40 * 893663 * 2
def baseEnd_893663 : Nat := 458878662139042273102625

theorem tailTrace_893663 : CollatzResearch.WordTrace tailWord_893663 prefixEnd_893663 458878662139042273102625 := by
  unfold tailWord_893663
  simp only [CollatzResearch.WordTrace]
  refine ⟨32594567361419051334373643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21729711574279367556249095 32594567361419051334373643)
  ·
    refine ⟨48891851042128577001560465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32594567361419051334373643 48891851042128577001560465)
    ·
      refine ⟨36668888281596432751170349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48891851042128577001560465 36668888281596432751170349)
      ·
        refine ⟨13750833105598662281688881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36668888281596432751170349 13750833105598662281688881)
        ·
          refine ⟨10313124829198996711266661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13750833105598662281688881 10313124829198996711266661)
          ·
            refine ⟨1933710905474811883362499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10313124829198996711266661 1933710905474811883362499)
            ·
              refine ⟨2900566358212217825043749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1933710905474811883362499 2900566358212217825043749)
              ·
                refine ⟨543856192164790842195703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2900566358212217825043749 543856192164790842195703)
                ·
                  refine ⟨815784288247186263293555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 543856192164790842195703 815784288247186263293555)
                  ·
                    refine ⟨1223676432370779394940333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 815784288247186263293555 1223676432370779394940333)
                    ·
                      refine ⟨458878662139042273102625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1223676432370779394940333 458878662139042273102625)
                      ·
                        rfl

theorem cell23_893663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 4, 1, 1, 3].length) (baseStart_893663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893663 prefixEnd_893663 := by exact prefixLift 893663
  have htrace : WordTrace (prefixWord ++ tailWord_893663) baseStart_893663 baseEnd_893663 := by
    simpa [prefixWord, tailWord_893663, baseEnd_893663] using wordTrace_append hprefix tailTrace_893663
  have hstable : (prefixWord ++ tailWord_893663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893663).length < 2 ^ (prefixWord ++ tailWord_893663).sum := by decide
  have hdescent : baseEnd_893663 < baseStart_893663 := by decide
  rcases family_descends (prefixWord ++ tailWord_893663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893669 : List Nat := [1, 3, 1, 4, 1, 2, 1, 2, 3, 1, 4]
def baseStart_893669 : Nat := 118140960795 + 893669 * 2 ^ 59
def prefixEnd_893669 : Nat := 4983230072969 + 3 ^ 40 * 893669 * 2
def baseEnd_893669 : Nat := 458881743022969249627597

theorem tailTrace_893669 : CollatzResearch.WordTrace tailWord_893669 prefixEnd_893669 458881743022969249627597 := by
  unfold tailWord_893669
  simp only [CollatzResearch.WordTrace]
  refine ⟨32594786199397314359092061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21729857466264876239394707 32594786199397314359092061)
  ·
    refine ⟨12223044824773992884659523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32594786199397314359092061 12223044824773992884659523)
    ·
      refine ⟨18334567237160989326989285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12223044824773992884659523 18334567237160989326989285)
      ·
        refine ⟨3437731356967685498810491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18334567237160989326989285 3437731356967685498810491)
        ·
          refine ⟨5156597035451528248215737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3437731356967685498810491 5156597035451528248215737)
          ·
            refine ⟨3867447776588646186161803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5156597035451528248215737 3867447776588646186161803)
            ·
              refine ⟨5801171664882969279242705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3867447776588646186161803 5801171664882969279242705)
              ·
                refine ⟨4350878748662226959432029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5801171664882969279242705 4350878748662226959432029)
                ·
                  refine ⟨1631579530748335109787011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4350878748662226959432029 1631579530748335109787011)
                  ·
                    refine ⟨2447369296122502664680517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1631579530748335109787011 2447369296122502664680517)
                    ·
                      refine ⟨458881743022969249627597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2447369296122502664680517 458881743022969249627597)
                      ·
                        rfl

theorem cell23_893669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_893669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893669 prefixEnd_893669 := by exact prefixLift 893669
  have htrace : WordTrace (prefixWord ++ tailWord_893669) baseStart_893669 baseEnd_893669 := by
    simpa [prefixWord, tailWord_893669, baseEnd_893669] using wordTrace_append hprefix tailTrace_893669
  have hstable : (prefixWord ++ tailWord_893669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893669).length < 2 ^ (prefixWord ++ tailWord_893669).sum := by decide
  have hdescent : baseEnd_893669 < baseStart_893669 := by decide
  rcases family_descends (prefixWord ++ tailWord_893669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893679 : List Nat := [1, 1, 2, 1, 5, 3, 2, 1, 1, 6]
def baseStart_893679 : Nat := 118140960795 + 893679 * 2 ^ 59
def prefixEnd_893679 : Nat := 4983230072969 + 3 ^ 40 * 893679 * 2
def baseEnd_893679 : Nat := 152962292609838070167517

theorem tailTrace_893679 : CollatzResearch.WordTrace tailWord_893679 prefixEnd_893679 152962292609838070167517 := by
  unfold tailWord_893679
  simp only [CollatzResearch.WordTrace]
  refine ⟨32595150929361086066956091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21730100619574057377970727 32595150929361086066956091)
  ·
    refine ⟨48892726394041629100434137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32595150929361086066956091 48892726394041629100434137)
    ·
      refine ⟨36669544795531221825325603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48892726394041629100434137 36669544795531221825325603)
      ·
        refine ⟨55004317193296832737988405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36669544795531221825325603 55004317193296832737988405)
        ·
          refine ⟨5156654736871578069186413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55004317193296832737988405 5156654736871578069186413)
          ·
            refine ⟨1933745526326841775944905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5156654736871578069186413 1933745526326841775944905)
            ·
              refine ⟨1450309144745131331958679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1933745526326841775944905 1450309144745131331958679)
              ·
                refine ⟨2175463717117696997938019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1450309144745131331958679 2175463717117696997938019)
                ·
                  refine ⟨3263195575676545496907029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2175463717117696997938019 3263195575676545496907029)
                  ·
                    refine ⟨152962292609838070167517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3263195575676545496907029 152962292609838070167517)
                    ·
                      rfl

theorem cell23_893679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 6].length) (baseStart_893679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893679 prefixEnd_893679 := by exact prefixLift 893679
  have htrace : WordTrace (prefixWord ++ tailWord_893679) baseStart_893679 baseEnd_893679 := by
    simpa [prefixWord, tailWord_893679, baseEnd_893679] using wordTrace_append hprefix tailTrace_893679
  have hstable : (prefixWord ++ tailWord_893679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893679).length < 2 ^ (prefixWord ++ tailWord_893679).sum := by decide
  have hdescent : baseEnd_893679 < baseStart_893679 := by decide
  rcases family_descends (prefixWord ++ tailWord_893679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893686 : List Nat := [5, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4]
def baseStart_893686 : Nat := 118140960795 + 893686 * 2 ^ 59
def prefixEnd_893686 : Nat := 4983230072969 + 3 ^ 40 * 893686 * 2
def baseEnd_893686 : Nat := 458890472194095683115019

theorem tailTrace_893686 : CollatzResearch.WordTrace tailWord_893686 prefixEnd_893686 458890472194095683115019 := by
  unfold tailWord_893686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2037212890020982891403807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21730270826890484174973941 2037212890020982891403807)
  ·
    refine ⟨3055819335031474337105711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2037212890020982891403807 3055819335031474337105711)
    ·
      refine ⟨4583729002547211505658567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3055819335031474337105711 4583729002547211505658567)
      ·
        refine ⟨6875593503820817258487851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4583729002547211505658567 6875593503820817258487851)
        ·
          refine ⟨10313390255731225887731777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6875593503820817258487851 10313390255731225887731777)
          ·
            refine ⟨7735042691798419415798833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10313390255731225887731777 7735042691798419415798833)
            ·
              refine ⟨5801282018848814561849125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7735042691798419415798833 5801282018848814561849125)
              ·
                refine ⟨1087740378534152730346711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5801282018848814561849125 1087740378534152730346711)
                ·
                  refine ⟨1631610567801229095520067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1087740378534152730346711 1631610567801229095520067)
                  ·
                    refine ⟨2447415851701843643280101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1631610567801229095520067 2447415851701843643280101)
                    ·
                      refine ⟨458890472194095683115019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2447415851701843643280101 458890472194095683115019)
                      ·
                        rfl

theorem cell23_893686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_893686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893686 prefixEnd_893686 := by exact prefixLift 893686
  have htrace : WordTrace (prefixWord ++ tailWord_893686) baseStart_893686 baseEnd_893686 := by
    simpa [prefixWord, tailWord_893686, baseEnd_893686] using wordTrace_append hprefix tailTrace_893686
  have hstable : (prefixWord ++ tailWord_893686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893686).length < 2 ^ (prefixWord ++ tailWord_893686).sum := by decide
  have hdescent : baseEnd_893686 < baseStart_893686 := by decide
  rcases family_descends (prefixWord ++ tailWord_893686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893703 : List Nat := [1, 1, 4, 4, 1, 1, 4, 1, 1, 1, 4]
def baseStart_893703 : Nat := 118140960795 + 893703 * 2 ^ 59
def prefixEnd_893703 : Nat := 4983230072969 + 3 ^ 40 * 893703 * 2
def baseEnd_893703 : Nat := 458899201365222116602441

theorem tailTrace_893703 : CollatzResearch.WordTrace tailWord_893703 prefixEnd_893703 458899201365222116602441 := by
  unfold tailWord_893703
  simp only [CollatzResearch.WordTrace]
  refine ⟨32596026281274138165829763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21730684187516092110553175 32596026281274138165829763)
  ·
    refine ⟨48894039421911207248744645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32596026281274138165829763 48894039421911207248744645)
    ·
      refine ⟨9167632391608351359139621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48894039421911207248744645 9167632391608351359139621)
      ·
        refine ⟨1718931073426565879838679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9167632391608351359139621 1718931073426565879838679)
        ·
          refine ⟨2578396610139848819758019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1718931073426565879838679 2578396610139848819758019)
          ·
            refine ⟨3867594915209773229637029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2578396610139848819758019 3867594915209773229637029)
            ·
              refine ⟨725174046601832480556943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3867594915209773229637029 725174046601832480556943)
              ·
                refine ⟨1087761069902748720835415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 725174046601832480556943 1087761069902748720835415)
                ·
                  refine ⟨1631641604854123081253123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1087761069902748720835415 1631641604854123081253123)
                  ·
                    refine ⟨2447462407281184621879685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1631641604854123081253123 2447462407281184621879685)
                    ·
                      refine ⟨458899201365222116602441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2447462407281184621879685 458899201365222116602441)
                      ·
                        rfl

theorem cell23_893703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_893703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893703 prefixEnd_893703 := by exact prefixLift 893703
  have htrace : WordTrace (prefixWord ++ tailWord_893703) baseStart_893703 baseEnd_893703 := by
    simpa [prefixWord, tailWord_893703, baseEnd_893703] using wordTrace_append hprefix tailTrace_893703
  have hstable : (prefixWord ++ tailWord_893703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893703).length < 2 ^ (prefixWord ++ tailWord_893703).sum := by decide
  have hdescent : baseEnd_893703 < baseStart_893703 := by decide
  rcases family_descends (prefixWord ++ tailWord_893703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893706 : List Nat := [3, 1, 2, 2, 1, 2, 3, 3, 1, 2, 3]
def baseStart_893706 : Nat := 118140960795 + 893706 * 2 ^ 59
def prefixEnd_893706 : Nat := 4983230072969 + 3 ^ 40 * 893706 * 2
def baseEnd_893706 : Nat := 458900741807185604864927

theorem tailTrace_893706 : CollatzResearch.WordTrace tailWord_893706 prefixEnd_893706 458900741807185604864927 := by
  unfold tailWord_893706
  simp only [CollatzResearch.WordTrace]
  refine ⟨8149033925065817419547243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21730757133508846452125981 8149033925065817419547243)
  ·
    refine ⟨12223550887598726129320865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8149033925065817419547243 12223550887598726129320865)
    ·
      refine ⟨9167663165699044596990649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12223550887598726129320865 9167663165699044596990649)
      ·
        refine ⟨6875747374274283447742987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9167663165699044596990649 6875747374274283447742987)
        ·
          refine ⟨10313621061411425171614481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6875747374274283447742987 10313621061411425171614481)
          ·
            refine ⟨7735215796058568878710861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10313621061411425171614481 7735215796058568878710861)
            ·
              refine ⟨2900705923521963329516573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7735215796058568878710861 2900705923521963329516573)
              ·
                refine ⟨1087764721320736248568715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2900705923521963329516573 1087764721320736248568715)
                ·
                  refine ⟨1631647081981104372853073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1087764721320736248568715 1631647081981104372853073)
                  ·
                    refine ⟨1223735311485828279639805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1631647081981104372853073 1223735311485828279639805)
                    ·
                      refine ⟨458900741807185604864927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1223735311485828279639805 458900741807185604864927)
                      ·
                        rfl

theorem cell23_893706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_893706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893706 prefixEnd_893706 := by exact prefixLift 893706
  have htrace : WordTrace (prefixWord ++ tailWord_893706) baseStart_893706 baseEnd_893706 := by
    simpa [prefixWord, tailWord_893706, baseEnd_893706] using wordTrace_append hprefix tailTrace_893706
  have hstable : (prefixWord ++ tailWord_893706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893706).length < 2 ^ (prefixWord ++ tailWord_893706).sum := by decide
  have hdescent : baseEnd_893706 < baseStart_893706 := by decide
  rcases family_descends (prefixWord ++ tailWord_893706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893749 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 2, 2, 5]
def baseStart_893749 : Nat := 118140960795 + 893749 * 2 ^ 59
def prefixEnd_893749 : Nat := 4983230072969 + 3 ^ 40 * 893749 * 2
def baseEnd_893749 : Nat := 458922821475328936627229

theorem tailTrace_893749 : CollatzResearch.WordTrace tailWord_893749 prefixEnd_893749 458922821475328936627229 := by
  unfold tailWord_893749
  simp only [CollatzResearch.WordTrace]
  refine ⟨32597704039107488022004301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21731802692738325348002867 32597704039107488022004301)
  ·
    refine ⟨12224139014665308008251613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32597704039107488022004301 12224139014665308008251613)
    ·
      refine ⟨4584052130499490503094355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12224139014665308008251613 4584052130499490503094355)
      ·
        refine ⟨6876078195749235754641533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4584052130499490503094355 6876078195749235754641533)
        ·
          refine ⟨2578529323405963407990575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6876078195749235754641533 2578529323405963407990575)
          ·
            refine ⟨3867793985108945111985863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2578529323405963407990575 3867793985108945111985863)
            ·
              refine ⟨5801690977663417667978795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3867793985108945111985863 5801690977663417667978795)
              ·
                refine ⟨8702536466495126501968193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5801690977663417667978795 8702536466495126501968193)
                ·
                  refine ⟨6526902349871344876476145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8702536466495126501968193 6526902349871344876476145)
                  ·
                    refine ⟨4895176762403508657357109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6526902349871344876476145 4895176762403508657357109)
                    ·
                      refine ⟨458922821475328936627229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4895176762403508657357109 458922821475328936627229)
                      ·
                        rfl

theorem cell23_893749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_893749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893749 prefixEnd_893749 := by exact prefixLift 893749
  have htrace : WordTrace (prefixWord ++ tailWord_893749) baseStart_893749 baseEnd_893749 := by
    simpa [prefixWord, tailWord_893749, baseEnd_893749] using wordTrace_append hprefix tailTrace_893749
  have hstable : (prefixWord ++ tailWord_893749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893749).length < 2 ^ (prefixWord ++ tailWord_893749).sum := by decide
  have hdescent : baseEnd_893749 < baseStart_893749 := by decide
  rcases family_descends (prefixWord ++ tailWord_893749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893754 : List Nat := [3, 1, 1, 1, 7, 1, 1, 3, 1, 2, 2]
def baseStart_893754 : Nat := 118140960795 + 893754 * 2 ^ 59
def prefixEnd_893754 : Nat := 4983230072969 + 3 ^ 40 * 893754 * 2
def baseEnd_893754 : Nat := 458925388878601417064707

theorem tailTrace_893754 : CollatzResearch.WordTrace tailWord_893754 prefixEnd_893754 458925388878601417064707 := by
  unfold tailWord_893754
  simp only [CollatzResearch.WordTrace]
  refine ⟨8149471601022343468984079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21731924269392915917290877 8149471601022343468984079)
  ·
    refine ⟨12224207401533515203476119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8149471601022343468984079 12224207401533515203476119)
    ·
      refine ⟨18336311102300272805214179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12224207401533515203476119 18336311102300272805214179)
      ·
        refine ⟨27504466653450409207821269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18336311102300272805214179 27504466653450409207821269)
        ·
          refine ⟨644635937190243965808311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 27504466653450409207821269 644635937190243965808311)
          ·
            refine ⟨966953905785365948712467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644635937190243965808311 966953905785365948712467)
            ·
              refine ⟨1450430858678048923068701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 966953905785365948712467 1450430858678048923068701)
              ·
                refine ⟨543911572004268346150763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1450430858678048923068701 543911572004268346150763)
                ·
                  refine ⟨815867358006402519226145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 543911572004268346150763 815867358006402519226145)
                  ·
                    refine ⟨611900518504801889419609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 815867358006402519226145 611900518504801889419609)
                    ·
                      refine ⟨458925388878601417064707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 611900518504801889419609 458925388878601417064707)
                      ·
                        rfl

theorem cell23_893754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 3, 1, 2, 2].length) (baseStart_893754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893754 prefixEnd_893754 := by exact prefixLift 893754
  have htrace : WordTrace (prefixWord ++ tailWord_893754) baseStart_893754 baseEnd_893754 := by
    simpa [prefixWord, tailWord_893754, baseEnd_893754] using wordTrace_append hprefix tailTrace_893754
  have hstable : (prefixWord ++ tailWord_893754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893754).length < 2 ^ (prefixWord ++ tailWord_893754).sum := by decide
  have hdescent : baseEnd_893754 < baseStart_893754 := by decide
  rcases family_descends (prefixWord ++ tailWord_893754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893833 : List Nat := [1, 2, 1, 1, 5, 2, 4, 2, 5]
def baseStart_893833 : Nat := 118140960795 + 893833 * 2 ^ 59
def prefixEnd_893833 : Nat := 4983230072969 + 3 ^ 40 * 893833 * 2
def baseEnd_893833 : Nat := 50996217094478511997427

theorem tailTrace_893833 : CollatzResearch.WordTrace tailWord_893833 prefixEnd_893833 50996217094478511997427 := by
  unfold tailWord_893833
  simp only [CollatzResearch.WordTrace]
  refine ⟨32600767770803170368062153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21733845180535446912041435 32600767770803170368062153)
  ·
    refine ⟨24450575828102377776046615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32600767770803170368062153 24450575828102377776046615)
    ·
      refine ⟨36675863742153566664069923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24450575828102377776046615 36675863742153566664069923)
      ·
        refine ⟨55013795613230349996104885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36675863742153566664069923 55013795613230349996104885)
        ·
          refine ⟨5157543338740345312134833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55013795613230349996104885 5157543338740345312134833)
          ·
            refine ⟨3868157504055258984101125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5157543338740345312134833 3868157504055258984101125)
            ·
              refine ⟨725279532010361059518961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3868157504055258984101125 725279532010361059518961)
              ·
                refine ⟨543959649007770794639221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 725279532010361059518961 543959649007770794639221)
                ·
                  refine ⟨50996217094478511997427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 543959649007770794639221 50996217094478511997427)
                  ·
                    rfl

theorem cell23_893833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 2, 5].length) (baseStart_893833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893833 prefixEnd_893833 := by exact prefixLift 893833
  have htrace : WordTrace (prefixWord ++ tailWord_893833) baseStart_893833 baseEnd_893833 := by
    simpa [prefixWord, tailWord_893833, baseEnd_893833] using wordTrace_append hprefix tailTrace_893833
  have hstable : (prefixWord ++ tailWord_893833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893833).length < 2 ^ (prefixWord ++ tailWord_893833).sum := by decide
  have hdescent : baseEnd_893833 < baseStart_893833 := by decide
  rcases family_descends (prefixWord ++ tailWord_893833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893836 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 2, 5, 2]
def baseStart_893836 : Nat := 118140960795 + 893836 * 2 ^ 59
def prefixEnd_893836 : Nat := 4983230072969 + 3 ^ 40 * 893836 * 2
def baseEnd_893836 : Nat := 458967494292270096239329

theorem tailTrace_893836 : CollatzResearch.WordTrace tailWord_893836 prefixEnd_893836 458967494292270096239329 := by
  unfold tailWord_893836
  simp only [CollatzResearch.WordTrace]
  refine ⟨16300438594896150940210681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21733918126528201253614241 16300438594896150940210681)
  ·
    refine ⟨12225328946172113205158011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16300438594896150940210681 12225328946172113205158011)
    ·
      refine ⟨18337993419258169807737017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12225328946172113205158011 18337993419258169807737017)
      ·
        refine ⟨13753495064443627355802763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18337993419258169807737017 13753495064443627355802763)
        ·
          refine ⟨20630242596665441033704145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13753495064443627355802763 20630242596665441033704145)
          ·
            refine ⟨15472681947499080775278109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20630242596665441033704145 15472681947499080775278109)
            ·
              refine ⟨5802255730312155290729291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15472681947499080775278109 5802255730312155290729291)
              ·
                refine ⟨8703383595468232936093937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5802255730312155290729291 8703383595468232936093937)
                ·
                  refine ⟨6527537696601174702070453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8703383595468232936093937 6527537696601174702070453)
                  ·
                    refine ⟨611956659056360128319105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6527537696601174702070453 611956659056360128319105)
                    ·
                      refine ⟨458967494292270096239329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 611956659056360128319105 458967494292270096239329)
                      ·
                        rfl

theorem cell23_893836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 2, 5, 2].length) (baseStart_893836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893836 prefixEnd_893836 := by exact prefixLift 893836
  have htrace : WordTrace (prefixWord ++ tailWord_893836) baseStart_893836 baseEnd_893836 := by
    simpa [prefixWord, tailWord_893836, baseEnd_893836] using wordTrace_append hprefix tailTrace_893836
  have hstable : (prefixWord ++ tailWord_893836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893836).length < 2 ^ (prefixWord ++ tailWord_893836).sum := by decide
  have hdescent : baseEnd_893836 < baseStart_893836 := by decide
  rcases family_descends (prefixWord ++ tailWord_893836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893849 : List Nat := [1, 2, 1, 2, 1, 3, 1, 4, 1, 3, 4]
def baseStart_893849 : Nat := 118140960795 + 893849 * 2 ^ 59
def prefixEnd_893849 : Nat := 4983230072969 + 3 ^ 40 * 893849 * 2
def baseEnd_893849 : Nat := 458974169540778545376769

theorem tailTrace_893849 : CollatzResearch.WordTrace tailWord_893849 prefixEnd_893849 458974169540778545376769 := by
  unfold tailWord_893849
  simp only [CollatzResearch.WordTrace]
  refine ⟨32601351338745205100644601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21734234225830136733763067 32601351338745205100644601)
  ·
    refine ⟨24451013504058903825483451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32601351338745205100644601 24451013504058903825483451)
    ·
      refine ⟨36676520256088355738225177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24451013504058903825483451 36676520256088355738225177)
      ·
        refine ⟨27507390192066266803668883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36676520256088355738225177 27507390192066266803668883)
        ·
          refine ⟨41261085288099400205503325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27507390192066266803668883 41261085288099400205503325)
          ·
            refine ⟨15472906983037275077063747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41261085288099400205503325 15472906983037275077063747)
            ·
              refine ⟨23209360474555912615595621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15472906983037275077063747 23209360474555912615595621)
              ·
                refine ⟨4351755088979233615424179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23209360474555912615595621 4351755088979233615424179)
                ·
                  refine ⟨6527632633468850423136269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4351755088979233615424179 6527632633468850423136269)
                  ·
                    refine ⟨2447862237550818908676101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6527632633468850423136269 2447862237550818908676101)
                    ·
                      refine ⟨458974169540778545376769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2447862237550818908676101 458974169540778545376769)
                      ·
                        rfl

theorem cell23_893849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_893849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893849 prefixEnd_893849 := by exact prefixLift 893849
  have htrace : WordTrace (prefixWord ++ tailWord_893849) baseStart_893849 baseEnd_893849 := by
    simpa [prefixWord, tailWord_893849, baseEnd_893849] using wordTrace_append hprefix tailTrace_893849
  have hstable : (prefixWord ++ tailWord_893849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893849).length < 2 ^ (prefixWord ++ tailWord_893849).sum := by decide
  have hdescent : baseEnd_893849 < baseStart_893849 := by decide
  rcases family_descends (prefixWord ++ tailWord_893849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893878 : List Nat := [5, 1, 4, 1, 1, 2, 1, 2, 2, 2, 2]
def baseStart_893878 : Nat := 118140960795 + 893878 * 2 ^ 59
def prefixEnd_893878 : Nat := 4983230072969 + 3 ^ 40 * 893878 * 2
def baseEnd_893878 : Nat := 458989060479758931914137

theorem tailTrace_893878 : CollatzResearch.WordTrace tailWord_893878 prefixEnd_893878 458989060479758931914137 := by
  unfold tailWord_893878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2037650565977508940840643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21734939370426762035633525 2037650565977508940840643)
  ·
    refine ⟨3056475848966263411260965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2037650565977508940840643 3056475848966263411260965)
    ·
      refine ⟨573089221681174389611431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3056475848966263411260965 573089221681174389611431)
      ·
        refine ⟨859633832521761584417147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573089221681174389611431 859633832521761584417147)
        ·
          refine ⟨1289450748782642376625721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859633832521761584417147 1289450748782642376625721)
          ·
            refine ⟨967088061586981782469291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1289450748782642376625721 967088061586981782469291)
            ·
              refine ⟨1450632092380472673703937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 967088061586981782469291 1450632092380472673703937)
              ·
                refine ⟨1087974069285354505277953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1450632092380472673703937 1087974069285354505277953)
                ·
                  refine ⟨815980551964015878958465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1087974069285354505277953 815980551964015878958465)
                  ·
                    refine ⟨611985413973011909218849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 815980551964015878958465 611985413973011909218849)
                    ·
                      refine ⟨458989060479758931914137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 611985413973011909218849 458989060479758931914137)
                      ·
                        rfl

theorem cell23_893878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_893878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893878 prefixEnd_893878 := by exact prefixLift 893878
  have htrace : WordTrace (prefixWord ++ tailWord_893878) baseStart_893878 baseEnd_893878 := by
    simpa [prefixWord, tailWord_893878, baseEnd_893878] using wordTrace_append hprefix tailTrace_893878
  have hstable : (prefixWord ++ tailWord_893878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893878).length < 2 ^ (prefixWord ++ tailWord_893878).sum := by decide
  have hdescent : baseEnd_893878 < baseStart_893878 := by decide
  rcases family_descends (prefixWord ++ tailWord_893878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893879 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 6]
def baseStart_893879 : Nat := 118140960795 + 893879 * 2 ^ 59
def prefixEnd_893879 : Nat := 4983230072969 + 3 ^ 40 * 893879 * 2
def baseEnd_893879 : Nat := 458989573960413428001631

theorem tailTrace_893879 : CollatzResearch.WordTrace tailWord_893879 prefixEnd_893879 458989573960413428001631 := by
  unfold tailWord_893879
  simp only [CollatzResearch.WordTrace]
  refine ⟨32602445528636520224236691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21734963685757680149491127 32602445528636520224236691)
  ·
    refine ⟨48903668292954780336355037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32602445528636520224236691 48903668292954780336355037)
    ·
      refine ⟨18338875609858042626133139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48903668292954780336355037 18338875609858042626133139)
      ·
        refine ⟨27508313414787063939199709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18338875609858042626133139 27508313414787063939199709)
        ·
          refine ⟨10315617530545148977199891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27508313414787063939199709 10315617530545148977199891)
          ·
            refine ⟨15473426295817723465799837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10315617530545148977199891 15473426295817723465799837)
            ·
              refine ⟨5802534860931646299674939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15473426295817723465799837 5802534860931646299674939)
              ·
                refine ⟨8703802291397469449512409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5802534860931646299674939 8703802291397469449512409)
                ·
                  refine ⟨6527851718548102087134307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8703802291397469449512409 6527851718548102087134307)
                  ·
                    refine ⟨9791777577822153130701461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6527851718548102087134307 9791777577822153130701461)
                    ·
                      refine ⟨458989573960413428001631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9791777577822153130701461 458989573960413428001631)
                      ·
                        rfl

theorem cell23_893879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_893879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893879 prefixEnd_893879 := by exact prefixLift 893879
  have htrace : WordTrace (prefixWord ++ tailWord_893879) baseStart_893879 baseEnd_893879 := by
    simpa [prefixWord, tailWord_893879, baseEnd_893879] using wordTrace_append hprefix tailTrace_893879
  have hstable : (prefixWord ++ tailWord_893879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893879).length < 2 ^ (prefixWord ++ tailWord_893879).sum := by decide
  have hdescent : baseEnd_893879 < baseStart_893879 := by decide
  rcases family_descends (prefixWord ++ tailWord_893879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893910 : List Nat := [5, 2, 1, 1, 2, 1, 2, 2, 3, 4]
def baseStart_893910 : Nat := 118140960795 + 893910 * 2 ^ 59
def prefixEnd_893910 : Nat := 4983230072969 + 3 ^ 40 * 893910 * 2
def baseEnd_893910 : Nat := 153001830620234268904663

theorem tailTrace_893910 : CollatzResearch.WordTrace tailWord_893910 prefixEnd_893910 153001830620234268904663 := by
  unfold tailWord_893910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2037723511970263282413449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21735717461016141679076789 2037723511970263282413449)
  ·
    refine ⟨1528292633977697461810087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2037723511970263282413449 1528292633977697461810087)
    ·
      refine ⟨2292438950966546192715131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1528292633977697461810087 2292438950966546192715131)
      ·
        refine ⟨3438658426449819289072697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2292438950966546192715131 3438658426449819289072697)
        ·
          refine ⟨2578993819837364466804523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3438658426449819289072697 2578993819837364466804523)
          ·
            refine ⟨3868490729756046700206785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2578993819837364466804523 3868490729756046700206785)
            ·
              refine ⟨2901368047317035025155089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3868490729756046700206785 2901368047317035025155089)
              ·
                refine ⟨2176026035487776268866317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2901368047317035025155089 2176026035487776268866317)
                ·
                  refine ⟨816009763307916100824869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2176026035487776268866317 816009763307916100824869)
                  ·
                    refine ⟨153001830620234268904663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 816009763307916100824869 153001830620234268904663)
                    ·
                      rfl

theorem cell23_893910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_893910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893910 prefixEnd_893910 := by exact prefixLift 893910
  have htrace : WordTrace (prefixWord ++ tailWord_893910) baseStart_893910 baseEnd_893910 := by
    simpa [prefixWord, tailWord_893910, baseEnd_893910] using wordTrace_append hprefix tailTrace_893910
  have hstable : (prefixWord ++ tailWord_893910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893910).length < 2 ^ (prefixWord ++ tailWord_893910).sum := by decide
  have hdescent : baseEnd_893910 < baseStart_893910 := by decide
  rcases family_descends (prefixWord ++ tailWord_893910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893927 : List Nat := [1, 1, 5, 2, 2, 3, 1, 3, 1, 4]
def baseStart_893927 : Nat := 118140960795 + 893927 * 2 ^ 59
def prefixEnd_893927 : Nat := 4983230072969 + 3 ^ 40 * 893927 * 2
def baseEnd_893927 : Nat := 153004740343943080067137

theorem tailTrace_893927 : CollatzResearch.WordTrace tailWord_893927 prefixEnd_893927 153004740343943080067137 := by
  unfold tailWord_893927
  simp only [CollatzResearch.WordTrace]
  refine ⟨32604196232462624421984035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21736130821641749614656023 32604196232462624421984035)
  ·
    refine ⟨48906294348693936632976053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32604196232462624421984035 48906294348693936632976053)
    ·
      refine ⟨4584965095190056559341505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48906294348693936632976053 4584965095190056559341505)
      ·
        refine ⟨3438723821392542419506129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4584965095190056559341505 3438723821392542419506129)
        ·
          refine ⟨2579042866044406814629597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3438723821392542419506129 2579042866044406814629597)
          ·
            refine ⟨967141074766652555486099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2579042866044406814629597 967141074766652555486099)
            ·
              refine ⟨1450711612149978833229149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 967141074766652555486099 1450711612149978833229149)
              ·
                refine ⟨544016854556242062460931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1450711612149978833229149 544016854556242062460931)
                ·
                  refine ⟨816025281834363093691397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 544016854556242062460931 816025281834363093691397)
                  ·
                    refine ⟨153004740343943080067137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 816025281834363093691397 153004740343943080067137)
                    ·
                      rfl

theorem cell23_893927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_893927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893927 prefixEnd_893927 := by exact prefixLift 893927
  have htrace : WordTrace (prefixWord ++ tailWord_893927) baseStart_893927 baseEnd_893927 := by
    simpa [prefixWord, tailWord_893927, baseEnd_893927] using wordTrace_append hprefix tailTrace_893927
  have hstable : (prefixWord ++ tailWord_893927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893927).length < 2 ^ (prefixWord ++ tailWord_893927).sum := by decide
  have hdescent : baseEnd_893927 < baseStart_893927 := by decide
  rcases family_descends (prefixWord ++ tailWord_893927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893973 : List Nat := [1, 3, 2, 1, 4, 2, 1, 1, 3, 1, 4]
def baseStart_893973 : Nat := 118140960795 + 893973 * 2 ^ 59
def prefixEnd_893973 : Nat := 4983230072969 + 3 ^ 40 * 893973 * 2
def baseEnd_893973 : Nat := 459037841141936060226199

theorem tailTrace_893973 : CollatzResearch.WordTrace tailWord_893973 prefixEnd_893973 459037841141936060226199 := by
  unfold tailWord_893973
  simp only [CollatzResearch.WordTrace]
  refine ⟨32605873990295974278158573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21737249326863982852105715 32605873990295974278158573)
  ·
    refine ⟨12227202746360990354309465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32605873990295974278158573 12227202746360990354309465)
    ·
      refine ⟨9170402059770742765732099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12227202746360990354309465 9170402059770742765732099)
      ·
        refine ⟨13755603089656114148598149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9170402059770742765732099 13755603089656114148598149)
        ·
          refine ⟨2579175579310521402862153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13755603089656114148598149 2579175579310521402862153)
          ·
            refine ⟨1934381684482891052146615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2579175579310521402862153 1934381684482891052146615)
            ·
              refine ⟨2901572526724336578219923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1934381684482891052146615 2901572526724336578219923)
              ·
                refine ⟨4352358790086504867329885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2901572526724336578219923 4352358790086504867329885)
                ·
                  refine ⟨1632134546282439325248707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4352358790086504867329885 1632134546282439325248707)
                  ·
                    refine ⟨2448201819423658987873061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1632134546282439325248707 2448201819423658987873061)
                    ·
                      refine ⟨459037841141936060226199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2448201819423658987873061 459037841141936060226199)
                      ·
                        rfl

theorem cell23_893973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_893973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_893973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_893973 prefixEnd_893973 := by exact prefixLift 893973
  have htrace : WordTrace (prefixWord ++ tailWord_893973) baseStart_893973 baseEnd_893973 := by
    simpa [prefixWord, tailWord_893973, baseEnd_893973] using wordTrace_append hprefix tailTrace_893973
  have hstable : (prefixWord ++ tailWord_893973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893973).length < 2 ^ (prefixWord ++ tailWord_893973).sum := by decide
  have hdescent : baseEnd_893973 < baseStart_893973 := by decide
  rcases family_descends (prefixWord ++ tailWord_893973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894013 : List Nat := [1, 4, 1, 3, 1, 4, 1, 8]
def baseStart_894013 : Nat := 118140960795 + 894013 * 2 ^ 59
def prefixEnd_894013 : Nat := 4983230072969 + 3 ^ 40 * 894013 * 2
def baseEnd_894013 : Nat := 17002162235856144582445

theorem tailTrace_894013 : CollatzResearch.WordTrace tailWord_894013 prefixEnd_894013 17002162235856144582445 := by
  unfold tailWord_894013
  simp only [CollatzResearch.WordTrace]
  refine ⟨32607332910151061109614693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21738221940100707406409795 32607332910151061109614693)
  ·
    refine ⟨6113874920653323958052755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32607332910151061109614693 6113874920653323958052755)
    ·
      refine ⟨9170812380979985937079133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6113874920653323958052755 9170812380979985937079133)
      ·
        refine ⟨3439054642867494726404675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9170812380979985937079133 3439054642867494726404675)
        ·
          refine ⟨5158581964301242089607013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3439054642867494726404675 5158581964301242089607013)
          ·
            refine ⟨967234118306482891801315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5158581964301242089607013 967234118306482891801315)
            ·
              refine ⟨1450851177459724337701973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 967234118306482891801315 1450851177459724337701973)
              ·
                refine ⟨17002162235856144582445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1450851177459724337701973 17002162235856144582445)
                ·
                  rfl

theorem cell23_894013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 8].length) (baseStart_894013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894013 prefixEnd_894013 := by exact prefixLift 894013
  have htrace : WordTrace (prefixWord ++ tailWord_894013) baseStart_894013 baseEnd_894013 := by
    simpa [prefixWord, tailWord_894013, baseEnd_894013] using wordTrace_append hprefix tailTrace_894013
  have hstable : (prefixWord ++ tailWord_894013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894013).length < 2 ^ (prefixWord ++ tailWord_894013).sum := by decide
  have hdescent : baseEnd_894013 < baseStart_894013 := by decide
  rcases family_descends (prefixWord ++ tailWord_894013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894023 : List Nat := [1, 1, 4, 1, 3, 2, 1, 3, 1, 3, 3]
def baseStart_894023 : Nat := 118140960795 + 894023 * 2 ^ 59
def prefixEnd_894023 : Nat := 4983230072969 + 3 ^ 40 * 894023 * 2
def baseEnd_894023 : Nat := 459063515174660864600969

theorem tailTrace_894023 : CollatzResearch.WordTrace tailWord_894023 prefixEnd_894023 459063515174660864600969 := by
  unfold tailWord_894023
  simp only [CollatzResearch.WordTrace]
  refine ⟨32607697640114832817478723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21738465093409888544985815 32607697640114832817478723)
  ·
    refine ⟨48911546460172249226218085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32607697640114832817478723 48911546460172249226218085)
    ·
      refine ⟨9170914961282296729915891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48911546460172249226218085 9170914961282296729915891)
      ·
        refine ⟨13756372441923445094873837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9170914961282296729915891 13756372441923445094873837)
        ·
          refine ⟨5158639665721291910577689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13756372441923445094873837 5158639665721291910577689)
          ·
            refine ⟨3868979749290968932933267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5158639665721291910577689 3868979749290968932933267)
            ·
              refine ⟨5803469623936453399399901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3868979749290968932933267 5803469623936453399399901)
              ·
                refine ⟨2176301108976170024774963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5803469623936453399399901 2176301108976170024774963)
                ·
                  refine ⟨3264451663464255037162445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2176301108976170024774963 3264451663464255037162445)
                  ·
                    refine ⟨1224169373799095638935917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3264451663464255037162445 1224169373799095638935917)
                    ·
                      refine ⟨459063515174660864600969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1224169373799095638935917 459063515174660864600969)
                      ·
                        rfl

theorem cell23_894023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_894023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894023 prefixEnd_894023 := by exact prefixLift 894023
  have htrace : WordTrace (prefixWord ++ tailWord_894023) baseStart_894023 baseEnd_894023 := by
    simpa [prefixWord, tailWord_894023, baseEnd_894023] using wordTrace_append hprefix tailTrace_894023
  have hstable : (prefixWord ++ tailWord_894023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894023).length < 2 ^ (prefixWord ++ tailWord_894023).sum := by decide
  have hdescent : baseEnd_894023 < baseStart_894023 := by decide
  rcases family_descends (prefixWord ++ tailWord_894023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894057 : List Nat := [1, 2, 1, 1, 1, 8, 1, 2, 2, 1, 3]
def baseStart_894057 : Nat := 118140960795 + 894057 * 2 ^ 59
def prefixEnd_894057 : Nat := 4983230072969 + 3 ^ 40 * 894057 * 2
def baseEnd_894057 : Nat := 459080973516913731575813

theorem tailTrace_894057 : CollatzResearch.WordTrace tailWord_894057 prefixEnd_894057 459080973516913731575813 := by
  unfold tailWord_894057
  simp only [CollatzResearch.WordTrace]
  refine ⟨32608937721991656624216425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21739291814661104416144283 32608937721991656624216425)
  ·
    refine ⟨24456703291493742468162319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32608937721991656624216425 24456703291493742468162319)
    ·
      refine ⟨36685054937240613702243479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24456703291493742468162319 36685054937240613702243479)
      ·
        refine ⟨55027582405860920553365219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36685054937240613702243479 55027582405860920553365219)
        ·
          refine ⟨82541373608791380830047829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55027582405860920553365219 82541373608791380830047829)
          ·
            refine ⟨967281721978023994102123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 82541373608791380830047829 967281721978023994102123)
            ·
              refine ⟨1450922582967035991153185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 967281721978023994102123 1450922582967035991153185)
              ·
                refine ⟨1088191937225276993364889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1450922582967035991153185 1088191937225276993364889)
                ·
                  refine ⟨816143952918957745023667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1088191937225276993364889 816143952918957745023667)
                  ·
                    refine ⟨1224215929378436617535501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 816143952918957745023667 1224215929378436617535501)
                    ·
                      refine ⟨459080973516913731575813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1224215929378436617535501 459080973516913731575813)
                      ·
                        rfl

theorem cell23_894057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 2, 1, 3].length) (baseStart_894057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894057 prefixEnd_894057 := by exact prefixLift 894057
  have htrace : WordTrace (prefixWord ++ tailWord_894057) baseStart_894057 baseEnd_894057 := by
    simpa [prefixWord, tailWord_894057, baseEnd_894057] using wordTrace_append hprefix tailTrace_894057
  have hstable : (prefixWord ++ tailWord_894057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894057).length < 2 ^ (prefixWord ++ tailWord_894057).sum := by decide
  have hdescent : baseEnd_894057 < baseStart_894057 := by decide
  rcases family_descends (prefixWord ++ tailWord_894057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894080 : List Nat := [2, 1, 1, 2, 1, 3, 5, 1, 1, 4, 2]
def baseStart_894080 : Nat := 118140960795 + 894080 * 2 ^ 59
def prefixEnd_894080 : Nat := 4983230072969 + 3 ^ 40 * 894080 * 2
def baseEnd_894080 : Nat := 459092783571967141588207

theorem tailTrace_894080 : CollatzResearch.WordTrace tailWord_894080 prefixEnd_894080 459092783571967141588207 := by
  unfold tailWord_894080
  simp only [CollatzResearch.WordTrace]
  refine ⟨16304888300454165776151847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21739851067272221034869129 16304888300454165776151847)
  ·
    refine ⟨24457332450681248664227771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16304888300454165776151847 24457332450681248664227771)
    ·
      refine ⟨36685998676021872996341657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24457332450681248664227771 36685998676021872996341657)
      ·
        refine ⟨27514499007016404747256243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36685998676021872996341657 27514499007016404747256243)
        ·
          refine ⟨41271748510524607120884365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27514499007016404747256243 41271748510524607120884365)
          ·
            refine ⟨15476905691446727670331637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41271748510524607120884365 15476905691446727670331637)
            ·
              refine ⟨1450959908573130719093591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15476905691446727670331637 1450959908573130719093591)
              ·
                refine ⟨2176439862859696078640387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1450959908573130719093591 2176439862859696078640387)
                ·
                  refine ⟨3264659794289544117960581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2176439862859696078640387 3264659794289544117960581)
                  ·
                    refine ⟨612123711429289522117609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3264659794289544117960581 612123711429289522117609)
                    ·
                      refine ⟨459092783571967141588207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 612123711429289522117609 459092783571967141588207)
                      ·
                        rfl

theorem cell23_894080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 1, 4, 2].length) (baseStart_894080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894080 prefixEnd_894080 := by exact prefixLift 894080
  have htrace : WordTrace (prefixWord ++ tailWord_894080) baseStart_894080 baseEnd_894080 := by
    simpa [prefixWord, tailWord_894080, baseEnd_894080] using wordTrace_append hprefix tailTrace_894080
  have hstable : (prefixWord ++ tailWord_894080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894080).length < 2 ^ (prefixWord ++ tailWord_894080).sum := by decide
  have hdescent : baseEnd_894080 < baseStart_894080 := by decide
  rcases family_descends (prefixWord ++ tailWord_894080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894163 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 5, 4]
def baseStart_894163 : Nat := 118140960795 + 894163 * 2 ^ 59
def prefixEnd_894163 : Nat := 4983230072969 + 3 ^ 40 * 894163 * 2
def baseEnd_894163 : Nat := 153045134155430105616775

theorem tailTrace_894163 : CollatzResearch.WordTrace tailWord_894163 prefixEnd_894163 153045134155430105616775 := by
  unfold tailWord_894163
  simp only [CollatzResearch.WordTrace]
  refine ⟨32612803859607636727575143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21741869239738424485050095 32612803859607636727575143)
  ·
    refine ⟨48919205789411455091362715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32612803859607636727575143 48919205789411455091362715)
    ·
      refine ⟨73378808684117182637044073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48919205789411455091362715 73378808684117182637044073)
      ·
        refine ⟨55034106513087886977783055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73378808684117182637044073 55034106513087886977783055)
        ·
          refine ⟨82551159769631830466674583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55034106513087886977783055 82551159769631830466674583)
          ·
            refine ⟨123826739654447745700011875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82551159769631830466674583 123826739654447745700011875)
            ·
              refine ⟨185740109481671618550017813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123826739654447745700011875 185740109481671618550017813)
              ·
                refine ⟨8706567631953357119532085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 185740109481671618550017813 8706567631953357119532085)
                ·
                  refine ⟨816240715495627229956133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8706567631953357119532085 816240715495627229956133)
                  ·
                    refine ⟨153045134155430105616775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 816240715495627229956133 153045134155430105616775)
                    ·
                      rfl

theorem cell23_894163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 5, 4].length) (baseStart_894163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894163 prefixEnd_894163 := by exact prefixLift 894163
  have htrace : WordTrace (prefixWord ++ tailWord_894163) baseStart_894163 baseEnd_894163 := by
    simpa [prefixWord, tailWord_894163, baseEnd_894163] using wordTrace_append hprefix tailTrace_894163
  have hstable : (prefixWord ++ tailWord_894163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894163).length < 2 ^ (prefixWord ++ tailWord_894163).sum := by decide
  have hdescent : baseEnd_894163 < baseStart_894163 := by decide
  rcases family_descends (prefixWord ++ tailWord_894163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894170 : List Nat := [3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2]
def baseStart_894170 : Nat := 118140960795 + 894170 * 2 ^ 59
def prefixEnd_894170 : Nat := 4983230072969 + 3 ^ 40 * 894170 * 2
def baseEnd_894170 : Nat := 459138996830871789462793

theorem tailTrace_894170 : CollatzResearch.WordTrace tailWord_894170 prefixEnd_894170 459138996830871789462793 := by
  unfold tailWord_894170
  simp only [CollatzResearch.WordTrace]
  refine ⟨8153264792645569230769991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21742039447054851282053309 8153264792645569230769991)
  ·
    refine ⟨12229897188968353846154987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8153264792645569230769991 12229897188968353846154987)
    ·
      refine ⟨18344845783452530769232481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12229897188968353846154987 18344845783452530769232481)
      ·
        refine ⟨13758634337589398076924361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18344845783452530769232481 13758634337589398076924361)
        ·
          refine ⟨10318975753192048557693271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13758634337589398076924361 10318975753192048557693271)
          ·
            refine ⟨15478463629788072836539907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10318975753192048557693271 15478463629788072836539907)
            ·
              refine ⟨23217695444682109254809861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15478463629788072836539907 23217695444682109254809861)
              ·
                refine ⟨4353317895877895485276849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23217695444682109254809861 4353317895877895485276849)
                ·
                  refine ⟨3264988421908421613957637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4353317895877895485276849 3264988421908421613957637)
                  ·
                    refine ⟨612185329107829052617057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3264988421908421613957637 612185329107829052617057)
                    ·
                      refine ⟨459138996830871789462793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 612185329107829052617057 459138996830871789462793)
                      ·
                        rfl

theorem cell23_894170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2].length) (baseStart_894170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894170 prefixEnd_894170 := by exact prefixLift 894170
  have htrace : WordTrace (prefixWord ++ tailWord_894170) baseStart_894170 baseEnd_894170 := by
    simpa [prefixWord, tailWord_894170, baseEnd_894170] using wordTrace_append hprefix tailTrace_894170
  have hstable : (prefixWord ++ tailWord_894170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894170).length < 2 ^ (prefixWord ++ tailWord_894170).sum := by decide
  have hdescent : baseEnd_894170 < baseStart_894170 := by decide
  rcases family_descends (prefixWord ++ tailWord_894170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894190 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 4, 2, 3]
def baseStart_894190 : Nat := 118140960795 + 894190 * 2 ^ 59
def prefixEnd_894190 : Nat := 4983230072969 + 3 ^ 40 * 894190 * 2
def baseEnd_894190 : Nat := 459149266443961711212701

theorem tailTrace_894190 : CollatzResearch.WordTrace tailWord_894190 prefixEnd_894190 459149266443961711212701 := by
  unfold tailWord_894190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4076723578813727542351003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21742525753673213559205349 4076723578813727542351003)
  ·
    refine ⟨6115085368220591313526505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4076723578813727542351003 6115085368220591313526505)
    ·
      refine ⟨4586314026165443485144879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6115085368220591313526505 4586314026165443485144879)
      ·
        refine ⟨6879471039248165227717319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4586314026165443485144879 6879471039248165227717319)
        ·
          refine ⟨10319206558872247841575979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6879471039248165227717319 10319206558872247841575979)
          ·
            refine ⟨15478809838308371762363969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10319206558872247841575979 15478809838308371762363969)
            ·
              refine ⟨11609107378731278821772977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15478809838308371762363969 11609107378731278821772977)
              ·
                refine ⟨8706830534048459116329733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11609107378731278821772977 8706830534048459116329733)
                ·
                  refine ⟨1632530725134086084311825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8706830534048459116329733 1632530725134086084311825)
                  ·
                    refine ⟨1224398043850564563233869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1632530725134086084311825 1224398043850564563233869)
                    ·
                      refine ⟨459149266443961711212701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1224398043850564563233869 459149266443961711212701)
                      ·
                        rfl

theorem cell23_894190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_894190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894190 prefixEnd_894190 := by exact prefixLift 894190
  have htrace : WordTrace (prefixWord ++ tailWord_894190) baseStart_894190 baseEnd_894190 := by
    simpa [prefixWord, tailWord_894190, baseEnd_894190] using wordTrace_append hprefix tailTrace_894190
  have hstable : (prefixWord ++ tailWord_894190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894190).length < 2 ^ (prefixWord ++ tailWord_894190).sum := by decide
  have hdescent : baseEnd_894190 < baseStart_894190 := by decide
  rcases family_descends (prefixWord ++ tailWord_894190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894204 : List Nat := [2, 2, 2, 1, 6, 1, 1, 1, 2, 1, 4]
def baseStart_894204 : Nat := 118140960795 + 894204 * 2 ^ 59
def prefixEnd_894204 : Nat := 4983230072969 + 3 ^ 40 * 894204 * 2
def baseEnd_894204 : Nat := 459156455173124656437637

theorem tailTrace_894204 : CollatzResearch.WordTrace tailWord_894204 prefixEnd_894204 459156455173124656437637 := by
  unfold tailWord_894204
  simp only [CollatzResearch.WordTrace]
  refine ⟨16307149626229550364908833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21742866168306067153211777 16307149626229550364908833)
  ·
    refine ⟨12230362219672162773681625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16307149626229550364908833 12230362219672162773681625)
    ·
      refine ⟨9172771664754122080261219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12230362219672162773681625 9172771664754122080261219)
      ·
        refine ⟨13759157497131183120391829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9172771664754122080261219 13759157497131183120391829)
        ·
          refine ⟨644960507678024208768367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13759157497131183120391829 644960507678024208768367)
          ·
            refine ⟨967440761517036313152551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644960507678024208768367 967440761517036313152551)
            ·
              refine ⟨1451161142275554469728827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 967440761517036313152551 1451161142275554469728827)
              ·
                refine ⟨2176741713413331704593241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1451161142275554469728827 2176741713413331704593241)
                ·
                  refine ⟨1632556285059998778444931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2176741713413331704593241 1632556285059998778444931)
                  ·
                    refine ⟨2448834427589998167667397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1632556285059998778444931 2448834427589998167667397)
                    ·
                      refine ⟨459156455173124656437637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2448834427589998167667397 459156455173124656437637)
                      ·
                        rfl

theorem cell23_894204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 2, 1, 4].length) (baseStart_894204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894204 prefixEnd_894204 := by exact prefixLift 894204
  have htrace : WordTrace (prefixWord ++ tailWord_894204) baseStart_894204 baseEnd_894204 := by
    simpa [prefixWord, tailWord_894204, baseEnd_894204] using wordTrace_append hprefix tailTrace_894204
  have hstable : (prefixWord ++ tailWord_894204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894204).length < 2 ^ (prefixWord ++ tailWord_894204).sum := by decide
  have hdescent : baseEnd_894204 < baseStart_894204 := by decide
  rcases family_descends (prefixWord ++ tailWord_894204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894207 : List Nat := [1, 1, 2, 2, 1, 7, 1, 1, 2, 2, 3]
def baseStart_894207 : Nat := 118140960795 + 894207 * 2 ^ 59
def prefixEnd_894207 : Nat := 4983230072969 + 3 ^ 40 * 894207 * 2
def baseEnd_894207 : Nat := 459157995615088144700123

theorem tailTrace_894207 : CollatzResearch.WordTrace tailWord_894207 prefixEnd_894207 459157995615088144700123 := by
  unfold tailWord_894207
  simp only [CollatzResearch.WordTrace]
  refine ⟨32614408671448232242176875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21742939114298821494784583 32614408671448232242176875)
  ·
    refine ⟨48921613007172348363265313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32614408671448232242176875 48921613007172348363265313)
    ·
      refine ⟨36691209755379261272448985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48921613007172348363265313 36691209755379261272448985)
      ·
        refine ⟨27518407316534445954336739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36691209755379261272448985 27518407316534445954336739)
        ·
          refine ⟨41277610974801668931505109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27518407316534445954336739 41277610974801668931505109)
          ·
            refine ⟨967444007221914115582151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 41277610974801668931505109 967444007221914115582151)
            ·
              refine ⟨1451166010832871173373227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 967444007221914115582151 1451166010832871173373227)
              ·
                refine ⟨2176749016249306760059841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1451166010832871173373227 2176749016249306760059841)
                ·
                  refine ⟨1632561762186980070044881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2176749016249306760059841 1632561762186980070044881)
                  ·
                    refine ⟨1224421321640235052533661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1632561762186980070044881 1224421321640235052533661)
                    ·
                      refine ⟨459157995615088144700123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1224421321640235052533661 459157995615088144700123)
                      ·
                        rfl

theorem cell23_894207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 2, 3].length) (baseStart_894207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894207 prefixEnd_894207 := by exact prefixLift 894207
  have htrace : WordTrace (prefixWord ++ tailWord_894207) baseStart_894207 baseEnd_894207 := by
    simpa [prefixWord, tailWord_894207, baseEnd_894207] using wordTrace_append hprefix tailTrace_894207
  have hstable : (prefixWord ++ tailWord_894207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894207).length < 2 ^ (prefixWord ++ tailWord_894207).sum := by decide
  have hdescent : baseEnd_894207 < baseStart_894207 := by decide
  rcases family_descends (prefixWord ++ tailWord_894207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894257 : List Nat := [1, 2, 2, 3, 3, 2, 2, 2, 1, 5]
def baseStart_894257 : Nat := 118140960795 + 894257 * 2 ^ 59
def prefixEnd_894257 : Nat := 4983230072969 + 3 ^ 40 * 894257 * 2
def baseEnd_894257 : Nat := 153061223215937649691631

theorem tailTrace_894257 : CollatzResearch.WordTrace tailWord_894257 prefixEnd_894257 153061223215937649691631 := by
  unfold tailWord_894257
  simp only [CollatzResearch.WordTrace]
  refine ⟨32616232321267090781497025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21744154880844727187664683 32616232321267090781497025)
  ·
    refine ⟨24462174240950318086122769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32616232321267090781497025 24462174240950318086122769)
    ·
      refine ⟨18346630680712738564592077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24462174240950318086122769 18346630680712738564592077)
      ·
        refine ⟨6879986505267276961722029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18346630680712738564592077 6879986505267276961722029)
        ·
          refine ⟨2579994939475228860645761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6879986505267276961722029 2579994939475228860645761)
          ·
            refine ⟨1934996204606421645484321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2579994939475228860645761 1934996204606421645484321)
            ·
              refine ⟨1451247153454816234113241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1934996204606421645484321 1451247153454816234113241)
              ·
                refine ⟨1088435365091112175584931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1451247153454816234113241 1088435365091112175584931)
                ·
                  refine ⟨1632653047636668263377397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1088435365091112175584931 1632653047636668263377397)
                  ·
                    refine ⟨153061223215937649691631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1632653047636668263377397 153061223215937649691631)
                    ·
                      rfl

theorem cell23_894257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 5].length) (baseStart_894257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894257 prefixEnd_894257 := by exact prefixLift 894257
  have htrace : WordTrace (prefixWord ++ tailWord_894257) baseStart_894257 baseEnd_894257 := by
    simpa [prefixWord, tailWord_894257, baseEnd_894257] using wordTrace_append hprefix tailTrace_894257
  have hstable : (prefixWord ++ tailWord_894257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894257).length < 2 ^ (prefixWord ++ tailWord_894257).sum := by decide
  have hdescent : baseEnd_894257 < baseStart_894257 := by decide
  rcases family_descends (prefixWord ++ tailWord_894257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894270 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 3, 6]
def baseStart_894270 : Nat := 118140960795 + 894270 * 2 ^ 59
def prefixEnd_894270 : Nat := 4983230072969 + 3 ^ 40 * 894270 * 2
def baseEnd_894270 : Nat := 153063448298773799404111

theorem tailTrace_894270 : CollatzResearch.WordTrace tailWord_894270 prefixEnd_894270 153063448298773799404111 := by
  unfold tailWord_894270
  simp only [CollatzResearch.WordTrace]
  refine ⟨4077088308777499250215033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21744470980146662667813509 4077088308777499250215033)
  ·
    refine ⟨3057816231583124437661275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4077088308777499250215033 3057816231583124437661275)
    ·
      refine ⟨4586724347374686656491913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3057816231583124437661275 4586724347374686656491913)
      ·
        refine ⟨3440043260531014992368935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4586724347374686656491913 3440043260531014992368935)
        ·
          refine ⟨5160064890796522488553403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3440043260531014992368935 5160064890796522488553403)
          ·
            refine ⟨7740097336194783732830105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5160064890796522488553403 7740097336194783732830105)
            ·
              refine ⟨5805073002146087799622579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7740097336194783732830105 5805073002146087799622579)
              ·
                refine ⟨8707609503219131699433869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5805073002146087799622579 8707609503219131699433869)
                ·
                  refine ⟨3265353563707174387287701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8707609503219131699433869 3265353563707174387287701)
                  ·
                    refine ⟨153063448298773799404111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3265353563707174387287701 153063448298773799404111)
                    ·
                      rfl

theorem cell23_894270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_894270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894270 prefixEnd_894270 := by exact prefixLift 894270
  have htrace : WordTrace (prefixWord ++ tailWord_894270) baseStart_894270 baseEnd_894270 := by
    simpa [prefixWord, tailWord_894270, baseEnd_894270] using wordTrace_append hprefix tailTrace_894270
  have hstable : (prefixWord ++ tailWord_894270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894270).length < 2 ^ (prefixWord ++ tailWord_894270).sum := by decide
  have hdescent : baseEnd_894270 < baseStart_894270 := by decide
  rcases family_descends (prefixWord ++ tailWord_894270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894271 : List Nat := [1, 1, 2, 2, 4, 4, 1, 3, 1, 1, 3]
def baseStart_894271 : Nat := 118140960795 + 894271 * 2 ^ 59
def prefixEnd_894271 : Nat := 4983230072969 + 3 ^ 40 * 894271 * 2
def baseEnd_894271 : Nat := 459190858376975894299829

theorem tailTrace_894271 : CollatzResearch.WordTrace tailWord_894271 prefixEnd_894271 459190858376975894299829 := by
  unfold tailWord_894271
  simp only [CollatzResearch.WordTrace]
  refine ⟨32616742943216371172506667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21744495295477580781671111 32616742943216371172506667)
  ·
    refine ⟨48925114414824556758760001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32616742943216371172506667 48925114414824556758760001)
    ·
      refine ⟨36693835811118417569070001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48925114414824556758760001 36693835811118417569070001)
      ·
        refine ⟨27520376858338813176802501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36693835811118417569070001 27520376858338813176802501)
        ·
          refine ⟨5160070660938527470650469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27520376858338813176802501 5160070660938527470650469)
          ·
            refine ⟨967513248925973900746963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5160070660938527470650469 967513248925973900746963)
            ·
              refine ⟨1451269873388960851120445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 967513248925973900746963 1451269873388960851120445)
              ·
                refine ⟨544226202520860319170167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1451269873388960851120445 544226202520860319170167)
                ·
                  refine ⟨816339303781290478755251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 544226202520860319170167 816339303781290478755251)
                  ·
                    refine ⟨1224508955671935718132877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 816339303781290478755251 1224508955671935718132877)
                    ·
                      refine ⟨459190858376975894299829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1224508955671935718132877 459190858376975894299829)
                      ·
                        rfl

theorem cell23_894271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 3, 1, 1, 3].length) (baseStart_894271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894271 prefixEnd_894271 := by exact prefixLift 894271
  have htrace : WordTrace (prefixWord ++ tailWord_894271) baseStart_894271 baseEnd_894271 := by
    simpa [prefixWord, tailWord_894271, baseEnd_894271] using wordTrace_append hprefix tailTrace_894271
  have hstable : (prefixWord ++ tailWord_894271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894271).length < 2 ^ (prefixWord ++ tailWord_894271).sum := by decide
  have hdescent : baseEnd_894271 < baseStart_894271 := by decide
  rcases family_descends (prefixWord ++ tailWord_894271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894277 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 5, 2, 2]
def baseStart_894277 : Nat := 118140960795 + 894277 * 2 ^ 59
def prefixEnd_894277 : Nat := 4983230072969 + 3 ^ 40 * 894277 * 2
def baseEnd_894277 : Nat := 459193939260902870824801

theorem tailTrace_894277 : CollatzResearch.WordTrace tailWord_894277 prefixEnd_894277 459193939260902870824801 := by
  unfold tailWord_894277
  simp only [CollatzResearch.WordTrace]
  refine ⟨32616961781194634197225085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21744641187463089464816723 32616961781194634197225085)
  ·
    refine ⟨12231360667947987823959407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32616961781194634197225085 12231360667947987823959407)
    ·
      refine ⟨18347041001921981735939111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12231360667947987823959407 18347041001921981735939111)
      ·
        refine ⟨27520561502882972603908667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18347041001921981735939111 27520561502882972603908667)
        ·
          refine ⟨41280842254324458905863001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27520561502882972603908667 41280842254324458905863001)
          ·
            refine ⟨30960631690743344179397251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41280842254324458905863001 30960631690743344179397251)
            ·
              refine ⟨46440947536115016269095877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30960631690743344179397251 46440947536115016269095877)
              ·
                refine ⟨8707677663021565550455477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46440947536115016269095877 8707677663021565550455477)
                ·
                  refine ⟨816344780908271770355201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8707677663021565550455477 816344780908271770355201)
                  ·
                    refine ⟨612258585681203827766401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 816344780908271770355201 612258585681203827766401)
                    ·
                      refine ⟨459193939260902870824801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 612258585681203827766401 459193939260902870824801)
                      ·
                        rfl

theorem cell23_894277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 5, 2, 2].length) (baseStart_894277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894277 prefixEnd_894277 := by exact prefixLift 894277
  have htrace : WordTrace (prefixWord ++ tailWord_894277) baseStart_894277 baseEnd_894277 := by
    simpa [prefixWord, tailWord_894277, baseEnd_894277] using wordTrace_append hprefix tailTrace_894277
  have hstable : (prefixWord ++ tailWord_894277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894277).length < 2 ^ (prefixWord ++ tailWord_894277).sum := by decide
  have hdescent : baseEnd_894277 < baseStart_894277 := by decide
  rcases family_descends (prefixWord ++ tailWord_894277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894280 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 5, 2, 3]
def baseStart_894280 : Nat := 118140960795 + 894280 * 2 ^ 59
def prefixEnd_894280 : Nat := 4983230072969 + 3 ^ 40 * 894280 * 2
def baseEnd_894280 : Nat := 459195479702866359087287

theorem tailTrace_894280 : CollatzResearch.WordTrace tailWord_894280 prefixEnd_894280 459195479702866359087287 := by
  unfold tailWord_894280
  simp only [CollatzResearch.WordTrace]
  refine ⟨16308535600091882854792147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21744714133455843806389529 16308535600091882854792147)
  ·
    refine ⟨24462803400137824282188221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16308535600091882854792147 24462803400137824282188221)
    ·
      refine ⟨9173551275051684105820583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24462803400137824282188221 9173551275051684105820583)
      ·
        refine ⟨13760326912577526158730875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9173551275051684105820583 13760326912577526158730875)
        ·
          refine ⟨20640490368866289238096313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13760326912577526158730875 20640490368866289238096313)
          ·
            refine ⟨15480367776649716928572235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20640490368866289238096313 15480367776649716928572235)
            ·
              refine ⟨23220551664974575392858353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15480367776649716928572235 23220551664974575392858353)
              ·
                refine ⟨17415413748730931544643765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23220551664974575392858353 17415413748730931544643765)
                ·
                  refine ⟨1632695038943524832310353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17415413748730931544643765 1632695038943524832310353)
                  ·
                    refine ⟨1224521279207643624232765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1632695038943524832310353 1224521279207643624232765)
                    ·
                      refine ⟨459195479702866359087287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1224521279207643624232765 459195479702866359087287)
                      ·
                        rfl

theorem cell23_894280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_894280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894280 prefixEnd_894280 := by exact prefixLift 894280
  have htrace : WordTrace (prefixWord ++ tailWord_894280) baseStart_894280 baseEnd_894280 := by
    simpa [prefixWord, tailWord_894280, baseEnd_894280] using wordTrace_append hprefix tailTrace_894280
  have hstable : (prefixWord ++ tailWord_894280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894280).length < 2 ^ (prefixWord ++ tailWord_894280).sum := by decide
  have hdescent : baseEnd_894280 < baseStart_894280 := by decide
  rcases family_descends (prefixWord ++ tailWord_894280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894303 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 6]
def baseStart_894303 : Nat := 118140960795 + 894303 * 2 ^ 59
def prefixEnd_894303 : Nat := 4983230072969 + 3 ^ 40 * 894303 * 2
def baseEnd_894303 : Nat := 459207289757919769099681

theorem tailTrace_894303 : CollatzResearch.WordTrace tailWord_894303 prefixEnd_894303 459207289757919769099681 := by
  unfold tailWord_894303
  simp only [CollatzResearch.WordTrace]
  refine ⟨32617910079100440637671563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21745273386066960425114375 32617910079100440637671563)
  ·
    refine ⟨48926865118650660956507345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32617910079100440637671563 48926865118650660956507345)
    ·
      refine ⟨36695148838987995717380509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48926865118650660956507345 36695148838987995717380509)
      ·
        refine ⟨13760680814620498394017691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36695148838987995717380509 13760680814620498394017691)
        ·
          refine ⟨20641021221930747591026537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13760680814620498394017691 20641021221930747591026537)
          ·
            refine ⟨15480765916448060693269903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20641021221930747591026537 15480765916448060693269903)
            ·
              refine ⟨23221148874672091039904855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15480765916448060693269903 23221148874672091039904855)
              ·
                refine ⟨34831723312008136559857283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23221148874672091039904855 34831723312008136559857283)
                ·
                  refine ⟨52247584968012204839785925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34831723312008136559857283 52247584968012204839785925)
                  ·
                    refine ⟨9796422181502288407459861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52247584968012204839785925 9796422181502288407459861)
                    ·
                      refine ⟨459207289757919769099681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9796422181502288407459861 459207289757919769099681)
                      ·
                        rfl

theorem cell23_894303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_894303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894303 prefixEnd_894303 := by exact prefixLift 894303
  have htrace : WordTrace (prefixWord ++ tailWord_894303) baseStart_894303 baseEnd_894303 := by
    simpa [prefixWord, tailWord_894303, baseEnd_894303] using wordTrace_append hprefix tailTrace_894303
  have hstable : (prefixWord ++ tailWord_894303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894303).length < 2 ^ (prefixWord ++ tailWord_894303).sum := by decide
  have hdescent : baseEnd_894303 < baseStart_894303 := by decide
  rcases family_descends (prefixWord ++ tailWord_894303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894304 : List Nat := [2, 1, 1, 3, 4, 1, 4, 1, 2, 4]
def baseStart_894304 : Nat := 118140960795 + 894304 * 2 ^ 59
def prefixEnd_894304 : Nat := 4983230072969 + 3 ^ 40 * 894304 * 2
def baseEnd_894304 : Nat := 153069267746191421729059

theorem tailTrace_894304 : CollatzResearch.WordTrace tailWord_894304 prefixEnd_894304 153069267746191421729059 := by
  unfold tailWord_894304
  simp only [CollatzResearch.WordTrace]
  refine ⟨16308973276048408904228983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21745297701397878538971977 16308973276048408904228983)
  ·
    refine ⟨24463459914072613356343475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16308973276048408904228983 24463459914072613356343475)
    ·
      refine ⟨36695189871108920034515213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24463459914072613356343475 36695189871108920034515213)
      ·
        refine ⟨13760696201665845012943205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36695189871108920034515213 13760696201665845012943205)
        ·
          refine ⟨2580130537812345939926851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13760696201665845012943205 2580130537812345939926851)
          ·
            refine ⟨3870195806718518909890277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2580130537812345939926851 3870195806718518909890277)
            ·
              refine ⟨725661713759722295604427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3870195806718518909890277 725661713759722295604427)
              ·
                refine ⟨1088492570639583443406641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 725661713759722295604427 1088492570639583443406641)
                ·
                  refine ⟨816369427979687582554981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1088492570639583443406641 816369427979687582554981)
                  ·
                    refine ⟨153069267746191421729059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 816369427979687582554981 153069267746191421729059)
                    ·
                      rfl

theorem cell23_894304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 2, 4].length) (baseStart_894304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894304 prefixEnd_894304 := by exact prefixLift 894304
  have htrace : WordTrace (prefixWord ++ tailWord_894304) baseStart_894304 baseEnd_894304 := by
    simpa [prefixWord, tailWord_894304, baseEnd_894304] using wordTrace_append hprefix tailTrace_894304
  have hstable : (prefixWord ++ tailWord_894304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894304).length < 2 ^ (prefixWord ++ tailWord_894304).sum := by decide
  have hdescent : baseEnd_894304 < baseStart_894304 := by decide
  rcases family_descends (prefixWord ++ tailWord_894304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894311 : List Nat := [1, 1, 5, 1, 5, 1, 1, 2, 1, 1, 4]
def baseStart_894311 : Nat := 118140960795 + 894311 * 2 ^ 59
def prefixEnd_894311 : Nat := 4983230072969 + 3 ^ 40 * 894311 * 2
def baseEnd_894311 : Nat := 459211397603155737799645

theorem tailTrace_894311 : CollatzResearch.WordTrace tailWord_894311 prefixEnd_894311 459211397603155737799645 := by
  unfold tailWord_894311
  simp only [CollatzResearch.WordTrace]
  refine ⟨32618201863071458003962787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21745467908714305335975191 32618201863071458003962787)
  ·
    refine ⟨48927302794607187005944181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32618201863071458003962787 48927302794607187005944181)
    ·
      refine ⟨4586934636994423781807267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48927302794607187005944181 4586934636994423781807267)
      ·
        refine ⟨6880401955491635672710901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4586934636994423781807267 6880401955491635672710901)
        ·
          refine ⟨645037683327340844316647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6880401955491635672710901 645037683327340844316647)
          ·
            refine ⟨967556524991011266474971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645037683327340844316647 967556524991011266474971)
            ·
              refine ⟨1451334787486516899712457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 967556524991011266474971 1451334787486516899712457)
              ·
                refine ⟨1088501090614887674784343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1451334787486516899712457 1088501090614887674784343)
                ·
                  refine ⟨1632751635922331512176515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1088501090614887674784343 1632751635922331512176515)
                  ·
                    refine ⟨2449127453883497268264773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1632751635922331512176515 2449127453883497268264773)
                    ·
                      refine ⟨459211397603155737799645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2449127453883497268264773 459211397603155737799645)
                      ·
                        rfl

theorem cell23_894311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_894311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894311 prefixEnd_894311 := by exact prefixLift 894311
  have htrace : WordTrace (prefixWord ++ tailWord_894311) baseStart_894311 baseEnd_894311 := by
    simpa [prefixWord, tailWord_894311, baseEnd_894311] using wordTrace_append hprefix tailTrace_894311
  have hstable : (prefixWord ++ tailWord_894311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894311).length < 2 ^ (prefixWord ++ tailWord_894311).sum := by decide
  have hdescent : baseEnd_894311 < baseStart_894311 := by decide
  rcases family_descends (prefixWord ++ tailWord_894311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894313 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 4, 7]
def baseStart_894313 : Nat := 118140960795 + 894313 * 2 ^ 59
def prefixEnd_894313 : Nat := 4983230072969 + 3 ^ 40 * 894313 * 2
def baseEnd_894313 : Nat := 153070808188154909991545

theorem tailTrace_894313 : CollatzResearch.WordTrace tailWord_894313 prefixEnd_894313 153070808188154909991545 := by
  unfold tailWord_894313
  simp only [CollatzResearch.WordTrace]
  refine ⟨32618274809064212345535593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21745516539376141563690395 32618274809064212345535593)
  ·
    refine ⟨24463706106798159259151695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32618274809064212345535593 24463706106798159259151695)
    ·
      refine ⟨36695559160197238888727543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24463706106798159259151695 36695559160197238888727543)
      ·
        refine ⟨55043338740295858333091315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36695559160197238888727543 55043338740295858333091315)
        ·
          refine ⟨82565008110443787499636973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55043338740295858333091315 82565008110443787499636973)
          ·
            refine ⟨30961878041416420312363865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82565008110443787499636973 30961878041416420312363865)
            ·
              refine ⟨23221408531062315234272899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30961878041416420312363865 23221408531062315234272899)
              ·
                refine ⟨34832112796593472851409349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23221408531062315234272899 34832112796593472851409349)
                ·
                  refine ⟨6531021149361276159639253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34832112796593472851409349 6531021149361276159639253)
                  ·
                    refine ⟨153070808188154909991545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6531021149361276159639253 153070808188154909991545)
                    ·
                      rfl

theorem cell23_894313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 7].length) (baseStart_894313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894313 prefixEnd_894313 := by exact prefixLift 894313
  have htrace : WordTrace (prefixWord ++ tailWord_894313) baseStart_894313 baseEnd_894313 := by
    simpa [prefixWord, tailWord_894313, baseEnd_894313] using wordTrace_append hprefix tailTrace_894313
  have hstable : (prefixWord ++ tailWord_894313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894313).length < 2 ^ (prefixWord ++ tailWord_894313).sum := by decide
  have hdescent : baseEnd_894313 < baseStart_894313 := by decide
  rcases family_descends (prefixWord ++ tailWord_894313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894314 : List Nat := [3, 1, 3, 3, 2, 1, 1, 1, 3, 2, 3]
def baseStart_894314 : Nat := 118140960795 + 894314 * 2 ^ 59
def prefixEnd_894314 : Nat := 4983230072969 + 3 ^ 40 * 894314 * 2
def baseEnd_894314 : Nat := 459212938045119226062131

theorem tailTrace_894314 : CollatzResearch.WordTrace tailWord_894314 prefixEnd_894314 459212938045119226062131 := by
  unfold tailWord_894314
  simp only [CollatzResearch.WordTrace]
  refine ⟨8154577820515147379080499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21745540854707059677547997 8154577820515147379080499)
  ·
    refine ⟨12231866730772721068620749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8154577820515147379080499 12231866730772721068620749)
    ·
      refine ⟨4586950024039770400732781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12231866730772721068620749 4586950024039770400732781)
      ·
        refine ⟨1720106259014913900274793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4586950024039770400732781 1720106259014913900274793)
        ·
          refine ⟨1290079694261185425206095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1720106259014913900274793 1290079694261185425206095)
          ·
            refine ⟨1935119541391778137809143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1290079694261185425206095 1935119541391778137809143)
            ·
              refine ⟨2902679312087667206713715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1935119541391778137809143 2902679312087667206713715)
              ·
                refine ⟨4354018968131500810070573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2902679312087667206713715 4354018968131500810070573)
                ·
                  refine ⟨1632757113049312803776465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4354018968131500810070573 1632757113049312803776465)
                  ·
                    refine ⟨1224567834786984602832349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1632757113049312803776465 1224567834786984602832349)
                    ·
                      refine ⟨459212938045119226062131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1224567834786984602832349 459212938045119226062131)
                      ·
                        rfl

theorem cell23_894314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_894314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894314 prefixEnd_894314 := by exact prefixLift 894314
  have htrace : WordTrace (prefixWord ++ tailWord_894314) baseStart_894314 baseEnd_894314 := by
    simpa [prefixWord, tailWord_894314, baseEnd_894314] using wordTrace_append hprefix tailTrace_894314
  have hstable : (prefixWord ++ tailWord_894314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894314).length < 2 ^ (prefixWord ++ tailWord_894314).sum := by decide
  have hdescent : baseEnd_894314 < baseStart_894314 := by decide
  rcases family_descends (prefixWord ++ tailWord_894314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894334 : List Nat := [4, 2, 3, 2, 2, 10]
def baseStart_894334 : Nat := 118140960795 + 894334 * 2 ^ 59
def prefixEnd_894334 : Nat := 4983230072969 + 3 ^ 40 * 894334 * 2
def baseEnd_894334 : Nat := 1889807438922671390173

theorem tailTrace_894334 : CollatzResearch.WordTrace tailWord_894334 prefixEnd_894334 1889807438922671390173 := by
  unfold tailWord_894334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4077380092748516616506257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21746027161325421954700037 4077380092748516616506257)
  ·
    refine ⟨3058035069561387462379693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4077380092748516616506257 3058035069561387462379693)
    ·
      refine ⟨1146763151085520298392385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3058035069561387462379693 1146763151085520298392385)
      ·
        refine ⟨860072363314140223794289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1146763151085520298392385 860072363314140223794289)
        ·
          refine ⟨645054272485605167845717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 860072363314140223794289 645054272485605167845717)
          ·
            refine ⟨1889807438922671390173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 645054272485605167845717 1889807438922671390173)
            ·
              rfl

theorem cell23_894334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 10].length) (baseStart_894334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894334 prefixEnd_894334 := by exact prefixLift 894334
  have htrace : WordTrace (prefixWord ++ tailWord_894334) baseStart_894334 baseEnd_894334 := by
    simpa [prefixWord, tailWord_894334, baseEnd_894334] using wordTrace_append hprefix tailTrace_894334
  have hstable : (prefixWord ++ tailWord_894334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894334).length < 2 ^ (prefixWord ++ tailWord_894334).sum := by decide
  have hdescent : baseEnd_894334 < baseStart_894334 := by decide
  rcases family_descends (prefixWord ++ tailWord_894334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894344 : List Nat := [2, 1, 3, 3, 1, 2, 1, 4, 2, 1, 3]
def baseStart_894344 : Nat := 118140960795 + 894344 * 2 ^ 59
def prefixEnd_894344 : Nat := 4983230072969 + 3 ^ 40 * 894344 * 2
def baseEnd_894344 : Nat := 459228342464754108686993

theorem tailTrace_894344 : CollatzResearch.WordTrace tailWord_894344 prefixEnd_894344 459228342464754108686993 := by
  unfold tailWord_894344
  simp only [CollatzResearch.WordTrace]
  refine ⟨16309702735975952319957043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21746270314634603093276057 16309702735975952319957043)
  ·
    refine ⟨24464554103963928479935565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16309702735975952319957043 24464554103963928479935565)
    ·
      refine ⟨9174207788986473179975837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24464554103963928479935565 9174207788986473179975837)
      ·
        refine ⟨3440327920869927442490939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9174207788986473179975837 3440327920869927442490939)
        ·
          refine ⟨5160491881304891163736409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3440327920869927442490939 5160491881304891163736409)
          ·
            refine ⟨3870368910978668372802307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5160491881304891163736409 3870368910978668372802307)
            ·
              refine ⟨5805553366468002559203461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3870368910978668372802307 5805553366468002559203461)
              ·
                refine ⟨1088541256212750479850649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5805553366468002559203461 1088541256212750479850649)
                ·
                  refine ⟨816405942159562859887987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1088541256212750479850649 816405942159562859887987)
                  ·
                    refine ⟨1224608913239344289831981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 816405942159562859887987 1224608913239344289831981)
                    ·
                      refine ⟨459228342464754108686993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1224608913239344289831981 459228342464754108686993)
                      ·
                        rfl

theorem cell23_894344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_894344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894344 prefixEnd_894344 := by exact prefixLift 894344
  have htrace : WordTrace (prefixWord ++ tailWord_894344) baseStart_894344 baseEnd_894344 := by
    simpa [prefixWord, tailWord_894344, baseEnd_894344] using wordTrace_append hprefix tailTrace_894344
  have hstable : (prefixWord ++ tailWord_894344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894344).length < 2 ^ (prefixWord ++ tailWord_894344).sum := by decide
  have hdescent : baseEnd_894344 < baseStart_894344 := by decide
  rcases family_descends (prefixWord ++ tailWord_894344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894345 : List Nat := [1, 2, 1, 1, 7, 2, 2, 2, 1, 2, 2]
def baseStart_894345 : Nat := 118140960795 + 894345 * 2 ^ 59
def prefixEnd_894345 : Nat := 4983230072969 + 3 ^ 40 * 894345 * 2
def baseEnd_894345 : Nat := 459228855945408604774489

theorem tailTrace_894345 : CollatzResearch.WordTrace tailWord_894345 prefixEnd_894345 459228855945408604774489 := by
  unfold tailWord_894345
  simp only [CollatzResearch.WordTrace]
  refine ⟨32619441944948281810700489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21746294629965521207133659 32619441944948281810700489)
  ·
    refine ⟨24464581458711211358025367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32619441944948281810700489 24464581458711211358025367)
    ·
      refine ⟨36696872188066817037038051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24464581458711211358025367 36696872188066817037038051)
      ·
        refine ⟨55045308282100225555557077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36696872188066817037038051 55045308282100225555557077)
        ·
          refine ⟨1290124412861724036458369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 55045308282100225555557077 1290124412861724036458369)
          ·
            refine ⟨967593309646293027343777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1290124412861724036458369 967593309646293027343777)
            ·
              refine ⟨725694982234719770507833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 967593309646293027343777 725694982234719770507833)
              ·
                refine ⟨544271236676039827880875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 725694982234719770507833 544271236676039827880875)
                ·
                  refine ⟨816406855014059741821313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 544271236676039827880875 816406855014059741821313)
                  ·
                    refine ⟨612305141260544806365985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 816406855014059741821313 612305141260544806365985)
                    ·
                      refine ⟨459228855945408604774489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 612305141260544806365985 459228855945408604774489)
                      ·
                        rfl

theorem cell23_894345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 2, 1, 2, 2].length) (baseStart_894345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894345 prefixEnd_894345 := by exact prefixLift 894345
  have htrace : WordTrace (prefixWord ++ tailWord_894345) baseStart_894345 baseEnd_894345 := by
    simpa [prefixWord, tailWord_894345, baseEnd_894345] using wordTrace_append hprefix tailTrace_894345
  have hstable : (prefixWord ++ tailWord_894345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894345).length < 2 ^ (prefixWord ++ tailWord_894345).sum := by decide
  have hdescent : baseEnd_894345 < baseStart_894345 := by decide
  rcases family_descends (prefixWord ++ tailWord_894345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894407 : List Nat := [1, 1, 4, 1, 1, 3, 1, 6, 5]
def baseStart_894407 : Nat := 118140960795 + 894407 * 2 ^ 59
def prefixEnd_894407 : Nat := 4983230072969 + 3 ^ 40 * 894407 * 2
def baseEnd_894407 : Nat := 51028965749554151355467

theorem tailTrace_894407 : CollatzResearch.WordTrace tailWord_894407 prefixEnd_894407 51028965749554151355467 := by
  unfold tailWord_894407
  simp only [CollatzResearch.WordTrace]
  refine ⟨32621703270723666399457475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21747802180482444266304983 32621703270723666399457475)
  ·
    refine ⟨48932554906085499599186213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32621703270723666399457475 48932554906085499599186213)
    ·
      refine ⟨9174854044891031174847415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48932554906085499599186213 9174854044891031174847415)
      ·
        refine ⟨13762281067336546762271123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9174854044891031174847415 13762281067336546762271123)
        ·
          refine ⟨20643421601004820143406685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13762281067336546762271123 20643421601004820143406685)
          ·
            refine ⟨7741283100376807553777507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20643421601004820143406685 7741283100376807553777507)
            ·
              refine ⟨11611924650565211330666261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7741283100376807553777507 11611924650565211330666261)
              ·
                refine ⟨544308967995244281124981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11611924650565211330666261 544308967995244281124981)
                ·
                  refine ⟨51028965749554151355467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 544308967995244281124981 51028965749554151355467)
                  ·
                    rfl

theorem cell23_894407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 6, 5].length) (baseStart_894407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894407 prefixEnd_894407 := by exact prefixLift 894407
  have htrace : WordTrace (prefixWord ++ tailWord_894407) baseStart_894407 baseEnd_894407 := by
    simpa [prefixWord, tailWord_894407, baseEnd_894407] using wordTrace_append hprefix tailTrace_894407
  have hstable : (prefixWord ++ tailWord_894407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894407).length < 2 ^ (prefixWord ++ tailWord_894407).sum := by decide
  have hdescent : baseEnd_894407 < baseStart_894407 := by decide
  rcases family_descends (prefixWord ++ tailWord_894407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894437 : List Nat := [1, 3, 1, 5, 1, 1, 2, 1, 1, 7]
def baseStart_894437 : Nat := 118140960795 + 894437 * 2 ^ 59
def prefixEnd_894437 : Nat := 4983230072969 + 3 ^ 40 * 894437 * 2
def baseEnd_894437 : Nat := 153092032055207414941355

theorem tailTrace_894437 : CollatzResearch.WordTrace tailWord_894437 prefixEnd_894437 153092032055207414941355 := by
  unfold tailWord_894437
  simp only [CollatzResearch.WordTrace]
  refine ⟨32622797460614981523049565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21748531640409987682033043 32622797460614981523049565)
  ·
    refine ⟨12233549047730618071143587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32622797460614981523049565 12233549047730618071143587)
    ·
      refine ⟨18350323571595927106715381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12233549047730618071143587 18350323571595927106715381)
      ·
        refine ⟨1720342834837118166254567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18350323571595927106715381 1720342834837118166254567)
        ·
          refine ⟨2580514252255677249381851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1720342834837118166254567 2580514252255677249381851)
          ·
            refine ⟨3870771378383515874072777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2580514252255677249381851 3870771378383515874072777)
            ·
              refine ⟨2903078533787636905554583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3870771378383515874072777 2903078533787636905554583)
              ·
                refine ⟨4354617800681455358331875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2903078533787636905554583 4354617800681455358331875)
                ·
                  refine ⟨6531926701022183037497813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4354617800681455358331875 6531926701022183037497813)
                  ·
                    refine ⟨153092032055207414941355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6531926701022183037497813 153092032055207414941355)
                    ·
                      rfl

theorem cell23_894437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 7].length) (baseStart_894437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894437 prefixEnd_894437 := by exact prefixLift 894437
  have htrace : WordTrace (prefixWord ++ tailWord_894437) baseStart_894437 baseEnd_894437 := by
    simpa [prefixWord, tailWord_894437, baseEnd_894437] using wordTrace_append hprefix tailTrace_894437
  have hstable : (prefixWord ++ tailWord_894437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894437).length < 2 ^ (prefixWord ++ tailWord_894437).sum := by decide
  have hdescent : baseEnd_894437 < baseStart_894437 := by decide
  rcases family_descends (prefixWord ++ tailWord_894437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894454 : List Nat := [5, 1, 1, 1, 2, 3, 1, 2, 2, 5]
def baseStart_894454 : Nat := 118140960795 + 894454 * 2 ^ 59
def prefixEnd_894454 : Nat := 4983230072969 + 3 ^ 40 * 894454 * 2
def baseEnd_894454 : Nat := 153094941778916226103829

theorem tailTrace_894454 : CollatzResearch.WordTrace tailWord_894454 prefixEnd_894454 153094941778916226103829 := by
  unfold tailWord_894454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2038963593847087089151151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21748945001035595617612277 2038963593847087089151151)
  ·
    refine ⟨3058445390770630633726727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2038963593847087089151151 3058445390770630633726727)
    ·
      refine ⟨4587668086155945950590091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3058445390770630633726727 4587668086155945950590091)
      ·
        refine ⟨6881502129233918925885137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4587668086155945950590091 6881502129233918925885137)
        ·
          refine ⟨5161126596925439194413853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6881502129233918925885137 5161126596925439194413853)
          ·
            refine ⟨1935422473847039697905195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5161126596925439194413853 1935422473847039697905195)
            ·
              refine ⟨2903133710770559546857793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1935422473847039697905195 2903133710770559546857793)
              ·
                refine ⟨2177350283077919660143345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2903133710770559546857793 2177350283077919660143345)
                ·
                  refine ⟨1633012712308439745107509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2177350283077919660143345 1633012712308439745107509)
                  ·
                    refine ⟨153094941778916226103829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1633012712308439745107509 153094941778916226103829)
                    ·
                      rfl

theorem cell23_894454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_894454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894454 prefixEnd_894454 := by exact prefixLift 894454
  have htrace : WordTrace (prefixWord ++ tailWord_894454) baseStart_894454 baseEnd_894454 := by
    simpa [prefixWord, tailWord_894454, baseEnd_894454] using wordTrace_append hprefix tailTrace_894454
  have hstable : (prefixWord ++ tailWord_894454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894454).length < 2 ^ (prefixWord ++ tailWord_894454).sum := by decide
  have hdescent : baseEnd_894454 < baseStart_894454 := by decide
  rcases family_descends (prefixWord ++ tailWord_894454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894467 : List Nat := [1, 1, 1, 3, 2, 1, 2, 5, 3, 4]
def baseStart_894467 : Nat := 118140960795 + 894467 * 2 ^ 59
def prefixEnd_894467 : Nat := 4983230072969 + 3 ^ 40 * 894467 * 2
def baseEnd_894467 : Nat := 153097166861752375816309

theorem tailTrace_894467 : CollatzResearch.WordTrace tailWord_894467 prefixEnd_894467 153097166861752375816309 := by
  unfold tailWord_894467
  simp only [CollatzResearch.WordTrace]
  refine ⟨32623891650506296646641655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21749261100337531097761103 32623891650506296646641655)
  ·
    refine ⟨48935837475759444969962483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32623891650506296646641655 48935837475759444969962483)
    ·
      refine ⟨73403756213639167454943725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48935837475759444969962483 73403756213639167454943725)
      ·
        refine ⟨27526408580114687795603897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73403756213639167454943725 27526408580114687795603897)
        ·
          refine ⟨20644806435086015846702923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27526408580114687795603897 20644806435086015846702923)
          ·
            refine ⟨30967209652629023770054385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20644806435086015846702923 30967209652629023770054385)
            ·
              refine ⟨23225407239471767827540789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30967209652629023770054385 23225407239471767827540789)
              ·
                refine ⟨2177381928700478233831949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23225407239471767827540789 2177381928700478233831949)
                ·
                  refine ⟨816518223262679337686981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2177381928700478233831949 816518223262679337686981)
                  ·
                    refine ⟨153097166861752375816309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 816518223262679337686981 153097166861752375816309)
                    ·
                      rfl

theorem cell23_894467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 3, 4].length) (baseStart_894467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894467 prefixEnd_894467 := by exact prefixLift 894467
  have htrace : WordTrace (prefixWord ++ tailWord_894467) baseStart_894467 baseEnd_894467 := by
    simpa [prefixWord, tailWord_894467, baseEnd_894467] using wordTrace_append hprefix tailTrace_894467
  have hstable : (prefixWord ++ tailWord_894467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894467).length < 2 ^ (prefixWord ++ tailWord_894467).sum := by decide
  have hdescent : baseEnd_894467 < baseStart_894467 := by decide
  rcases family_descends (prefixWord ++ tailWord_894467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894527 : List Nat := [1, 1, 2, 2, 3, 3, 1, 2, 3, 5]
def baseStart_894527 : Nat := 118140960795 + 894527 * 2 ^ 59
def prefixEnd_894527 : Nat := 4983230072969 + 3 ^ 40 * 894527 * 2
def baseEnd_894527 : Nat := 153107436474842297566217

theorem tailTrace_894527 : CollatzResearch.WordTrace tailWord_894527 prefixEnd_894527 153107436474842297566217 := by
  unfold tailWord_894527
  simp only [CollatzResearch.WordTrace]
  refine ⟨32626080030288926893825835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21750720020192617929217223 32626080030288926893825835)
  ·
    refine ⟨48939120045433390340738753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32626080030288926893825835 48939120045433390340738753)
    ·
      refine ⟨36704340034075042755554065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48939120045433390340738753 36704340034075042755554065)
      ·
        refine ⟨27528255025556282066665549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36704340034075042755554065 27528255025556282066665549)
        ·
          refine ⟨10323095634583605774999581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27528255025556282066665549 10323095634583605774999581)
          ·
            refine ⟨3871160862968852165624843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10323095634583605774999581 3871160862968852165624843)
            ·
              refine ⟨5806741294453278248437265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3871160862968852165624843 5806741294453278248437265)
              ·
                refine ⟨4355055970839958686327949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5806741294453278248437265 4355055970839958686327949)
                ·
                  refine ⟨1633145989064984507372981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4355055970839958686327949 1633145989064984507372981)
                  ·
                    refine ⟨153107436474842297566217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1633145989064984507372981 153107436474842297566217)
                    ·
                      rfl

theorem cell23_894527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 5].length) (baseStart_894527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894527 prefixEnd_894527 := by exact prefixLift 894527
  have htrace : WordTrace (prefixWord ++ tailWord_894527) baseStart_894527 baseEnd_894527 := by
    simpa [prefixWord, tailWord_894527, baseEnd_894527] using wordTrace_append hprefix tailTrace_894527
  have hstable : (prefixWord ++ tailWord_894527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894527).length < 2 ^ (prefixWord ++ tailWord_894527).sum := by decide
  have hdescent : baseEnd_894527 < baseStart_894527 := by decide
  rcases family_descends (prefixWord ++ tailWord_894527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894551 : List Nat := [1, 1, 3, 2, 2, 3, 3, 1, 2, 3, 2]
def baseStart_894551 : Nat := 118140960795 + 894551 * 2 ^ 59
def prefixEnd_894551 : Nat := 4983230072969 + 3 ^ 40 * 894551 * 2
def baseEnd_894551 : Nat := 459334632960234798798541

theorem tailTrace_894551 : CollatzResearch.WordTrace tailWord_894551 prefixEnd_894551 459334632960234798798541 := by
  unfold tailWord_894551
  simp only [CollatzResearch.WordTrace]
  refine ⟨32626955382201978992699507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21751303588134652661799671 32626955382201978992699507)
  ·
    refine ⟨48940433073302968489049261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32626955382201978992699507 48940433073302968489049261)
    ·
      refine ⟨18352662402488613183393473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48940433073302968489049261 18352662402488613183393473)
      ·
        refine ⟨13764496801866459887545105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18352662402488613183393473 13764496801866459887545105)
        ·
          refine ⟨10323372601399844915658829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13764496801866459887545105 10323372601399844915658829)
          ·
            refine ⟨3871264725524941843372061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10323372601399844915658829 3871264725524941843372061)
            ·
              refine ⟨1451724272071853191264523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3871264725524941843372061 1451724272071853191264523)
              ·
                refine ⟨2177586408107779786896785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1451724272071853191264523 2177586408107779786896785)
                ·
                  refine ⟨1633189806080834840172589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2177586408107779786896785 1633189806080834840172589)
                  ·
                    refine ⟨612446177280313065064721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1633189806080834840172589 612446177280313065064721)
                    ·
                      refine ⟨459334632960234798798541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 612446177280313065064721 459334632960234798798541)
                      ·
                        rfl

theorem cell23_894551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 3, 2].length) (baseStart_894551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894551 prefixEnd_894551 := by exact prefixLift 894551
  have htrace : WordTrace (prefixWord ++ tailWord_894551) baseStart_894551 baseEnd_894551 := by
    simpa [prefixWord, tailWord_894551, baseEnd_894551] using wordTrace_append hprefix tailTrace_894551
  have hstable : (prefixWord ++ tailWord_894551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894551).length < 2 ^ (prefixWord ++ tailWord_894551).sum := by decide
  have hdescent : baseEnd_894551 < baseStart_894551 := by decide
  rcases family_descends (prefixWord ++ tailWord_894551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894577 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 3, 2, 4]
def baseStart_894577 : Nat := 118140960795 + 894577 * 2 ^ 59
def prefixEnd_894577 : Nat := 4983230072969 + 3 ^ 40 * 894577 * 2
def baseEnd_894577 : Nat := 459347983457251697073421

theorem tailTrace_894577 : CollatzResearch.WordTrace tailWord_894577 prefixEnd_894577 459347983457251697073421 := by
  unfold tailWord_894577
  simp only [CollatzResearch.WordTrace]
  refine ⟨32627903680107785433145985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21751935786738523622097323 32627903680107785433145985)
  ·
    refine ⟨24470927760080839074859489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32627903680107785433145985 24470927760080839074859489)
    ·
      refine ⟨18353195820060629306144617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24470927760080839074859489 18353195820060629306144617)
      ·
        refine ⟨13764896865045471979608463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18353195820060629306144617 13764896865045471979608463)
        ·
          refine ⟨20647345297568207969412695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13764896865045471979608463 20647345297568207969412695)
          ·
            refine ⟨30971017946352311954119043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20647345297568207969412695 30971017946352311954119043)
            ·
              refine ⟨46456526919528467931178565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30971017946352311954119043 46456526919528467931178565)
              ·
                refine ⟨8710598797411587737095981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46456526919528467931178565 8710598797411587737095981)
                ·
                  refine ⟨3266474549029345401410993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8710598797411587737095981 3266474549029345401410993)
                  ·
                    refine ⟨2449855911772009051058245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3266474549029345401410993 2449855911772009051058245)
                    ·
                      refine ⟨459347983457251697073421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2449855911772009051058245 459347983457251697073421)
                      ·
                        rfl

theorem cell23_894577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_894577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894577 prefixEnd_894577 := by exact prefixLift 894577
  have htrace : WordTrace (prefixWord ++ tailWord_894577) baseStart_894577 baseEnd_894577 := by
    simpa [prefixWord, tailWord_894577, baseEnd_894577] using wordTrace_append hprefix tailTrace_894577
  have hstable : (prefixWord ++ tailWord_894577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894577).length < 2 ^ (prefixWord ++ tailWord_894577).sum := by decide
  have hdescent : baseEnd_894577 < baseStart_894577 := by decide
  rcases family_descends (prefixWord ++ tailWord_894577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894615 : List Nat := [1, 1, 3, 3, 2, 2, 3, 3, 1, 2, 2]
def baseStart_894615 : Nat := 118140960795 + 894615 * 2 ^ 59
def prefixEnd_894615 : Nat := 4983230072969 + 3 ^ 40 * 894615 * 2
def baseEnd_894615 : Nat := 459367495722122548398247

theorem tailTrace_894615 : CollatzResearch.WordTrace tailWord_894615 prefixEnd_894615 459367495722122548398247 := by
  unfold tailWord_894615
  simp only [CollatzResearch.WordTrace]
  refine ⟨32629289653970117923029299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21752859769313411948686199 32629289653970117923029299)
  ·
    refine ⟨48943934480955176884543949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32629289653970117923029299 48943934480955176884543949)
    ·
      refine ⟨18353975430358191331703981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48943934480955176884543949 18353975430358191331703981)
      ·
        refine ⟨6882740786384321749388993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18353975430358191331703981 6882740786384321749388993)
        ·
          refine ⟨5162055589788241312041745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6882740786384321749388993 5162055589788241312041745)
          ·
            refine ⟨3871541692341180984031309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5162055589788241312041745 3871541692341180984031309)
            ·
              refine ⟨1451828134627942869011741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3871541692341180984031309 1451828134627942869011741)
              ·
                refine ⟨544435550485478575879403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1451828134627942869011741 544435550485478575879403)
                ·
                  refine ⟨816653325728217863819105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 544435550485478575879403 816653325728217863819105)
                  ·
                    refine ⟨612489994296163397864329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 816653325728217863819105 612489994296163397864329)
                    ·
                      refine ⟨459367495722122548398247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 612489994296163397864329 459367495722122548398247)
                      ·
                        rfl

theorem cell23_894615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_894615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894615 prefixEnd_894615 := by exact prefixLift 894615
  have htrace : WordTrace (prefixWord ++ tailWord_894615) baseStart_894615 baseEnd_894615 := by
    simpa [prefixWord, tailWord_894615, baseEnd_894615] using wordTrace_append hprefix tailTrace_894615
  have hstable : (prefixWord ++ tailWord_894615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894615).length < 2 ^ (prefixWord ++ tailWord_894615).sum := by decide
  have hdescent : baseEnd_894615 < baseStart_894615 := by decide
  rcases family_descends (prefixWord ++ tailWord_894615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894627 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 5]
def baseStart_894627 : Nat := 118140960795 + 894627 * 2 ^ 59
def prefixEnd_894627 : Nat := 4983230072969 + 3 ^ 40 * 894627 * 2
def baseEnd_894627 : Nat := 459373657489976501448191

theorem tailTrace_894627 : CollatzResearch.WordTrace tailWord_894627 prefixEnd_894627 459373657489976501448191 := by
  unfold tailWord_894627
  simp only [CollatzResearch.WordTrace]
  refine ⟨32629727329926643972466135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21753151553284429314977423 32629727329926643972466135)
  ·
    refine ⟨48944590994889965958699203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32629727329926643972466135 48944590994889965958699203)
    ·
      refine ⟨73416886492334948938048805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48944590994889965958699203 73416886492334948938048805)
      ·
        refine ⟨13765666217312802925884151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73416886492334948938048805 13765666217312802925884151)
        ·
          refine ⟨20648499325969204388826227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13765666217312802925884151 20648499325969204388826227)
          ·
            refine ⟨30972748988953806583239341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20648499325969204388826227 30972748988953806583239341)
            ·
              refine ⟨11614780870857677468714753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30972748988953806583239341 11614780870857677468714753)
              ·
                refine ⟨8711085653143258101536065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11614780870857677468714753 8711085653143258101536065)
                ·
                  refine ⟨6533314239857443576152049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8711085653143258101536065 6533314239857443576152049)
                  ·
                    refine ⟨4899985679893082682114037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6533314239857443576152049 4899985679893082682114037)
                    ·
                      refine ⟨459373657489976501448191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4899985679893082682114037 459373657489976501448191)
                      ·
                        rfl

theorem cell23_894627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_894627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894627 prefixEnd_894627 := by exact prefixLift 894627
  have htrace : WordTrace (prefixWord ++ tailWord_894627) baseStart_894627 baseEnd_894627 := by
    simpa [prefixWord, tailWord_894627, baseEnd_894627] using wordTrace_append hprefix tailTrace_894627
  have hstable : (prefixWord ++ tailWord_894627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894627).length < 2 ^ (prefixWord ++ tailWord_894627).sum := by decide
  have hdescent : baseEnd_894627 < baseStart_894627 := by decide
  rcases family_descends (prefixWord ++ tailWord_894627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894671 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 6, 2, 2]
def baseStart_894671 : Nat := 118140960795 + 894671 * 2 ^ 59
def prefixEnd_894671 : Nat := 4983230072969 + 3 ^ 40 * 894671 * 2
def baseEnd_894671 : Nat := 459396250638774329297989

theorem tailTrace_894671 : CollatzResearch.WordTrace tailWord_894671 prefixEnd_894671 459396250638774329297989 := by
  unfold tailWord_894671
  simp only [CollatzResearch.WordTrace]
  refine ⟨32631332141767239487067867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21754221427844826324711911 32631332141767239487067867)
  ·
    refine ⟨48946998212650859230601801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32631332141767239487067867 48946998212650859230601801)
    ·
      refine ⟨36710248659488144422951351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48946998212650859230601801 36710248659488144422951351)
      ·
        refine ⟨55065372989232216634427027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36710248659488144422951351 55065372989232216634427027)
        ·
          refine ⟨82598059483848324951640541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55065372989232216634427027 82598059483848324951640541)
          ·
            refine ⟨30974272306443121856865203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82598059483848324951640541 30974272306443121856865203)
            ·
              refine ⟨46461408459664682785297805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30974272306443121856865203 46461408459664682785297805)
              ·
                refine ⟨17423028172374256044486677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46461408459664682785297805 17423028172374256044486677)
                ·
                  refine ⟨816704445580043252085313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17423028172374256044486677 816704445580043252085313)
                  ·
                    refine ⟨612528334185032439063985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 816704445580043252085313 612528334185032439063985)
                    ·
                      refine ⟨459396250638774329297989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 612528334185032439063985 459396250638774329297989)
                      ·
                        rfl

theorem cell23_894671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 6, 2, 2].length) (baseStart_894671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894671 prefixEnd_894671 := by exact prefixLift 894671
  have htrace : WordTrace (prefixWord ++ tailWord_894671) baseStart_894671 baseEnd_894671 := by
    simpa [prefixWord, tailWord_894671, baseEnd_894671] using wordTrace_append hprefix tailTrace_894671
  have hstable : (prefixWord ++ tailWord_894671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894671).length < 2 ^ (prefixWord ++ tailWord_894671).sum := by decide
  have hdescent : baseEnd_894671 < baseStart_894671 := by decide
  rcases family_descends (prefixWord ++ tailWord_894671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894688 : List Nat := [2, 1, 1, 3, 1, 2, 3, 4, 2, 2, 2]
def baseStart_894688 : Nat := 118140960795 + 894688 * 2 ^ 59
def prefixEnd_894688 : Nat := 4983230072969 + 3 ^ 40 * 894688 * 2
def baseEnd_894688 : Nat := 459404979809900762785411

theorem tailTrace_894688 : CollatzResearch.WordTrace tailWord_894688 prefixEnd_894688 459404979809900762785411 := by
  unfold tailWord_894688
  simp only [CollatzResearch.WordTrace]
  refine ⟨16315976091352825695218359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21754634788470434260291145 16315976091352825695218359)
  ·
    refine ⟨24473964137029238542827539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16315976091352825695218359 24473964137029238542827539)
    ·
      refine ⟨36710946205543857814241309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24473964137029238542827539 36710946205543857814241309)
      ·
        refine ⟨13766604827078946680340491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36710946205543857814241309 13766604827078946680340491)
        ·
          refine ⟨20649907240618420020510737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13766604827078946680340491 20649907240618420020510737)
          ·
            refine ⟨15487430430463815015383053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20649907240618420020510737 15487430430463815015383053)
            ·
              refine ⟨5807786411423930630768645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15487430430463815015383053 5807786411423930630768645)
              ·
                refine ⟨1088959952141986993269121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5807786411423930630768645 1088959952141986993269121)
                ·
                  refine ⟨816719964106490244951841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1088959952141986993269121 816719964106490244951841)
                  ·
                    refine ⟨612539973079867683713881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 816719964106490244951841 612539973079867683713881)
                    ·
                      refine ⟨459404979809900762785411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 612539973079867683713881 459404979809900762785411)
                      ·
                        rfl

theorem cell23_894688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 2, 2, 2].length) (baseStart_894688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894688 prefixEnd_894688 := by exact prefixLift 894688
  have htrace : WordTrace (prefixWord ++ tailWord_894688) baseStart_894688 baseEnd_894688 := by
    simpa [prefixWord, tailWord_894688, baseEnd_894688] using wordTrace_append hprefix tailTrace_894688
  have hstable : (prefixWord ++ tailWord_894688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894688).length < 2 ^ (prefixWord ++ tailWord_894688).sum := by decide
  have hdescent : baseEnd_894688 < baseStart_894688 := by decide
  rcases family_descends (prefixWord ++ tailWord_894688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894697 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 8]
def baseStart_894697 : Nat := 118140960795 + 894697 * 2 ^ 59
def prefixEnd_894697 : Nat := 4983230072969 + 3 ^ 40 * 894697 * 2
def baseEnd_894697 : Nat := 459409601135791227572869

theorem tailTrace_894697 : CollatzResearch.WordTrace tailWord_894697 prefixEnd_894697 459409601135791227572869 := by
  unfold tailWord_894697
  simp only [CollatzResearch.WordTrace]
  refine ⟨32632280439673045927514345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21754853626448697285009563 32632280439673045927514345)
  ·
    refine ⟨24474210329754784445635759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32632280439673045927514345 24474210329754784445635759)
    ·
      refine ⟨36711315494632176668453639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24474210329754784445635759 36711315494632176668453639)
      ·
        refine ⟨55066973241948265002680459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36711315494632176668453639 55066973241948265002680459)
        ·
          refine ⟨82600459862922397504020689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55066973241948265002680459 82600459862922397504020689)
          ·
            refine ⟨61950344897191798128015517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82600459862922397504020689 61950344897191798128015517)
            ·
              refine ⟨23231379336446924298005819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61950344897191798128015517 23231379336446924298005819)
              ·
                refine ⟨34847069004670386447008729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23231379336446924298005819 34847069004670386447008729)
                ·
                  refine ⟨26135301753502789835256547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34847069004670386447008729 26135301753502789835256547)
                  ·
                    refine ⟨39202952630254184752884821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26135301753502789835256547 39202952630254184752884821)
                    ·
                      refine ⟨459409601135791227572869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 39202952630254184752884821 459409601135791227572869)
                      ·
                        rfl

theorem cell23_894697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 8].length) (baseStart_894697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894697 prefixEnd_894697 := by exact prefixLift 894697
  have htrace : WordTrace (prefixWord ++ tailWord_894697) baseStart_894697 baseEnd_894697 := by
    simpa [prefixWord, tailWord_894697, baseEnd_894697] using wordTrace_append hprefix tailTrace_894697
  have hstable : (prefixWord ++ tailWord_894697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894697).length < 2 ^ (prefixWord ++ tailWord_894697).sum := by decide
  have hdescent : baseEnd_894697 < baseStart_894697 := by decide
  rcases family_descends (prefixWord ++ tailWord_894697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894701 : List Nat := [1, 5, 1, 2, 1, 3, 1, 1, 2, 2, 4]
def baseStart_894701 : Nat := 118140960795 + 894701 * 2 ^ 59
def prefixEnd_894701 : Nat := 4983230072969 + 3 ^ 40 * 894701 * 2
def baseEnd_894701 : Nat := 459411655058409211922851

theorem tailTrace_894701 : CollatzResearch.WordTrace tailWord_894701 prefixEnd_894701 459411655058409211922851 := by
  unfold tailWord_894701
  simp only [CollatzResearch.WordTrace]
  refine ⟨32632426331658554610659957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21754950887772369740439971 32632426331658554610659957)
  ·
    refine ⟨3059289968592989494749371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32632426331658554610659957 3059289968592989494749371)
    ·
      refine ⟨4588934952889484242124057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3059289968592989494749371 4588934952889484242124057)
      ·
        refine ⟨3441701214667113181593043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4588934952889484242124057 3441701214667113181593043)
        ·
          refine ⟨5162551822000669772389565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3441701214667113181593043 5162551822000669772389565)
          ·
            refine ⟨1935956933250251164646087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5162551822000669772389565 1935956933250251164646087)
            ·
              refine ⟨2903935399875376746969131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1935956933250251164646087 2903935399875376746969131)
              ·
                refine ⟨4355903099813065120453697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2903935399875376746969131 4355903099813065120453697)
                ·
                  refine ⟨3266927324859798840340273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4355903099813065120453697 3266927324859798840340273)
                  ·
                    refine ⟨2450195493644849130255205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3266927324859798840340273 2450195493644849130255205)
                    ·
                      refine ⟨459411655058409211922851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2450195493644849130255205 459411655058409211922851)
                      ·
                        rfl

theorem cell23_894701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_894701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894701 prefixEnd_894701 := by exact prefixLift 894701
  have htrace : WordTrace (prefixWord ++ tailWord_894701) baseStart_894701 baseEnd_894701 := by
    simpa [prefixWord, tailWord_894701, baseEnd_894701] using wordTrace_append hprefix tailTrace_894701
  have hstable : (prefixWord ++ tailWord_894701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894701).length < 2 ^ (prefixWord ++ tailWord_894701).sum := by decide
  have hdescent : baseEnd_894701 < baseStart_894701 := by decide
  rcases family_descends (prefixWord ++ tailWord_894701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894733 : List Nat := [1, 7, 2, 1, 2, 1, 1, 2, 2, 1, 3]
def baseStart_894733 : Nat := 118140960795 + 894733 * 2 ^ 59
def prefixEnd_894733 : Nat := 4983230072969 + 3 ^ 40 * 894733 * 2
def baseEnd_894733 : Nat := 459428086439353086722705

theorem tailTrace_894733 : CollatzResearch.WordTrace tailWord_894733 prefixEnd_894733 459428086439353086722705 := by
  unfold tailWord_894733
  simp only [CollatzResearch.WordTrace]
  refine ⟨32633593467542624075824853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21755728978361749383883235 32633593467542624075824853)
  ·
    refine ⟨764849846895530251777145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 32633593467542624075824853 764849846895530251777145)
    ·
      refine ⟨573637385171647688832859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 764849846895530251777145 573637385171647688832859)
      ·
        refine ⟨860456077757471533249289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573637385171647688832859 860456077757471533249289)
        ·
          refine ⟨645342058318103649936967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 860456077757471533249289 645342058318103649936967)
          ·
            refine ⟨968013087477155474905451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645342058318103649936967 968013087477155474905451)
            ·
              refine ⟨1452019631215733212358177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 968013087477155474905451 1452019631215733212358177)
              ·
                refine ⟨1089014723411799909268633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1452019631215733212358177 1089014723411799909268633)
                ·
                  refine ⟨816761042558849931951475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1089014723411799909268633 816761042558849931951475)
                  ·
                    refine ⟨1225141563838274897927213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 816761042558849931951475 1225141563838274897927213)
                    ·
                      refine ⟨459428086439353086722705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1225141563838274897927213 459428086439353086722705)
                      ·
                        rfl

theorem cell23_894733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_894733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894733 prefixEnd_894733 := by exact prefixLift 894733
  have htrace : WordTrace (prefixWord ++ tailWord_894733) baseStart_894733 baseEnd_894733 := by
    simpa [prefixWord, tailWord_894733, baseEnd_894733] using wordTrace_append hprefix tailTrace_894733
  have hstable : (prefixWord ++ tailWord_894733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894733).length < 2 ^ (prefixWord ++ tailWord_894733).sum := by decide
  have hdescent : baseEnd_894733 < baseStart_894733 := by decide
  rcases family_descends (prefixWord ++ tailWord_894733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894734 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5]
def baseStart_894734 : Nat := 118140960795 + 894734 * 2 ^ 59
def prefixEnd_894734 : Nat := 4983230072969 + 3 ^ 40 * 894734 * 2
def baseEnd_894734 : Nat := 459428599920007582810199

theorem tailTrace_894734 : CollatzResearch.WordTrace tailWord_894734 prefixEnd_894734 459428599920007582810199 := by
  unfold tailWord_894734
  simp only [CollatzResearch.WordTrace]
  refine ⟨4079203742567375155826407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21755753293692667497740837 4079203742567375155826407)
  ·
    refine ⟨6118805613851062733739611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4079203742567375155826407 6118805613851062733739611)
    ·
      refine ⟨9178208420776594100609417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6118805613851062733739611 9178208420776594100609417)
      ·
        refine ⟨6883656315582445575457063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9178208420776594100609417 6883656315582445575457063)
        ·
          refine ⟨10325484473373668363185595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6883656315582445575457063 10325484473373668363185595)
          ·
            refine ⟨15488226710060502544778393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10325484473373668363185595 15488226710060502544778393)
            ·
              refine ⟨11616170032545376908583795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15488226710060502544778393 11616170032545376908583795)
              ·
                refine ⟨17424255048818065362875693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11616170032545376908583795 17424255048818065362875693)
                ·
                  refine ⟨6534095643306774511078385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17424255048818065362875693 6534095643306774511078385)
                  ·
                    refine ⟨4900571732480080883308789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6534095643306774511078385 4900571732480080883308789)
                    ·
                      refine ⟨459428599920007582810199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4900571732480080883308789 459428599920007582810199)
                      ·
                        rfl

theorem cell23_894734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_894734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894734 prefixEnd_894734 := by exact prefixLift 894734
  have htrace : WordTrace (prefixWord ++ tailWord_894734) baseStart_894734 baseEnd_894734 := by
    simpa [prefixWord, tailWord_894734, baseEnd_894734] using wordTrace_append hprefix tailTrace_894734
  have hstable : (prefixWord ++ tailWord_894734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894734).length < 2 ^ (prefixWord ++ tailWord_894734).sum := by decide
  have hdescent : baseEnd_894734 < baseStart_894734 := by decide
  rcases family_descends (prefixWord ++ tailWord_894734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894738 : List Nat := [3, 2, 4, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_894738 : Nat := 118140960795 + 894738 * 2 ^ 59
def prefixEnd_894738 : Nat := 4983230072969 + 3 ^ 40 * 894738 * 2
def baseEnd_894738 : Nat := 459430653842625567160181

theorem tailTrace_894738 : CollatzResearch.WordTrace tailWord_894738 prefixEnd_894738 459430653842625567160181 := by
  unfold tailWord_894738
  simp only [CollatzResearch.WordTrace]
  refine ⟨8158443958131127482439217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21755850555016339953171245 8158443958131127482439217)
  ·
    refine ⟨6118832968598345611829413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8158443958131127482439217 6118832968598345611829413)
    ·
      refine ⟨1147281181612189802218015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6118832968598345611829413 1147281181612189802218015)
      ·
        refine ⟨1720921772418284703327023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1147281181612189802218015 1720921772418284703327023)
        ·
          refine ⟨2581382658627427054990535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1720921772418284703327023 2581382658627427054990535)
          ·
            refine ⟨3872073987941140582485803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2581382658627427054990535 3872073987941140582485803)
            ·
              refine ⟨5808110981911710873728705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3872073987941140582485803 5808110981911710873728705)
              ·
                refine ⟨4356083236433783155296529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5808110981911710873728705 4356083236433783155296529)
                ·
                  refine ⟨3267062427325337366472397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4356083236433783155296529 3267062427325337366472397)
                  ·
                    refine ⟨1225148410247001512427149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3267062427325337366472397 1225148410247001512427149)
                    ·
                      refine ⟨459430653842625567160181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1225148410247001512427149 459430653842625567160181)
                      ·
                        rfl

theorem cell23_894738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_894738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894738 prefixEnd_894738 := by exact prefixLift 894738
  have htrace : WordTrace (prefixWord ++ tailWord_894738) baseStart_894738 baseEnd_894738 := by
    simpa [prefixWord, tailWord_894738, baseEnd_894738] using wordTrace_append hprefix tailTrace_894738
  have hstable : (prefixWord ++ tailWord_894738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894738).length < 2 ^ (prefixWord ++ tailWord_894738).sum := by decide
  have hdescent : baseEnd_894738 < baseStart_894738 := by decide
  rcases family_descends (prefixWord ++ tailWord_894738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894818 : List Nat := [3, 3, 2, 1, 2, 2, 1, 3, 6]
def baseStart_894818 : Nat := 118140960795 + 894818 * 2 ^ 59
def prefixEnd_894818 : Nat := 4983230072969 + 3 ^ 40 * 894818 * 2
def baseEnd_894818 : Nat := 51052414699442806017757

theorem tailTrace_894818 : CollatzResearch.WordTrace tailWord_894818 prefixEnd_894818 51052414699442806017757 := by
  unfold tailWord_894818
  simp only [CollatzResearch.WordTrace]
  refine ⟨8159173418058670898167277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21757795781489789061779405 8159173418058670898167277)
  ·
    refine ⟨3059690031772001586812729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8159173418058670898167277 3059690031772001586812729)
    ·
      refine ⟨2294767523829001190109547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3059690031772001586812729 2294767523829001190109547)
      ·
        refine ⟨3442151285743501785164321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2294767523829001190109547 3442151285743501785164321)
        ·
          refine ⟨2581613464307626338873241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3442151285743501785164321 2581613464307626338873241)
          ·
            refine ⟨1936210098230719754154931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2581613464307626338873241 1936210098230719754154931)
            ·
              refine ⟨2904315147346079631232397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1936210098230719754154931 2904315147346079631232397)
              ·
                refine ⟨1089118180254779861712149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2904315147346079631232397 1089118180254779861712149)
                ·
                  refine ⟨51052414699442806017757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1089118180254779861712149 51052414699442806017757)
                  ·
                    rfl

theorem cell23_894818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_894818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894818 prefixEnd_894818 := by exact prefixLift 894818
  have htrace : WordTrace (prefixWord ++ tailWord_894818) baseStart_894818 baseEnd_894818 := by
    simpa [prefixWord, tailWord_894818, baseEnd_894818] using wordTrace_append hprefix tailTrace_894818
  have hstable : (prefixWord ++ tailWord_894818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894818).length < 2 ^ (prefixWord ++ tailWord_894818).sum := by decide
  have hdescent : baseEnd_894818 < baseStart_894818 := by decide
  rcases family_descends (prefixWord ++ tailWord_894818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894845 : List Nat := [1, 4, 1, 1, 2, 1, 1, 7, 1, 1, 3]
def baseStart_894845 : Nat := 118140960795 + 894845 * 2 ^ 59
def prefixEnd_894845 : Nat := 4983230072969 + 3 ^ 40 * 894845 * 2
def baseEnd_894845 : Nat := 459485596272656648522189

theorem tailTrace_894845 : CollatzResearch.WordTrace tailWord_894845 prefixEnd_894845 459485596272656648522189 := by
  unfold tailWord_894845
  simp only [CollatzResearch.WordTrace]
  refine ⟨32637678443136867203901989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21758452295424578135934659 32637678443136867203901989)
  ·
    refine ⟨6119564708088162600731623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32637678443136867203901989 6119564708088162600731623)
    ·
      refine ⟨9179347062132243901097435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6119564708088162600731623 9179347062132243901097435)
      ·
        refine ⟨13769020593198365851646153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9179347062132243901097435 13769020593198365851646153)
        ·
          refine ⟨10326765444898774388734615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13769020593198365851646153 10326765444898774388734615)
          ·
            refine ⟨15490148167348161583101923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10326765444898774388734615 15490148167348161583101923)
            ·
              refine ⟨23235222251022242374652885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15490148167348161583101923 23235222251022242374652885)
              ·
                refine ⟨544575521508333805655927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 23235222251022242374652885 544575521508333805655927)
                ·
                  refine ⟨816863282262500708483891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 544575521508333805655927 816863282262500708483891)
                  ·
                    refine ⟨1225294923393751062725837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 816863282262500708483891 1225294923393751062725837)
                    ·
                      refine ⟨459485596272656648522189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1225294923393751062725837 459485596272656648522189)
                      ·
                        rfl

theorem cell23_894845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 7, 1, 1, 3].length) (baseStart_894845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894845 prefixEnd_894845 := by exact prefixLift 894845
  have htrace : WordTrace (prefixWord ++ tailWord_894845) baseStart_894845 baseEnd_894845 := by
    simpa [prefixWord, tailWord_894845, baseEnd_894845] using wordTrace_append hprefix tailTrace_894845
  have hstable : (prefixWord ++ tailWord_894845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894845).length < 2 ^ (prefixWord ++ tailWord_894845).sum := by decide
  have hdescent : baseEnd_894845 < baseStart_894845 := by decide
  rcases family_descends (prefixWord ++ tailWord_894845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894848 : List Nat := [2, 1, 1, 2, 1, 2, 7, 1, 1, 5]
def baseStart_894848 : Nat := 118140960795 + 894848 * 2 ^ 59
def prefixEnd_894848 : Nat := 4983230072969 + 3 ^ 40 * 894848 * 2
def baseEnd_894848 : Nat := 153162378904873378928225

theorem tailTrace_894848 : CollatzResearch.WordTrace tailWord_894848 prefixEnd_894848 153162378904873378928225 := by
  unfold tailWord_894848
  simp only [CollatzResearch.WordTrace]
  refine ⟨16318893931062999358130599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21758525241417332477507465 16318893931062999358130599)
  ·
    refine ⟨24478340896594499037195899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16318893931062999358130599 24478340896594499037195899)
    ·
      refine ⟨36717511344891748555793849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24478340896594499037195899 36717511344891748555793849)
      ·
        refine ⟨27538133508668811416845387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36717511344891748555793849 27538133508668811416845387)
        ·
          refine ⟨41307200263003217125268081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27538133508668811416845387 41307200263003217125268081)
          ·
            refine ⟨30980400197252412843951061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41307200263003217125268081 30980400197252412843951061)
            ·
              refine ⟨726103129623103426030103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 30980400197252412843951061 726103129623103426030103)
              ·
                refine ⟨1089154694434655139045155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 726103129623103426030103 1089154694434655139045155)
                ·
                  refine ⟨1633732041651982708567733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1089154694434655139045155 1633732041651982708567733)
                  ·
                    refine ⟨153162378904873378928225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1633732041651982708567733 153162378904873378928225)
                    ·
                      rfl

theorem cell23_894848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 1, 5].length) (baseStart_894848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894848 prefixEnd_894848 := by exact prefixLift 894848
  have htrace : WordTrace (prefixWord ++ tailWord_894848) baseStart_894848 baseEnd_894848 := by
    simpa [prefixWord, tailWord_894848, baseEnd_894848] using wordTrace_append hprefix tailTrace_894848
  have hstable : (prefixWord ++ tailWord_894848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894848).length < 2 ^ (prefixWord ++ tailWord_894848).sum := by decide
  have hdescent : baseEnd_894848 < baseStart_894848 := by decide
  rcases family_descends (prefixWord ++ tailWord_894848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894868 : List Nat := [2, 4, 2, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_894868 : Nat := 118140960795 + 894868 * 2 ^ 59
def prefixEnd_894868 : Nat := 4983230072969 + 3 ^ 40 * 894868 * 2
def baseEnd_894868 : Nat := 459497406327710058534583

theorem tailTrace_894868 : CollatzResearch.WordTrace tailWord_894868 prefixEnd_894868 459497406327710058534583 := by
  unfold tailWord_894868
  simp only [CollatzResearch.WordTrace]
  refine ⟨16319258661026771065994629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21759011548035694754659505 16319258661026771065994629)
  ·
    refine ⟨3059860998942519574873993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16319258661026771065994629 3059860998942519574873993)
    ·
      refine ⟨2294895749206889681155495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3059860998942519574873993 2294895749206889681155495)
      ·
        refine ⟨3442343623810334521733243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2294895749206889681155495 3442343623810334521733243)
        ·
          refine ⟨5163515435715501782599865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3442343623810334521733243 5163515435715501782599865)
          ·
            refine ⟨3872636576786626336949899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5163515435715501782599865 3872636576786626336949899)
            ·
              refine ⟨5808954865179939505424849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3872636576786626336949899 5808954865179939505424849)
              ·
                refine ⟨4356716148884954629068637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5808954865179939505424849 4356716148884954629068637)
                ·
                  refine ⟨1633768555831857985900739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4356716148884954629068637 1633768555831857985900739)
                  ·
                    refine ⟨2450652833747786978851109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1633768555831857985900739 2450652833747786978851109)
                    ·
                      refine ⟨459497406327710058534583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2450652833747786978851109 459497406327710058534583)
                      ·
                        rfl

theorem cell23_894868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_894868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894868 prefixEnd_894868 := by exact prefixLift 894868
  have htrace : WordTrace (prefixWord ++ tailWord_894868) baseStart_894868 baseEnd_894868 := by
    simpa [prefixWord, tailWord_894868, baseEnd_894868] using wordTrace_append hprefix tailTrace_894868
  have hstable : (prefixWord ++ tailWord_894868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894868).length < 2 ^ (prefixWord ++ tailWord_894868).sum := by decide
  have hdescent : baseEnd_894868 < baseStart_894868 := by decide
  rcases family_descends (prefixWord ++ tailWord_894868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894908 : List Nat := [2, 2, 2, 5, 1, 1, 10]
def baseStart_894908 : Nat := 118140960795 + 894908 * 2 ^ 59
def prefixEnd_894908 : Nat := 4983230072969 + 3 ^ 40 * 894908 * 2
def baseEnd_894908 : Nat := 5673061056220862988079

theorem tailTrace_894908 : CollatzResearch.WordTrace tailWord_894908 prefixEnd_894908 5673061056220862988079 := by
  unfold tailWord_894908
  simp only [CollatzResearch.WordTrace]
  refine ⟨16319988120954314481722689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21759984161272419308963585 16319988120954314481722689)
  ·
    refine ⟨12239991090715735861292017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16319988120954314481722689 12239991090715735861292017)
    ·
      refine ⟨9179993318036801895969013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12239991090715735861292017 9179993318036801895969013)
      ·
        refine ⟨860624373565950177747095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9179993318036801895969013 860624373565950177747095)
        ·
          refine ⟨1290936560348925266620643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860624373565950177747095 1290936560348925266620643)
          ·
            refine ⟨1936404840523387899930965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1290936560348925266620643 1936404840523387899930965)
            ·
              refine ⟨5673061056220862988079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1936404840523387899930965 5673061056220862988079)
              ·
                rfl

theorem cell23_894908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 10].length) (baseStart_894908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894908 prefixEnd_894908 := by exact prefixLift 894908
  have htrace : WordTrace (prefixWord ++ tailWord_894908) baseStart_894908 baseEnd_894908 := by
    simpa [prefixWord, tailWord_894908, baseEnd_894908] using wordTrace_append hprefix tailTrace_894908
  have hstable : (prefixWord ++ tailWord_894908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894908).length < 2 ^ (prefixWord ++ tailWord_894908).sum := by decide
  have hdescent : baseEnd_894908 < baseStart_894908 := by decide
  rcases family_descends (prefixWord ++ tailWord_894908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894928 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 5, 3, 2]
def baseStart_894928 : Nat := 118140960795 + 894928 * 2 ^ 59
def prefixEnd_894928 : Nat := 4983230072969 + 3 ^ 40 * 894928 * 2
def baseEnd_894928 : Nat := 459528215166979823784307

theorem tailTrace_894928 : CollatzResearch.WordTrace tailWord_894928 prefixEnd_894928 459528215166979823784307 := by
  unfold tailWord_894928
  simp only [CollatzResearch.WordTrace]
  refine ⟨16320352850918086189586719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21760470467890781586115625 16320352850918086189586719)
  ·
    refine ⟨24480529276377129284380079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16320352850918086189586719 24480529276377129284380079)
    ·
      refine ⟨36720793914565693926570119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24480529276377129284380079 36720793914565693926570119)
      ·
        refine ⟨55081190871848540889855179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36720793914565693926570119 55081190871848540889855179)
        ·
          refine ⟨82621786307772811334782769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55081190871848540889855179 82621786307772811334782769)
          ·
            refine ⟨61966339730829608501087077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82621786307772811334782769 61966339730829608501087077)
            ·
              refine ⟨11618688699530551593953827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61966339730829608501087077 11618688699530551593953827)
              ·
                refine ⟨17428033049295827390930741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11618688699530551593953827 17428033049295827390930741)
                ·
                  refine ⟨1633878098371483817899757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17428033049295827390930741 1633878098371483817899757)
                  ·
                    refine ⟨612704286889306431712409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1633878098371483817899757 612704286889306431712409)
                    ·
                      refine ⟨459528215166979823784307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 612704286889306431712409 459528215166979823784307)
                      ·
                        rfl

theorem cell23_894928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 5, 3, 2].length) (baseStart_894928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894928 prefixEnd_894928 := by exact prefixLift 894928
  have htrace : WordTrace (prefixWord ++ tailWord_894928) baseStart_894928 baseEnd_894928 := by
    simpa [prefixWord, tailWord_894928, baseEnd_894928] using wordTrace_append hprefix tailTrace_894928
  have hstable : (prefixWord ++ tailWord_894928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894928).length < 2 ^ (prefixWord ++ tailWord_894928).sum := by decide
  have hdescent : baseEnd_894928 < baseStart_894928 := by decide
  rcases family_descends (prefixWord ++ tailWord_894928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894945 : List Nat := [1, 2, 3, 1, 2, 1, 3, 4, 1, 3, 2]
def baseStart_894945 : Nat := 118140960795 + 894945 * 2 ^ 59
def prefixEnd_894945 : Nat := 4983230072969 + 3 ^ 40 * 894945 * 2
def baseEnd_894945 : Nat := 459536944338106257271729

theorem tailTrace_894945 : CollatzResearch.WordTrace tailWord_894945 prefixEnd_894945 459536944338106257271729 := by
  unfold tailWord_894945
  simp only [CollatzResearch.WordTrace]
  refine ⟨32641325742774584282542289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21760883828516389521694859 32641325742774584282542289)
  ·
    refine ⟨24480994307080938211906717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32641325742774584282542289 24480994307080938211906717)
    ·
      refine ⟨9180372865155351829465019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24480994307080938211906717 9180372865155351829465019)
      ·
        refine ⟨13770559297733027744197529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9180372865155351829465019 13770559297733027744197529)
        ·
          refine ⟨10327919473299770808148147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13770559297733027744197529 10327919473299770808148147)
          ·
            refine ⟨15491879209949656212222221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10327919473299770808148147 15491879209949656212222221)
            ·
              refine ⟨5809454703731121079583333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15491879209949656212222221 5809454703731121079583333)
              ·
                refine ⟨1089272756949585202421875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5809454703731121079583333 1089272756949585202421875)
                ·
                  refine ⟨1633909135424377803632813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1089272756949585202421875 1633909135424377803632813)
                  ·
                    refine ⟨612715925784141676362305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1633909135424377803632813 612715925784141676362305)
                    ·
                      refine ⟨459536944338106257271729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 612715925784141676362305 459536944338106257271729)
                      ·
                        rfl

theorem cell23_894945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 3, 2].length) (baseStart_894945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894945 prefixEnd_894945 := by exact prefixLift 894945
  have htrace : WordTrace (prefixWord ++ tailWord_894945) baseStart_894945 baseEnd_894945 := by
    simpa [prefixWord, tailWord_894945, baseEnd_894945] using wordTrace_append hprefix tailTrace_894945
  have hstable : (prefixWord ++ tailWord_894945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894945).length < 2 ^ (prefixWord ++ tailWord_894945).sum := by decide
  have hdescent : baseEnd_894945 < baseStart_894945 := by decide
  rcases family_descends (prefixWord ++ tailWord_894945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894971 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 4]
def baseStart_894971 : Nat := 118140960795 + 894971 * 2 ^ 59
def prefixEnd_894971 : Nat := 4983230072969 + 3 ^ 40 * 894971 * 2
def baseEnd_894971 : Nat := 459550294835123155546609

theorem tailTrace_894971 : CollatzResearch.WordTrace tailWord_894971 prefixEnd_894971 459550294835123155546609 := by
  unfold tailWord_894971
  simp only [CollatzResearch.WordTrace]
  refine ⟨32642274040680390722988767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21761516027120260481992511 32642274040680390722988767)
  ·
    refine ⟨48963411061020586084483151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32642274040680390722988767 48963411061020586084483151)
    ·
      refine ⟨73445116591530879126724727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48963411061020586084483151 73445116591530879126724727)
      ·
        refine ⟨110167674887296318690087091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73445116591530879126724727 110167674887296318690087091)
        ·
          refine ⟨165251512330944478035130637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110167674887296318690087091 165251512330944478035130637)
          ·
            refine ⟨61969317124104179263173989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165251512330944478035130637 61969317124104179263173989)
            ·
              refine ⟨11619246960769533611845123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61969317124104179263173989 11619246960769533611845123)
              ·
                refine ⟨17428870441154300417767685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11619246960769533611845123 17428870441154300417767685)
                ·
                  refine ⟨3267913207716431328331441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17428870441154300417767685 3267913207716431328331441)
                  ·
                    refine ⟨2450934905787323496248581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3267913207716431328331441 2450934905787323496248581)
                    ·
                      refine ⟨459550294835123155546609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2450934905787323496248581 459550294835123155546609)
                      ·
                        rfl

theorem cell23_894971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 4].length) (baseStart_894971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894971 prefixEnd_894971 := by exact prefixLift 894971
  have htrace : WordTrace (prefixWord ++ tailWord_894971) baseStart_894971 baseEnd_894971 := by
    simpa [prefixWord, tailWord_894971, baseEnd_894971] using wordTrace_append hprefix tailTrace_894971
  have hstable : (prefixWord ++ tailWord_894971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894971).length < 2 ^ (prefixWord ++ tailWord_894971).sum := by decide
  have hdescent : baseEnd_894971 < baseStart_894971 := by decide
  rcases family_descends (prefixWord ++ tailWord_894971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894986 : List Nat := [3, 1, 2, 2, 5, 1, 2, 1, 2, 1, 3]
def baseStart_894986 : Nat := 118140960795 + 894986 * 2 ^ 59
def prefixEnd_894986 : Nat := 4983230072969 + 3 ^ 40 * 894986 * 2
def baseEnd_894986 : Nat := 459557997044940596859041

theorem tailTrace_894986 : CollatzResearch.WordTrace tailWord_894986 prefixEnd_894986 459557997044940596859041 := by
  unfold tailWord_894986
  simp only [CollatzResearch.WordTrace]
  refine ⟨8160705283906512071196203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21761880757084032189856541 8160705283906512071196203)
  ·
    refine ⟨12241057925859768106794305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8160705283906512071196203 12241057925859768106794305)
    ·
      refine ⟨9180793444394826080095729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12241057925859768106794305 9180793444394826080095729)
      ·
        refine ⟨6885595083296119560071797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9180793444394826080095729 6885595083296119560071797)
        ·
          refine ⟨645524539059011208756731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6885595083296119560071797 645524539059011208756731)
          ·
            refine ⟨968286808588516813135097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645524539059011208756731 968286808588516813135097)
            ·
              refine ⟨726215106441387609851323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 968286808588516813135097 726215106441387609851323)
              ·
                refine ⟨1089322659662081414776985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 726215106441387609851323 1089322659662081414776985)
                ·
                  refine ⟨816991994746561061082739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1089322659662081414776985 816991994746561061082739)
                  ·
                    refine ⟨1225487992119841591624109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 816991994746561061082739 1225487992119841591624109)
                    ·
                      refine ⟨459557997044940596859041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1225487992119841591624109 459557997044940596859041)
                      ·
                        rfl

theorem cell23_894986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_894986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_894986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_894986 prefixEnd_894986 := by exact prefixLift 894986
  have htrace : WordTrace (prefixWord ++ tailWord_894986) baseStart_894986 baseEnd_894986 := by
    simpa [prefixWord, tailWord_894986, baseEnd_894986] using wordTrace_append hprefix tailTrace_894986
  have hstable : (prefixWord ++ tailWord_894986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894986).length < 2 ^ (prefixWord ++ tailWord_894986).sum := by decide
  have hdescent : baseEnd_894986 < baseStart_894986 := by decide
  rcases family_descends (prefixWord ++ tailWord_894986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895051 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 5]
def baseStart_895051 : Nat := 118140960795 + 895051 * 2 ^ 59
def prefixEnd_895051 : Nat := 4983230072969 + 3 ^ 40 * 895051 * 2
def baseEnd_895051 : Nat := 459591373287482842546241

theorem tailTrace_895051 : CollatzResearch.WordTrace tailWord_895051 prefixEnd_895051 459591373287482842546241 := by
  unfold tailWord_895051
  simp only [CollatzResearch.WordTrace]
  refine ⟨32645191880390564385901007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21763461253593709590600671 32645191880390564385901007)
  ·
    refine ⟨48967787820585846578851511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32645191880390564385901007 48967787820585846578851511)
    ·
      refine ⟨73451681730878769868277267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48967787820585846578851511 73451681730878769868277267)
      ·
        refine ⟨110177522596318154802415901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73451681730878769868277267 110177522596318154802415901)
        ·
          refine ⟨41316570973619308050905963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110177522596318154802415901 41316570973619308050905963)
          ·
            refine ⟨61974856460428962076358945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41316570973619308050905963 61974856460428962076358945)
            ·
              refine ⟨46481142345321721557269209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61974856460428962076358945 46481142345321721557269209)
              ·
                refine ⟨34860856758991291167951907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46481142345321721557269209 34860856758991291167951907)
                ·
                  refine ⟨52291285138486936751927861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34860856758991291167951907 52291285138486936751927861)
                  ·
                    refine ⟨4902307981733150320493237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52291285138486936751927861 4902307981733150320493237)
                    ·
                      refine ⟨459591373287482842546241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4902307981733150320493237 459591373287482842546241)
                      ·
                        rfl

theorem cell23_895051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 5].length) (baseStart_895051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895051 prefixEnd_895051 := by exact prefixLift 895051
  have htrace : WordTrace (prefixWord ++ tailWord_895051) baseStart_895051 baseEnd_895051 := by
    simpa [prefixWord, tailWord_895051, baseEnd_895051] using wordTrace_append hprefix tailTrace_895051
  have hstable : (prefixWord ++ tailWord_895051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895051).length < 2 ^ (prefixWord ++ tailWord_895051).sum := by decide
  have hdescent : baseEnd_895051 < baseStart_895051 := by decide
  rcases family_descends (prefixWord ++ tailWord_895051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895062 : List Nat := [5, 2, 2, 1, 1, 2, 1, 1, 1, 7]
def baseStart_895062 : Nat := 118140960795 + 895062 * 2 ^ 59
def prefixEnd_895062 : Nat := 4983230072969 + 3 ^ 40 * 895062 * 2
def baseEnd_895062 : Nat := 153199007191560766502897

theorem tailTrace_895062 : CollatzResearch.WordTrace tailWord_895062 prefixEnd_895062 153199007191560766502897 := by
  unfold tailWord_895062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2040349567709419579034465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21763728722233808843034293 2040349567709419579034465)
  ·
    refine ⟨1530262175782064684275849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2040349567709419579034465 1530262175782064684275849)
    ·
      refine ⟨1147696631836548513206887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1530262175782064684275849 1147696631836548513206887)
      ·
        refine ⟨1721544947754822769810331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1147696631836548513206887 1721544947754822769810331)
        ·
          refine ⟨2582317421632234154715497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1721544947754822769810331 2582317421632234154715497)
          ·
            refine ⟨1936738066224175616036623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2582317421632234154715497 1936738066224175616036623)
            ·
              refine ⟨2905107099336263424054935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1936738066224175616036623 2905107099336263424054935)
              ·
                refine ⟨4357660649004395136082403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2905107099336263424054935 4357660649004395136082403)
                ·
                  refine ⟨6536490973506592704123605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4357660649004395136082403 6536490973506592704123605)
                  ·
                    refine ⟨153199007191560766502897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6536490973506592704123605 153199007191560766502897)
                    ·
                      rfl

theorem cell23_895062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_895062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895062 prefixEnd_895062 := by exact prefixLift 895062
  have htrace : WordTrace (prefixWord ++ tailWord_895062) baseStart_895062 baseEnd_895062 := by
    simpa [prefixWord, tailWord_895062, baseEnd_895062] using wordTrace_append hprefix tailTrace_895062
  have hstable : (prefixWord ++ tailWord_895062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895062).length < 2 ^ (prefixWord ++ tailWord_895062).sum := by decide
  have hdescent : baseEnd_895062 < baseStart_895062 := by decide
  rcases family_descends (prefixWord ++ tailWord_895062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895085 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 4, 2, 3]
def baseStart_895085 : Nat := 118140960795 + 895085 * 2 ^ 59
def prefixEnd_895085 : Nat := 4983230072969 + 3 ^ 40 * 895085 * 2
def baseEnd_895085 : Nat := 459608831629735709521085

theorem tailTrace_895085 : CollatzResearch.WordTrace tailWord_895085 prefixEnd_895085 459608831629735709521085 := by
  unfold tailWord_895085
  simp only [CollatzResearch.WordTrace]
  refine ⟨32646431962267388192638709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21764287974844925461759139 32646431962267388192638709)
  ·
    refine ⟨3060602996462567643059879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32646431962267388192638709 3060602996462567643059879)
    ·
      refine ⟨4590904494693851464589819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3060602996462567643059879 4590904494693851464589819)
      ·
        refine ⟨6886356742040777196884729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4590904494693851464589819 6886356742040777196884729)
        ·
          refine ⟨5164767556530582897663547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6886356742040777196884729 5164767556530582897663547)
          ·
            refine ⟨7747151334795874346495321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5164767556530582897663547 7747151334795874346495321)
            ·
              refine ⟨5810363501096905759871491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7747151334795874346495321 5810363501096905759871491)
              ·
                refine ⟨8715545251645358639807237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5810363501096905759871491 8715545251645358639807237)
                ·
                  refine ⟨1634164734683504744963857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8715545251645358639807237 1634164734683504744963857)
                  ·
                    refine ⟨1225623551012628558722893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1634164734683504744963857 1225623551012628558722893)
                    ·
                      refine ⟨459608831629735709521085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1225623551012628558722893 459608831629735709521085)
                      ·
                        rfl

theorem cell23_895085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_895085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895085 prefixEnd_895085 := by exact prefixLift 895085
  have htrace : WordTrace (prefixWord ++ tailWord_895085) baseStart_895085 baseEnd_895085 := by
    simpa [prefixWord, tailWord_895085, baseEnd_895085] using wordTrace_append hprefix tailTrace_895085
  have hstable : (prefixWord ++ tailWord_895085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895085).length < 2 ^ (prefixWord ++ tailWord_895085).sum := by decide
  have hdescent : baseEnd_895085 < baseStart_895085 := by decide
  rcases family_descends (prefixWord ++ tailWord_895085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895088 : List Nat := [2, 1, 1, 1, 5, 3, 1, 1, 8]
def baseStart_895088 : Nat := 118140960795 + 895088 * 2 ^ 59
def prefixEnd_895088 : Nat := 4983230072969 + 3 ^ 40 * 895088 * 2
def baseEnd_895088 : Nat := 51067819119077688642619

theorem tailTrace_895088 : CollatzResearch.WordTrace tailWord_895088 prefixEnd_895088 51067819119077688642619 := by
  unfold tailWord_895088
  simp only [CollatzResearch.WordTrace]
  refine ⟨16323270690628259852498959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21764360920837679803331945 16323270690628259852498959)
  ·
    refine ⟨24484906035942389778748439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16323270690628259852498959 24484906035942389778748439)
    ·
      refine ⟨36727359053913584668122659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24484906035942389778748439 36727359053913584668122659)
      ·
        refine ⟨55091038580870377002183989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36727359053913584668122659 55091038580870377002183989)
        ·
          refine ⟨5164784866956597843954749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55091038580870377002183989 5164784866956597843954749)
          ·
            refine ⟨1936794325108724191483031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5164784866956597843954749 1936794325108724191483031)
            ·
              refine ⟨2905191487663086287224547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1936794325108724191483031 2905191487663086287224547)
              ·
                refine ⟨4357787231494629430836821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2905191487663086287224547 4357787231494629430836821)
                ·
                  refine ⟨51067819119077688642619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4357787231494629430836821 51067819119077688642619)
                  ·
                    rfl

theorem cell23_895088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 8].length) (baseStart_895088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895088 prefixEnd_895088 := by exact prefixLift 895088
  have htrace : WordTrace (prefixWord ++ tailWord_895088) baseStart_895088 baseEnd_895088 := by
    simpa [prefixWord, tailWord_895088, baseEnd_895088] using wordTrace_append hprefix tailTrace_895088
  have hstable : (prefixWord ++ tailWord_895088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895088).length < 2 ^ (prefixWord ++ tailWord_895088).sum := by decide
  have hdescent : baseEnd_895088 < baseStart_895088 := by decide
  rcases family_descends (prefixWord ++ tailWord_895088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895108 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 1, 2, 6]
def baseStart_895108 : Nat := 118140960795 + 895108 * 2 ^ 59
def prefixEnd_895108 : Nat := 4983230072969 + 3 ^ 40 * 895108 * 2
def baseEnd_895108 : Nat := 459620641684789119533479

theorem tailTrace_895108 : CollatzResearch.WordTrace tailWord_895108 prefixEnd_895108 459620641684789119533479 := by
  unfold tailWord_895108
  simp only [CollatzResearch.WordTrace]
  refine ⟨16323635420592031560362989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21764847227456042080483985 16323635420592031560362989)
  ·
    refine ⟨6121363282722011835136121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16323635420592031560362989 6121363282722011835136121)
    ·
      refine ⟨4591022462041508876352091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6121363282722011835136121 4591022462041508876352091)
      ·
        refine ⟨6886533693062263314528137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4591022462041508876352091 6886533693062263314528137)
        ·
          refine ⟨5164900269796697485896103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6886533693062263314528137 5164900269796697485896103)
          ·
            refine ⟨7747350404695046228844155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5164900269796697485896103 7747350404695046228844155)
            ·
              refine ⟨11621025607042569343266233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7747350404695046228844155 11621025607042569343266233)
              ·
                refine ⟨8715769205281927007449675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11621025607042569343266233 8715769205281927007449675)
                ·
                  refine ⟨13073653807922890511174513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8715769205281927007449675 13073653807922890511174513)
                  ·
                    refine ⟨9805240355942167883380885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13073653807922890511174513 9805240355942167883380885)
                    ·
                      refine ⟨459620641684789119533479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9805240355942167883380885 459620641684789119533479)
                      ·
                        rfl

theorem cell23_895108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_895108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895108 prefixEnd_895108 := by exact prefixLift 895108
  have htrace : WordTrace (prefixWord ++ tailWord_895108) baseStart_895108 baseEnd_895108 := by
    simpa [prefixWord, tailWord_895108, baseEnd_895108] using wordTrace_append hprefix tailTrace_895108
  have hstable : (prefixWord ++ tailWord_895108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895108).length < 2 ^ (prefixWord ++ tailWord_895108).sum := by decide
  have hdescent : baseEnd_895108 < baseStart_895108 := by decide
  rcases family_descends (prefixWord ++ tailWord_895108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895125 : List Nat := [1, 3, 2, 1, 1, 1, 3, 3, 1, 5, 2]
def baseStart_895125 : Nat := 118140960795 + 895125 * 2 ^ 59
def prefixEnd_895125 : Nat := 4983230072969 + 3 ^ 40 * 895125 * 2
def baseEnd_895125 : Nat := 459629370855915553020901

theorem tailTrace_895125 : CollatzResearch.WordTrace tailWord_895125 prefixEnd_895125 459629370855915553020901 := by
  unfold tailWord_895125
  simp only [CollatzResearch.WordTrace]
  refine ⟨32647890882122475024094829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21765260588081650016063219 32647890882122475024094829)
  ·
    refine ⟨12242959080795928134035561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32647890882122475024094829 12242959080795928134035561)
    ·
      refine ⟨9182219310596946100526671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12242959080795928134035561 9182219310596946100526671)
      ·
        refine ⟨13773328965895419150790007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9182219310596946100526671 13773328965895419150790007)
        ·
          refine ⟨20659993448843128726185011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13773328965895419150790007 20659993448843128726185011)
          ·
            refine ⟨30989990173264693089277517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20659993448843128726185011 30989990173264693089277517)
            ·
              refine ⟨11621246314974259908479069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30989990173264693089277517 11621246314974259908479069)
              ·
                refine ⟨4357967368115347465679651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11621246314974259908479069 4357967368115347465679651)
                ·
                  refine ⟨6536951052173021198519477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4357967368115347465679651 6536951052173021198519477)
                  ·
                    refine ⟨612839161141220737361201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6536951052173021198519477 612839161141220737361201)
                    ·
                      refine ⟨459629370855915553020901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 612839161141220737361201 459629370855915553020901)
                      ·
                        rfl

theorem cell23_895125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 5, 2].length) (baseStart_895125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895125 prefixEnd_895125 := by exact prefixLift 895125
  have htrace : WordTrace (prefixWord ++ tailWord_895125) baseStart_895125 baseEnd_895125 := by
    simpa [prefixWord, tailWord_895125, baseEnd_895125] using wordTrace_append hprefix tailTrace_895125
  have hstable : (prefixWord ++ tailWord_895125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895125).length < 2 ^ (prefixWord ++ tailWord_895125).sum := by decide
  have hdescent : baseEnd_895125 < baseStart_895125 := by decide
  rcases family_descends (prefixWord ++ tailWord_895125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895149 : List Nat := [1, 5, 2, 1, 2, 1, 3, 1, 3, 1, 3]
def baseStart_895149 : Nat := 118140960795 + 895149 * 2 ^ 59
def prefixEnd_895149 : Nat := 4983230072969 + 3 ^ 40 * 895149 * 2
def baseEnd_895149 : Nat := 459641694391623459120791

theorem tailTrace_895149 : CollatzResearch.WordTrace tailWord_895149 prefixEnd_895149 459641694391623459120791 := by
  unfold tailWord_895149
  simp only [CollatzResearch.WordTrace]
  refine ⟨32648766234035527122968501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21765844156023684748645667 32648766234035527122968501)
  ·
    refine ⟨3060821834440830667778297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32648766234035527122968501 3060821834440830667778297)
    ·
      refine ⟨2295616375830623000833723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3060821834440830667778297 2295616375830623000833723)
      ·
        refine ⟨3443424563745934501250585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2295616375830623000833723 3443424563745934501250585)
        ·
          refine ⟨2582568422809450875937939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3443424563745934501250585 2582568422809450875937939)
          ·
            refine ⟨3873852634214176313906909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2582568422809450875937939 3873852634214176313906909)
            ·
              refine ⟨1452694737830316117715091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3873852634214176313906909 1452694737830316117715091)
              ·
                refine ⟨2179042106745474176572637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1452694737830316117715091 2179042106745474176572637)
                ·
                  refine ⟨817140790029552816214739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2179042106745474176572637 817140790029552816214739)
                  ·
                    refine ⟨1225711185044329224322109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 817140790029552816214739 1225711185044329224322109)
                    ·
                      refine ⟨459641694391623459120791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1225711185044329224322109 459641694391623459120791)
                      ·
                        rfl

theorem cell23_895149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_895149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895149 prefixEnd_895149 := by exact prefixLift 895149
  have htrace : WordTrace (prefixWord ++ tailWord_895149) baseStart_895149 baseEnd_895149 := by
    simpa [prefixWord, tailWord_895149, baseEnd_895149] using wordTrace_append hprefix tailTrace_895149
  have hstable : (prefixWord ++ tailWord_895149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895149).length < 2 ^ (prefixWord ++ tailWord_895149).sum := by decide
  have hdescent : baseEnd_895149 < baseStart_895149 := by decide
  rcases family_descends (prefixWord ++ tailWord_895149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895156 : List Nat := [2, 5, 3, 1, 1, 1, 1, 3, 6]
def baseStart_895156 : Nat := 118140960795 + 895156 * 2 ^ 59
def prefixEnd_895156 : Nat := 4983230072969 + 3 ^ 40 * 895156 * 2
def baseEnd_895156 : Nat := 51071698750689436859251

theorem tailTrace_895156 : CollatzResearch.WordTrace tailWord_895156 prefixEnd_895156 51071698750689436859251 := by
  unfold tailWord_895156
  simp only [CollatzResearch.WordTrace]
  refine ⟨16324510772505083659236661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21766014363340111545648881 16324510772505083659236661)
  ·
    refine ⟨1530422884922351593053437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16324510772505083659236661 1530422884922351593053437)
    ·
      refine ⟨573908581845881847395039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1530422884922351593053437 573908581845881847395039)
      ·
        refine ⟨860862872768822771092559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573908581845881847395039 860862872768822771092559)
        ·
          refine ⟨1291294309153234156638839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860862872768822771092559 1291294309153234156638839)
          ·
            refine ⟨1936941463729851234958259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1291294309153234156638839 1936941463729851234958259)
            ·
              refine ⟨2905412195594776852437389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1936941463729851234958259 2905412195594776852437389)
              ·
                refine ⟨1089529573348041319664021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2905412195594776852437389 1089529573348041319664021)
                ·
                  refine ⟨51071698750689436859251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1089529573348041319664021 51071698750689436859251)
                  ·
                    rfl

theorem cell23_895156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_895156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895156 prefixEnd_895156 := by exact prefixLift 895156
  have htrace : WordTrace (prefixWord ++ tailWord_895156) baseStart_895156 baseEnd_895156 := by
    simpa [prefixWord, tailWord_895156, baseEnd_895156] using wordTrace_append hprefix tailTrace_895156
  have hstable : (prefixWord ++ tailWord_895156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895156).length < 2 ^ (prefixWord ++ tailWord_895156).sum := by decide
  have hdescent : baseEnd_895156 < baseStart_895156 := by decide
  rcases family_descends (prefixWord ++ tailWord_895156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895172 : List Nat := [2, 3, 3, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_895172 : Nat := 118140960795 + 895172 * 2 ^ 59
def prefixEnd_895172 : Nat := 4983230072969 + 3 ^ 40 * 895172 * 2
def baseEnd_895172 : Nat := 459653504446676869133185

theorem tailTrace_895172 : CollatzResearch.WordTrace tailWord_895172 prefixEnd_895172 459653504446676869133185 := by
  unfold tailWord_895172
  simp only [CollatzResearch.WordTrace]
  refine ⟨16324802556476101025527885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21766403408634801367370513 16324802556476101025527885)
  ·
    refine ⟨6121800958678537884572957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16324802556476101025527885 6121800958678537884572957)
    ·
      refine ⟨2295675359504451706714859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6121800958678537884572957 2295675359504451706714859)
      ·
        refine ⟨3443513039256677560072289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2295675359504451706714859 3443513039256677560072289)
        ·
          refine ⟨2582634779442508170054217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3443513039256677560072289 2582634779442508170054217)
          ·
            refine ⟨1936976084581881127540663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2582634779442508170054217 1936976084581881127540663)
            ·
              refine ⟨2905464126872821691310995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1936976084581881127540663 2905464126872821691310995)
              ·
                refine ⟨4358196190309232536966493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2905464126872821691310995 4358196190309232536966493)
                ·
                  refine ⟨1634323571365962201362435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4358196190309232536966493 1634323571365962201362435)
                  ·
                    refine ⟨2451485357048943302043653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1634323571365962201362435 2451485357048943302043653)
                    ·
                      refine ⟨459653504446676869133185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2451485357048943302043653 459653504446676869133185)
                      ·
                        rfl

theorem cell23_895172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_895172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895172 prefixEnd_895172 := by exact prefixLift 895172
  have htrace : WordTrace (prefixWord ++ tailWord_895172) baseStart_895172 baseEnd_895172 := by
    simpa [prefixWord, tailWord_895172, baseEnd_895172] using wordTrace_append hprefix tailTrace_895172
  have hstable : (prefixWord ++ tailWord_895172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895172).length < 2 ^ (prefixWord ++ tailWord_895172).sum := by decide
  have hdescent : baseEnd_895172 < baseStart_895172 := by decide
  rcases family_descends (prefixWord ++ tailWord_895172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895178 : List Nat := [3, 1, 2, 1, 3, 1, 1, 11]
def baseStart_895178 : Nat := 118140960795 + 895178 * 2 ^ 59
def prefixEnd_895178 : Nat := 4983230072969 + 3 ^ 40 * 895178 * 2
def baseEnd_895178 : Nat := 17024317975207549839191

theorem tailTrace_895178 : CollatzResearch.WordTrace tailWord_895178 prefixEnd_895178 17024317975207549839191 := by
  unfold tailWord_895178
  simp only [CollatzResearch.WordTrace]
  refine ⟨8162455987732616268943547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21766549300620310050516125 8162455987732616268943547)
  ·
    refine ⟨12243683981598924403415321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8162455987732616268943547 12243683981598924403415321)
    ·
      refine ⟨9182762986199193302561491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12243683981598924403415321 9182762986199193302561491)
      ·
        refine ⟨13774144479298789953842237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9182762986199193302561491 13774144479298789953842237)
        ·
          refine ⟨5165304179737046232690839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13774144479298789953842237 5165304179737046232690839)
          ·
            refine ⟨7747956269605569349036259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5165304179737046232690839 7747956269605569349036259)
            ·
              refine ⟨11621934404408354023554389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7747956269605569349036259 11621934404408354023554389)
              ·
                refine ⟨17024317975207549839191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 11621934404408354023554389 17024317975207549839191)
                ·
                  rfl

theorem cell23_895178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 11].length) (baseStart_895178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895178 prefixEnd_895178 := by exact prefixLift 895178
  have htrace : WordTrace (prefixWord ++ tailWord_895178) baseStart_895178 baseEnd_895178 := by
    simpa [prefixWord, tailWord_895178, baseEnd_895178] using wordTrace_append hprefix tailTrace_895178
  have hstable : (prefixWord ++ tailWord_895178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895178).length < 2 ^ (prefixWord ++ tailWord_895178).sum := by decide
  have hdescent : baseEnd_895178 < baseStart_895178 := by decide
  rcases family_descends (prefixWord ++ tailWord_895178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895192 : List Nat := [2, 1, 2, 2, 4, 3, 1, 1, 1, 1, 5]
def baseStart_895192 : Nat := 118140960795 + 895192 * 2 ^ 59
def prefixEnd_895192 : Nat := 4983230072969 + 3 ^ 40 * 895192 * 2
def baseEnd_895192 : Nat := 459663774059766790883093

theorem tailTrace_895192 : CollatzResearch.WordTrace tailWord_895192 prefixEnd_895192 459663774059766790883093 := by
  unfold tailWord_895192
  simp only [CollatzResearch.WordTrace]
  refine ⟨16325167286439872733391915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21766889715253163644522553 16325167286439872733391915)
  ·
    refine ⟨24487750929659809100087873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16325167286439872733391915 24487750929659809100087873)
    ·
      refine ⟨18365813197244856825065905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24487750929659809100087873 18365813197244856825065905)
      ·
        refine ⟨13774359897933642618799429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18365813197244856825065905 13774359897933642618799429)
        ·
          refine ⟨2582692480862557991024893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13774359897933642618799429 2582692480862557991024893)
          ·
            refine ⟨968509680323459246634335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2582692480862557991024893 968509680323459246634335)
            ·
              refine ⟨1452764520485188869951503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 968509680323459246634335 1452764520485188869951503)
              ·
                refine ⟨2179146780727783304927255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1452764520485188869951503 2179146780727783304927255)
                ·
                  refine ⟨3268720171091674957390883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2179146780727783304927255 3268720171091674957390883)
                  ·
                    refine ⟨4903080256637512436086325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3268720171091674957390883 4903080256637512436086325)
                    ·
                      refine ⟨459663774059766790883093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4903080256637512436086325 459663774059766790883093)
                      ·
                        rfl

theorem cell23_895192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_895192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895192 prefixEnd_895192 := by exact prefixLift 895192
  have htrace : WordTrace (prefixWord ++ tailWord_895192) baseStart_895192 baseEnd_895192 := by
    simpa [prefixWord, tailWord_895192, baseEnd_895192] using wordTrace_append hprefix tailTrace_895192
  have hstable : (prefixWord ++ tailWord_895192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895192).length < 2 ^ (prefixWord ++ tailWord_895192).sum := by decide
  have hdescent : baseEnd_895192 < baseStart_895192 := by decide
  rcases family_descends (prefixWord ++ tailWord_895192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895222 : List Nat := [5, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3]
def baseStart_895222 : Nat := 118140960795 + 895222 * 2 ^ 59
def prefixEnd_895222 : Nat := 4983230072969 + 3 ^ 40 * 895222 * 2
def baseEnd_895222 : Nat := 459679178479401673507955

theorem tailTrace_895222 : CollatzResearch.WordTrace tailWord_895222 prefixEnd_895222 459679178479401673507955 := by
  unfold tailWord_895222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2040714297673191286898495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21767619175180707060250613 2040714297673191286898495)
  ·
    refine ⟨3061071446509786930347743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2040714297673191286898495 3061071446509786930347743)
    ·
      refine ⟨4591607169764680395521615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3061071446509786930347743 4591607169764680395521615)
      ·
        refine ⟨6887410754647020593282423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4591607169764680395521615 6887410754647020593282423)
        ·
          refine ⟨10331116131970530889923635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6887410754647020593282423 10331116131970530889923635)
          ·
            refine ⟨15496674197955796334885453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10331116131970530889923635 15496674197955796334885453)
            ·
              refine ⟨5811252824233423625582045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15496674197955796334885453 5811252824233423625582045)
              ·
                refine ⟨2179219809087533859593267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5811252824233423625582045 2179219809087533859593267)
                ·
                  refine ⟨3268829713631300789389901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2179219809087533859593267 3268829713631300789389901)
                  ·
                    refine ⟨1225811142611737796021213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3268829713631300789389901 1225811142611737796021213)
                    ·
                      refine ⟨459679178479401673507955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1225811142611737796021213 459679178479401673507955)
                      ·
                        rfl

theorem cell23_895222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_895222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895222 prefixEnd_895222 := by exact prefixLift 895222
  have htrace : WordTrace (prefixWord ++ tailWord_895222) baseStart_895222 baseEnd_895222 := by
    simpa [prefixWord, tailWord_895222, baseEnd_895222] using wordTrace_append hprefix tailTrace_895222
  have hstable : (prefixWord ++ tailWord_895222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895222).length < 2 ^ (prefixWord ++ tailWord_895222).sum := by decide
  have hdescent : baseEnd_895222 < baseStart_895222 := by decide
  rcases family_descends (prefixWord ++ tailWord_895222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895232 : List Nat := [2, 1, 1, 2, 1, 1, 6, 1, 3, 3, 2]
def baseStart_895232 : Nat := 118140960795 + 895232 * 2 ^ 59
def prefixEnd_895232 : Nat := 4983230072969 + 3 ^ 40 * 895232 * 2
def baseEnd_895232 : Nat := 459684313285946634382909

theorem tailTrace_895232 : CollatzResearch.WordTrace tailWord_895232 prefixEnd_895232 459684313285946634382909 := by
  unfold tailWord_895232
  simp only [CollatzResearch.WordTrace]
  refine ⟨16325896746367416149119975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21767862328489888198826633 16325896746367416149119975)
  ·
    refine ⟨24488845119551124223679963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16325896746367416149119975 24488845119551124223679963)
    ·
      refine ⟨36733267679326686335519945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24488845119551124223679963 36733267679326686335519945)
      ·
        refine ⟨27549950759495014751639959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36733267679326686335519945 27549950759495014751639959)
        ·
          refine ⟨41324926139242522127459939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27549950759495014751639959 41324926139242522127459939)
          ·
            refine ⟨61987389208863783191189909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41324926139242522127459939 61987389208863783191189909)
            ·
              refine ⟨2905658869165489837087027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61987389208863783191189909 2905658869165489837087027)
              ·
                refine ⟨4358488303748234755630541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2905658869165489837087027 4358488303748234755630541)
                ·
                  refine ⟨1634433113905588033361453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4358488303748234755630541 1634433113905588033361453)
                  ·
                    refine ⟨612912417714595512510545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1634433113905588033361453 612912417714595512510545)
                    ·
                      refine ⟨459684313285946634382909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 612912417714595512510545 459684313285946634382909)
                      ·
                        rfl

theorem cell23_895232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 3, 3, 2].length) (baseStart_895232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895232 prefixEnd_895232 := by exact prefixLift 895232
  have htrace : WordTrace (prefixWord ++ tailWord_895232) baseStart_895232 baseEnd_895232 := by
    simpa [prefixWord, tailWord_895232, baseEnd_895232] using wordTrace_append hprefix tailTrace_895232
  have hstable : (prefixWord ++ tailWord_895232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895232).length < 2 ^ (prefixWord ++ tailWord_895232).sum := by decide
  have hdescent : baseEnd_895232 < baseStart_895232 := by decide
  rcases family_descends (prefixWord ++ tailWord_895232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895249 : List Nat := [1, 2, 2, 1, 1, 6, 1, 3, 1, 3, 2]
def baseStart_895249 : Nat := 118140960795 + 895249 * 2 ^ 59
def prefixEnd_895249 : Nat := 4983230072969 + 3 ^ 40 * 895249 * 2
def baseEnd_895249 : Nat := 459693042457073067870331

theorem tailTrace_895249 : CollatzResearch.WordTrace tailWord_895249 prefixEnd_895249 459693042457073067870331 := by
  unfold tailWord_895249
  simp only [CollatzResearch.WordTrace]
  refine ⟨32652413533673244201608801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21768275689115496134405867 32652413533673244201608801)
  ·
    refine ⟨24489310150254933151206601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32652413533673244201608801 24489310150254933151206601)
    ·
      refine ⟨18366982612691199863404951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24489310150254933151206601 18366982612691199863404951)
      ·
        refine ⟨27550473919036799795107427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18366982612691199863404951 27550473919036799795107427)
        ·
          refine ⟨41325710878555199692661141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27550473919036799795107427 41325710878555199692661141)
          ·
            refine ⟨1937142697432274985593491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41325710878555199692661141 1937142697432274985593491)
            ·
              refine ⟨2905714046148412478390237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1937142697432274985593491 2905714046148412478390237)
              ·
                refine ⟨1089642767305654679396339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2905714046148412478390237 1089642767305654679396339)
                ·
                  refine ⟨1634464150958482019094509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1089642767305654679396339 1634464150958482019094509)
                  ·
                    refine ⟨612924056609430757160441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1634464150958482019094509 612924056609430757160441)
                    ·
                      refine ⟨459693042457073067870331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 612924056609430757160441 459693042457073067870331)
                      ·
                        rfl

theorem cell23_895249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 3, 2].length) (baseStart_895249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895249 prefixEnd_895249 := by exact prefixLift 895249
  have htrace : WordTrace (prefixWord ++ tailWord_895249) baseStart_895249 baseEnd_895249 := by
    simpa [prefixWord, tailWord_895249, baseEnd_895249] using wordTrace_append hprefix tailTrace_895249
  have hstable : (prefixWord ++ tailWord_895249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895249).length < 2 ^ (prefixWord ++ tailWord_895249).sum := by decide
  have hdescent : baseEnd_895249 < baseStart_895249 := by decide
  rcases family_descends (prefixWord ++ tailWord_895249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895255 : List Nat := [1, 1, 3, 4, 1, 2, 1, 2, 2, 6]
def baseStart_895255 : Nat := 118140960795 + 895255 * 2 ^ 59
def prefixEnd_895255 : Nat := 4983230072969 + 3 ^ 40 * 895255 * 2
def baseEnd_895255 : Nat := 153232041113666681465101

theorem tailTrace_895255 : CollatzResearch.WordTrace tailWord_895255 prefixEnd_895255 153232041113666681465101 := by
  unfold tailWord_895255
  simp only [CollatzResearch.WordTrace]
  refine ⟨32652632371651507226327219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21768421581101004817551479 32652632371651507226327219)
  ·
    refine ⟨48978948557477260839490829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32652632371651507226327219 48978948557477260839490829)
    ·
      refine ⟨18367105709053972814809061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48978948557477260839490829 18367105709053972814809061)
      ·
        refine ⟨3443832320447619902776699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18367105709053972814809061 3443832320447619902776699)
        ·
          refine ⟨5165748480671429854165049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3443832320447619902776699 5165748480671429854165049)
          ·
            refine ⟨3874311360503572390623787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5165748480671429854165049 3874311360503572390623787)
            ·
              refine ⟨5811467040755358585935681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3874311360503572390623787 5811467040755358585935681)
              ·
                refine ⟨4358600280566518939451761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5811467040755358585935681 4358600280566518939451761)
                ·
                  refine ⟨3268950210424889204588821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4358600280566518939451761 3268950210424889204588821)
                  ·
                    refine ⟨153232041113666681465101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3268950210424889204588821 153232041113666681465101)
                    ·
                      rfl

theorem cell23_895255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 6].length) (baseStart_895255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895255 prefixEnd_895255 := by exact prefixLift 895255
  have htrace : WordTrace (prefixWord ++ tailWord_895255) baseStart_895255 baseEnd_895255 := by
    simpa [prefixWord, tailWord_895255, baseEnd_895255] using wordTrace_append hprefix tailTrace_895255
  have hstable : (prefixWord ++ tailWord_895255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895255).length < 2 ^ (prefixWord ++ tailWord_895255).sum := by decide
  have hdescent : baseEnd_895255 < baseStart_895255 := by decide
  rcases family_descends (prefixWord ++ tailWord_895255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895265 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 1, 6, 3]
def baseStart_895265 : Nat := 118140960795 + 895265 * 2 ^ 59
def prefixEnd_895265 : Nat := 4983230072969 + 3 ^ 40 * 895265 * 2
def baseEnd_895265 : Nat := 459701258147545005270257

theorem tailTrace_895265 : CollatzResearch.WordTrace tailWord_895265 prefixEnd_895265 459701258147545005270257 := by
  unfold tailWord_895265
  simp only [CollatzResearch.WordTrace]
  refine ⟨32652997101615278934191249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21768664734410185956127499 32652997101615278934191249)
  ·
    refine ⟨24489747826211459200643437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32652997101615278934191249 24489747826211459200643437)
    ·
      refine ⟨9183655434829297200241289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24489747826211459200643437 9183655434829297200241289)
      ·
        refine ⟨6887741576121972900180967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9183655434829297200241289 6887741576121972900180967)
        ·
          refine ⟨10331612364182959350271451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6887741576121972900180967 10331612364182959350271451)
          ·
            refine ⟨15497418546274439025407177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10331612364182959350271451 15497418546274439025407177)
            ·
              refine ⟨11623063909705829269055383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15497418546274439025407177 11623063909705829269055383)
              ·
                refine ⟨17434595864558743903583075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11623063909705829269055383 17434595864558743903583075)
                ·
                  refine ⟨26151893796838115855374613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17434595864558743903583075 26151893796838115855374613)
                  ·
                    refine ⟨1225870021726786680720685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26151893796838115855374613 1225870021726786680720685)
                    ·
                      refine ⟨459701258147545005270257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1225870021726786680720685 459701258147545005270257)
                      ·
                        rfl

theorem cell23_895265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_895265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895265 prefixEnd_895265 := by exact prefixLift 895265
  have htrace : WordTrace (prefixWord ++ tailWord_895265) baseStart_895265 baseEnd_895265 := by
    simpa [prefixWord, tailWord_895265, baseEnd_895265] using wordTrace_append hprefix tailTrace_895265
  have hstable : (prefixWord ++ tailWord_895265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895265).length < 2 ^ (prefixWord ++ tailWord_895265).sum := by decide
  have hdescent : baseEnd_895265 < baseStart_895265 := by decide
  rcases family_descends (prefixWord ++ tailWord_895265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895279 : List Nat := [1, 1, 2, 1, 2, 1, 4, 5, 2, 2, 2]
def baseStart_895279 : Nat := 118140960795 + 895279 * 2 ^ 59
def prefixEnd_895279 : Nat := 4983230072969 + 3 ^ 40 * 895279 * 2
def baseEnd_895279 : Nat := 459708446876707950495193

theorem tailTrace_895279 : CollatzResearch.WordTrace tailWord_895279 prefixEnd_895279 459708446876707950495193 := by
  unfold tailWord_895279
  simp only [CollatzResearch.WordTrace]
  refine ⟨32653507723564559325200891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21769005149043039550133927 32653507723564559325200891)
  ·
    refine ⟨48980261585346838987801337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32653507723564559325200891 48980261585346838987801337)
    ·
      refine ⟨36735196189010129240851003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48980261585346838987801337 36735196189010129240851003)
      ·
        refine ⟨55102794283515193861276505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36735196189010129240851003 55102794283515193861276505)
        ·
          refine ⟨41327095712636395395957379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55102794283515193861276505 41327095712636395395957379)
          ·
            refine ⟨61990643568954593093936069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41327095712636395395957379 61990643568954593093936069)
            ·
              refine ⟨11623245669178986205113013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61990643568954593093936069 11623245669178986205113013)
              ·
                refine ⟨1089679281485529956729345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11623245669178986205113013 1089679281485529956729345)
                ·
                  refine ⟨817259461114147467547009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1089679281485529956729345 817259461114147467547009)
                  ·
                    refine ⟨612944595835610600660257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 817259461114147467547009 612944595835610600660257)
                    ·
                      refine ⟨459708446876707950495193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 612944595835610600660257 459708446876707950495193)
                      ·
                        rfl

theorem cell23_895279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 2, 2, 2].length) (baseStart_895279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895279 prefixEnd_895279 := by exact prefixLift 895279
  have htrace : WordTrace (prefixWord ++ tailWord_895279) baseStart_895279 baseEnd_895279 := by
    simpa [prefixWord, tailWord_895279, baseEnd_895279] using wordTrace_append hprefix tailTrace_895279
  have hstable : (prefixWord ++ tailWord_895279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895279).length < 2 ^ (prefixWord ++ tailWord_895279).sum := by decide
  have hdescent : baseEnd_895279 < baseStart_895279 := by decide
  rcases family_descends (prefixWord ++ tailWord_895279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895285 : List Nat := [1, 3, 3, 1, 2, 1, 1, 4, 7]
def baseStart_895285 : Nat := 118140960795 + 895285 * 2 ^ 59
def prefixEnd_895285 : Nat := 4983230072969 + 3 ^ 40 * 895285 * 2
def baseEnd_895285 : Nat := 51079058640070547446685

theorem tailTrace_895285 : CollatzResearch.WordTrace tailWord_895285 prefixEnd_895285 51079058640070547446685 := by
  unfold tailWord_895285
  simp only [CollatzResearch.WordTrace]
  refine ⟨32653726561542822349919309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21769151041028548233279539 32653726561542822349919309)
  ·
    refine ⟨12245147460578558381219741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32653726561542822349919309 12245147460578558381219741)
    ·
      refine ⟨4591930297716959392957403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12245147460578558381219741 4591930297716959392957403)
      ·
        refine ⟨6887895446575439089436105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4591930297716959392957403 6887895446575439089436105)
        ·
          refine ⟨5165921584931579317077079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6887895446575439089436105 5165921584931579317077079)
          ·
            refine ⟨7748882377397368975615619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5165921584931579317077079 7748882377397368975615619)
            ·
              refine ⟨11623323566096053463423429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7748882377397368975615619 11623323566096053463423429)
              ·
                refine ⟨2179373168643010024391893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11623323566096053463423429 2179373168643010024391893)
                ·
                  refine ⟨51079058640070547446685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2179373168643010024391893 51079058640070547446685)
                  ·
                    rfl

theorem cell23_895285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 7].length) (baseStart_895285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895285 prefixEnd_895285 := by exact prefixLift 895285
  have htrace : WordTrace (prefixWord ++ tailWord_895285) baseStart_895285 baseEnd_895285 := by
    simpa [prefixWord, tailWord_895285, baseEnd_895285] using wordTrace_append hprefix tailTrace_895285
  have hstable : (prefixWord ++ tailWord_895285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895285).length < 2 ^ (prefixWord ++ tailWord_895285).sum := by decide
  have hdescent : baseEnd_895285 < baseStart_895285 := by decide
  rcases family_descends (prefixWord ++ tailWord_895285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895319 : List Nat := [1, 1, 3, 2, 3, 1, 5, 2, 5]
def baseStart_895319 : Nat := 118140960795 + 895319 * 2 ^ 59
def prefixEnd_895319 : Nat := 4983230072969 + 3 ^ 40 * 895319 * 2
def baseEnd_895319 : Nat := 51080998455876421555001

theorem tailTrace_895319 : CollatzResearch.WordTrace tailWord_895319 prefixEnd_895319 51080998455876421555001 := by
  unfold tailWord_895319
  simp only [CollatzResearch.WordTrace]
  refine ⟨32654966643419646156657011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21769977762279764104438007 32654966643419646156657011)
  ·
    refine ⟨48982449965129469234985517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32654966643419646156657011 48982449965129469234985517)
    ·
      refine ⟨18368418736923550963119569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48982449965129469234985517 18368418736923550963119569)
      ·
        refine ⟨13776314052692663222339677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18368418736923550963119569 13776314052692663222339677)
        ·
          refine ⟨5166117769759748708377379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13776314052692663222339677 5166117769759748708377379)
          ·
            refine ⟨7749176654639623062566069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5166117769759748708377379 7749176654639623062566069)
            ·
              refine ⟨726485311372464662115569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7749176654639623062566069 726485311372464662115569)
              ·
                refine ⟨544863983529348496586677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 726485311372464662115569 544863983529348496586677)
                ·
                  refine ⟨51080998455876421555001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 544863983529348496586677 51080998455876421555001)
                  ·
                    rfl

theorem cell23_895319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 2, 5].length) (baseStart_895319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895319 prefixEnd_895319 := by exact prefixLift 895319
  have htrace : WordTrace (prefixWord ++ tailWord_895319) baseStart_895319 baseEnd_895319 := by
    simpa [prefixWord, tailWord_895319, baseEnd_895319] using wordTrace_append hprefix tailTrace_895319
  have hstable : (prefixWord ++ tailWord_895319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895319).length < 2 ^ (prefixWord ++ tailWord_895319).sum := by decide
  have hdescent : baseEnd_895319 < baseStart_895319 := by decide
  rcases family_descends (prefixWord ++ tailWord_895319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895322 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 2, 5, 2]
def baseStart_895322 : Nat := 118140960795 + 895322 * 2 ^ 59
def prefixEnd_895322 : Nat := 4983230072969 + 3 ^ 40 * 895322 * 2
def baseEnd_895322 : Nat := 459730526544851282257495

theorem tailTrace_895322 : CollatzResearch.WordTrace tailWord_895322 prefixEnd_895322 459730526544851282257495 := by
  unfold tailWord_895322
  simp only [CollatzResearch.WordTrace]
  refine ⟨8163769015602194417254055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21770050708272518446010813 8163769015602194417254055)
  ·
    refine ⟨12245653523403291625881083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8163769015602194417254055 12245653523403291625881083)
    ·
      refine ⟨18368480285104937438821625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12245653523403291625881083 18368480285104937438821625)
      ·
        refine ⟨13776360213828703079116219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18368480285104937438821625 13776360213828703079116219)
        ·
          refine ⟨20664540320743054618674329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13776360213828703079116219 20664540320743054618674329)
          ·
            refine ⟨15498405240557290964005747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20664540320743054618674329 15498405240557290964005747)
            ·
              refine ⟨23247607860835936446008621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15498405240557290964005747 23247607860835936446008621)
              ·
                refine ⟨8717852947813476167253233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23247607860835936446008621 8717852947813476167253233)
                ·
                  refine ⟨6538389710860107125439925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8717852947813476167253233 6538389710860107125439925)
                  ·
                    refine ⟨612974035393135043009993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6538389710860107125439925 612974035393135043009993)
                    ·
                      refine ⟨459730526544851282257495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 612974035393135043009993 459730526544851282257495)
                      ·
                        rfl

theorem cell23_895322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 2, 5, 2].length) (baseStart_895322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895322 prefixEnd_895322 := by exact prefixLift 895322
  have htrace : WordTrace (prefixWord ++ tailWord_895322) baseStart_895322 baseEnd_895322 := by
    simpa [prefixWord, tailWord_895322, baseEnd_895322] using wordTrace_append hprefix tailTrace_895322
  have hstable : (prefixWord ++ tailWord_895322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895322).length < 2 ^ (prefixWord ++ tailWord_895322).sum := by decide
  have hdescent : baseEnd_895322 < baseStart_895322 := by decide
  rcases family_descends (prefixWord ++ tailWord_895322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895330 : List Nat := [3, 3, 2, 1, 1, 4, 2, 1, 2, 2, 2]
def baseStart_895330 : Nat := 118140960795 + 895330 * 2 ^ 59
def prefixEnd_895330 : Nat := 4983230072969 + 3 ^ 40 * 895330 * 2
def baseEnd_895330 : Nat := 459734634390087250957459

theorem tailTrace_895330 : CollatzResearch.WordTrace tailWord_895330 prefixEnd_895330 459734634390087250957459 := by
  unfold tailWord_895330
  simp only [CollatzResearch.WordTrace]
  refine ⟨8163841961594948758826861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21770245230919863356871629 8163841961594948758826861)
  ·
    refine ⟨3061440735598105784560073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8163841961594948758826861 3061440735598105784560073)
    ·
      refine ⟨2296080551698579338420055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3061440735598105784560073 2296080551698579338420055)
      ·
        refine ⟨3444120827547869007630083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2296080551698579338420055 3444120827547869007630083)
        ·
          refine ⟨5166181241321803511445125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3444120827547869007630083 5166181241321803511445125)
          ·
            refine ⟨968658982747838158395961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5166181241321803511445125 968658982747838158395961)
            ·
              refine ⟨726494237060878618796971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 968658982747838158395961 726494237060878618796971)
              ·
                refine ⟨1089741355591317928195457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 726494237060878618796971 1089741355591317928195457)
                ·
                  refine ⟨817306016693488446146593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1089741355591317928195457 817306016693488446146593)
                  ·
                    refine ⟨612979512520116334609945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 817306016693488446146593 612979512520116334609945)
                    ·
                      refine ⟨459734634390087250957459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 612979512520116334609945 459734634390087250957459)
                      ·
                        rfl

theorem cell23_895330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_895330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895330 prefixEnd_895330 := by exact prefixLift 895330
  have htrace : WordTrace (prefixWord ++ tailWord_895330) baseStart_895330 baseEnd_895330 := by
    simpa [prefixWord, tailWord_895330, baseEnd_895330] using wordTrace_append hprefix tailTrace_895330
  have hstable : (prefixWord ++ tailWord_895330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895330).length < 2 ^ (prefixWord ++ tailWord_895330).sum := by decide
  have hdescent : baseEnd_895330 < baseStart_895330 := by decide
  rcases family_descends (prefixWord ++ tailWord_895330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895349 : List Nat := [1, 3, 4, 1, 2, 2, 2, 1, 2, 5]
def baseStart_895349 : Nat := 118140960795 + 895349 * 2 ^ 59
def prefixEnd_895349 : Nat := 4983230072969 + 3 ^ 40 * 895349 * 2
def baseEnd_895349 : Nat := 153248130174174225539957

theorem tailTrace_895349 : CollatzResearch.WordTrace tailWord_895349 prefixEnd_895349 153248130174174225539957 := by
  unfold tailWord_895349
  simp only [CollatzResearch.WordTrace]
  refine ⟨32656060833310961280249101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21770707222207307520166067 32656060833310961280249101)
  ·
    refine ⟨12246022812491610480093413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32656060833310961280249101 12246022812491610480093413)
    ·
      refine ⟨2296129277342176965017515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12246022812491610480093413 2296129277342176965017515)
      ·
        refine ⟨3444193916013265447526273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2296129277342176965017515 3444193916013265447526273)
        ·
          refine ⟨2583145437009949085644705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3444193916013265447526273 2583145437009949085644705)
          ·
            refine ⟨1937359077757461814233529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2583145437009949085644705 1937359077757461814233529)
            ·
              refine ⟨1453019308318096360675147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1937359077757461814233529 1453019308318096360675147)
              ·
                refine ⟨2179528962477144541012721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1453019308318096360675147 2179528962477144541012721)
                ·
                  refine ⟨1634646721857858405759541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2179528962477144541012721 1634646721857858405759541)
                  ·
                    refine ⟨153248130174174225539957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1634646721857858405759541 153248130174174225539957)
                    ·
                      rfl

theorem cell23_895349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_895349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895349 prefixEnd_895349 := by exact prefixLift 895349
  have htrace : WordTrace (prefixWord ++ tailWord_895349) baseStart_895349 baseEnd_895349 := by
    simpa [prefixWord, tailWord_895349, baseEnd_895349] using wordTrace_append hprefix tailTrace_895349
  have hstable : (prefixWord ++ tailWord_895349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895349).length < 2 ^ (prefixWord ++ tailWord_895349).sum := by decide
  have hdescent : baseEnd_895349 < baseStart_895349 := by decide
  rcases family_descends (prefixWord ++ tailWord_895349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895365 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 2, 1, 6]
def baseStart_895365 : Nat := 118140960795 + 895365 * 2 ^ 59
def prefixEnd_895365 : Nat := 4983230072969 + 3 ^ 40 * 895365 * 2
def baseEnd_895365 : Nat := 459752606212994614019797

theorem tailTrace_895365 : CollatzResearch.WordTrace tailWord_895365 prefixEnd_895365 459752606212994614019797 := by
  unfold tailWord_895365
  simp only [CollatzResearch.WordTrace]
  refine ⟨32656644401252996012831549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21771096267501997341887699 32656644401252996012831549)
  ·
    refine ⟨12246241650469873504811831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32656644401252996012831549 12246241650469873504811831)
    ·
      refine ⟨18369362475704810257217747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12246241650469873504811831 18369362475704810257217747)
      ·
        refine ⟨27554043713557215385826621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18369362475704810257217747 27554043713557215385826621)
        ·
          refine ⟨10332766392583955769684983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27554043713557215385826621 10332766392583955769684983)
          ·
            refine ⟨15499149588875933654527475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10332766392583955769684983 15499149588875933654527475)
            ·
              refine ⟨23248724383313900481791213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15499149588875933654527475 23248724383313900481791213)
              ·
                refine ⟨8718271643742712680671705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23248724383313900481791213 8718271643742712680671705)
                ·
                  refine ⟨6538703732807034510503779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8718271643742712680671705 6538703732807034510503779)
                  ·
                    refine ⟨9808055599210551765755669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6538703732807034510503779 9808055599210551765755669)
                    ·
                      refine ⟨459752606212994614019797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9808055599210551765755669 459752606212994614019797)
                      ·
                        rfl

theorem cell23_895365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_895365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895365 prefixEnd_895365 := by exact prefixLift 895365
  have htrace : WordTrace (prefixWord ++ tailWord_895365) baseStart_895365 baseEnd_895365 := by
    simpa [prefixWord, tailWord_895365, baseEnd_895365] using wordTrace_append hprefix tailTrace_895365
  have hstable : (prefixWord ++ tailWord_895365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895365).length < 2 ^ (prefixWord ++ tailWord_895365).sum := by decide
  have hdescent : baseEnd_895365 < baseStart_895365 := by decide
  rcases family_descends (prefixWord ++ tailWord_895365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895370 : List Nat := [3, 1, 2, 5, 2, 1, 2, 2, 5]
def baseStart_895370 : Nat := 118140960795 + 895370 * 2 ^ 59
def prefixEnd_895370 : Nat := 4983230072969 + 3 ^ 40 * 895370 * 2
def baseEnd_895370 : Nat := 51083908179585232717475

theorem tailTrace_895370 : CollatzResearch.WordTrace tailWord_895370 prefixEnd_895370 51083908179585232717475 := by
  unfold tailWord_895370
  simp only [CollatzResearch.WordTrace]
  refine ⟨8164206691558720466690891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21771217844156587911175709 8164206691558720466690891)
  ·
    refine ⟨12246310037338080700036337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8164206691558720466690891 12246310037338080700036337)
    ·
      refine ⟨9184732528003560525027253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12246310037338080700036337 9184732528003560525027253)
      ·
        refine ⟨861068674500333799221305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9184732528003560525027253 861068674500333799221305)
        ·
          refine ⟨645801505875250349415979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 861068674500333799221305 645801505875250349415979)
          ·
            refine ⟨968702258812875524123969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645801505875250349415979 968702258812875524123969)
            ·
              refine ⟨726526694109656643092977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 968702258812875524123969 726526694109656643092977)
              ·
                refine ⟨544895020582242482319733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 726526694109656643092977 544895020582242482319733)
                ·
                  refine ⟨51083908179585232717475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 544895020582242482319733 51083908179585232717475)
                  ·
                    rfl

theorem cell23_895370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 2, 5].length) (baseStart_895370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895370 prefixEnd_895370 := by exact prefixLift 895370
  have htrace : WordTrace (prefixWord ++ tailWord_895370) baseStart_895370 baseEnd_895370 := by
    simpa [prefixWord, tailWord_895370, baseEnd_895370] using wordTrace_append hprefix tailTrace_895370
  have hstable : (prefixWord ++ tailWord_895370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895370).length < 2 ^ (prefixWord ++ tailWord_895370).sum := by decide
  have hdescent : baseEnd_895370 < baseStart_895370 := by decide
  rcases family_descends (prefixWord ++ tailWord_895370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895392 : List Nat := [2, 1, 1, 4, 1, 3, 2, 3, 6]
def baseStart_895392 : Nat := 118140960795 + 895392 * 2 ^ 59
def prefixEnd_895392 : Nat := 4983230072969 + 3 ^ 40 * 895392 * 2
def baseEnd_895392 : Nat := 51085163354518445375797

theorem tailTrace_895392 : CollatzResearch.WordTrace tailWord_895392 prefixEnd_895392 51085163354518445375797 := by
  unfold tailWord_895392
  simp only [CollatzResearch.WordTrace]
  refine ⟨16328814586077589812032215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21771752781436786416042953 16328814586077589812032215)
  ·
    refine ⟨24493221879116384718048323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16328814586077589812032215 24493221879116384718048323)
    ·
      refine ⟨36739832818674577077072485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24493221879116384718048323 36739832818674577077072485)
      ·
        refine ⟨6888718653501483201951091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36739832818674577077072485 6888718653501483201951091)
        ·
          refine ⟨10333077980252224802926637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6888718653501483201951091 10333077980252224802926637)
          ·
            refine ⟨3874904242594584301097489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10333077980252224802926637 3874904242594584301097489)
            ·
              refine ⟨2906178181945938225823117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3874904242594584301097489 2906178181945938225823117)
              ·
                refine ⟨1089816818229726834683669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2906178181945938225823117 1089816818229726834683669)
                ·
                  refine ⟨51085163354518445375797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1089816818229726834683669 51085163354518445375797)
                  ·
                    rfl

theorem cell23_895392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 6].length) (baseStart_895392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895392 prefixEnd_895392 := by exact prefixLift 895392
  have htrace : WordTrace (prefixWord ++ tailWord_895392) baseStart_895392 baseEnd_895392 := by
    simpa [prefixWord, tailWord_895392, baseEnd_895392] using wordTrace_append hprefix tailTrace_895392
  have hstable : (prefixWord ++ tailWord_895392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895392).length < 2 ^ (prefixWord ++ tailWord_895392).sum := by decide
  have hdescent : baseEnd_895392 < baseStart_895392 := by decide
  rcases family_descends (prefixWord ++ tailWord_895392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895413 : List Nat := [1, 3, 3, 2, 3, 1, 2, 3, 1, 4]
def baseStart_895413 : Nat := 118140960795 + 895413 * 2 ^ 59
def prefixEnd_895413 : Nat := 4983230072969 + 3 ^ 40 * 895413 * 2
def baseEnd_895413 : Nat := 153259084428136808739859

theorem tailTrace_895413 : CollatzResearch.WordTrace tailWord_895413 prefixEnd_895413 153259084428136808739859 := by
  unfold tailWord_895413
  simp only [CollatzResearch.WordTrace]
  refine ⟨32658395105079100210578893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21772263403386066807052595 32658395105079100210578893)
  ·
    refine ⟨12246898164404662578967085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32658395105079100210578893 12246898164404662578967085)
    ·
      refine ⟨4592586811651748467112657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12246898164404662578967085 4592586811651748467112657)
      ·
        refine ⟨3444440108738811350334493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4592586811651748467112657 3444440108738811350334493)
        ·
          refine ⟨1291665040777054256375435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3444440108738811350334493 1291665040777054256375435)
          ·
            refine ⟨1937497561165581384563153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1291665040777054256375435 1937497561165581384563153)
            ·
              refine ⟨1453123170874186038422365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1937497561165581384563153 1453123170874186038422365)
              ·
                refine ⟨544921189077819764408387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1453123170874186038422365 544921189077819764408387)
                ·
                  refine ⟨817381783616729646612581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 544921189077819764408387 817381783616729646612581)
                  ·
                    refine ⟨153259084428136808739859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 817381783616729646612581 153259084428136808739859)
                    ·
                      rfl

theorem cell23_895413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_895413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895413 prefixEnd_895413 := by exact prefixLift 895413
  have htrace : WordTrace (prefixWord ++ tailWord_895413) baseStart_895413 baseEnd_895413 := by
    simpa [prefixWord, tailWord_895413, baseEnd_895413] using wordTrace_append hprefix tailTrace_895413
  have hstable : (prefixWord ++ tailWord_895413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895413).length < 2 ^ (prefixWord ++ tailWord_895413).sum := by decide
  have hdescent : baseEnd_895413 < baseStart_895413 := by decide
  rcases family_descends (prefixWord ++ tailWord_895413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895446 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2]
def baseStart_895446 : Nat := 118140960795 + 895446 * 2 ^ 59
def prefixEnd_895446 : Nat := 4983230072969 + 3 ^ 40 * 895446 * 2
def baseEnd_895446 : Nat := 459794198146008797106925

theorem tailTrace_895446 : CollatzResearch.WordTrace tailWord_895446 prefixEnd_895446 459794198146008797106925 := by
  unfold tailWord_895446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2041224919622471677908137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21773065809306364564353461 2041224919622471677908137)
  ·
    refine ⟨1530918689716853758431103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2041224919622471677908137 1530918689716853758431103)
    ·
      refine ⟨2296378034575280637646655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1530918689716853758431103 2296378034575280637646655)
      ·
        refine ⟨3444567051862920956469983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2296378034575280637646655 3444567051862920956469983)
        ·
          refine ⟨5166850577794381434704975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3444567051862920956469983 5166850577794381434704975)
          ·
            refine ⟨7750275866691572152057463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5166850577794381434704975 7750275866691572152057463)
            ·
              refine ⟨11625413800037358228086195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7750275866691572152057463 11625413800037358228086195)
              ·
                refine ⟨17438120700056037342129293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11625413800037358228086195 17438120700056037342129293)
                ·
                  refine ⟨6539295262521014003298485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17438120700056037342129293 6539295262521014003298485)
                  ·
                    refine ⟨613058930861345062809233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6539295262521014003298485 613058930861345062809233)
                    ·
                      refine ⟨459794198146008797106925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 613058930861345062809233 459794198146008797106925)
                      ·
                        rfl

theorem cell23_895446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_895446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895446 prefixEnd_895446 := by exact prefixLift 895446
  have htrace : WordTrace (prefixWord ++ tailWord_895446) baseStart_895446 baseEnd_895446 := by
    simpa [prefixWord, tailWord_895446, baseEnd_895446] using wordTrace_append hprefix tailTrace_895446
  have hstable : (prefixWord ++ tailWord_895446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895446).length < 2 ^ (prefixWord ++ tailWord_895446).sum := by decide
  have hdescent : baseEnd_895446 < baseStart_895446 := by decide
  rcases family_descends (prefixWord ++ tailWord_895446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895470 : List Nat := [4, 1, 2, 1, 2, 4, 1, 3, 1, 1, 3]
def baseStart_895470 : Nat := 118140960795 + 895470 * 2 ^ 59
def prefixEnd_895470 : Nat := 4983230072969 + 3 ^ 40 * 895470 * 2
def baseEnd_895470 : Nat := 459806521681716703206815

theorem tailTrace_895470 : CollatzResearch.WordTrace tailWord_895470 prefixEnd_895470 459806521681716703206815 := by
  unfold tailWord_895470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4082559258234074868175483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21773649377248399296935909 4082559258234074868175483)
  ·
    refine ⟨6123838887351112302263225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4082559258234074868175483 6123838887351112302263225)
    ·
      refine ⟨4592879165513334226697419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6123838887351112302263225 4592879165513334226697419)
      ·
        refine ⟨6889318748270001340046129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4592879165513334226697419 6889318748270001340046129)
        ·
          refine ⟨5166989061202501005034597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6889318748270001340046129 5166989061202501005034597)
          ·
            refine ⟨968810448975468938443987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5166989061202501005034597 968810448975468938443987)
            ·
              refine ⟨1453215673463203407665981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 968810448975468938443987 1453215673463203407665981)
              ·
                refine ⟨544955877548701277874743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1453215673463203407665981 544955877548701277874743)
                ·
                  refine ⟨817433816323051916812115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 544955877548701277874743 817433816323051916812115)
                  ·
                    refine ⟨1226150724484577875218173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 817433816323051916812115 1226150724484577875218173)
                    ·
                      refine ⟨459806521681716703206815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1226150724484577875218173 459806521681716703206815)
                      ·
                        rfl

theorem cell23_895470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_895470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895470 prefixEnd_895470 := by exact prefixLift 895470
  have htrace : WordTrace (prefixWord ++ tailWord_895470) baseStart_895470 baseEnd_895470 := by
    simpa [prefixWord, tailWord_895470, baseEnd_895470] using wordTrace_append hprefix tailTrace_895470
  have hstable : (prefixWord ++ tailWord_895470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895470).length < 2 ^ (prefixWord ++ tailWord_895470).sum := by decide
  have hdescent : baseEnd_895470 < baseStart_895470 := by decide
  rcases family_descends (prefixWord ++ tailWord_895470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895472 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 4]
def baseStart_895472 : Nat := 118140960795 + 895472 * 2 ^ 59
def prefixEnd_895472 : Nat := 4983230072969 + 3 ^ 40 * 895472 * 2
def baseEnd_895472 : Nat := 459807548643025695381805

theorem tailTrace_895472 : CollatzResearch.WordTrace tailWord_895472 prefixEnd_895472 459807548643025695381805 := by
  unfold tailWord_895472
  simp only [CollatzResearch.WordTrace]
  refine ⟨16330273505932676643488335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21773698007910235524651113 16330273505932676643488335)
  ·
    refine ⟨24495410258899014965232503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16330273505932676643488335 24495410258899014965232503)
    ·
      refine ⟨36743115388348522447848755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24495410258899014965232503 36743115388348522447848755)
      ·
        refine ⟨55114673082522783671773133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36743115388348522447848755 55114673082522783671773133)
        ·
          refine ⟨20668002405946043876914925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55114673082522783671773133 20668002405946043876914925)
          ·
            refine ⟨7750500902229766453843097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20668002405946043876914925 7750500902229766453843097)
            ·
              refine ⟨5812875676672324840382323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7750500902229766453843097 5812875676672324840382323)
              ·
                refine ⟨8719313515008487260573485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5812875676672324840382323 8719313515008487260573485)
                ·
                  refine ⟨3269742568128182722715057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8719313515008487260573485 3269742568128182722715057)
                  ·
                    refine ⟨2452306926096137042036293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3269742568128182722715057 2452306926096137042036293)
                    ·
                      refine ⟨459807548643025695381805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2452306926096137042036293 459807548643025695381805)
                      ·
                        rfl

theorem cell23_895472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 4].length) (baseStart_895472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895472 prefixEnd_895472 := by exact prefixLift 895472
  have htrace : WordTrace (prefixWord ++ tailWord_895472) baseStart_895472 baseEnd_895472 := by
    simpa [prefixWord, tailWord_895472, baseEnd_895472] using wordTrace_append hprefix tailTrace_895472
  have hstable : (prefixWord ++ tailWord_895472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895472).length < 2 ^ (prefixWord ++ tailWord_895472).sum := by decide
  have hdescent : baseEnd_895472 < baseStart_895472 := by decide
  rcases family_descends (prefixWord ++ tailWord_895472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895493 : List Nat := [1, 3, 1, 1, 2, 2, 2, 6, 1, 2, 2]
def baseStart_895493 : Nat := 118140960795 + 895493 * 2 ^ 59
def prefixEnd_895493 : Nat := 4983230072969 + 3 ^ 40 * 895493 * 2
def baseEnd_895493 : Nat := 459818331736770113219209

theorem tailTrace_895493 : CollatzResearch.WordTrace tailWord_895493 prefixEnd_895493 459818331736770113219209 := by
  unfold tailWord_895493
  simp only [CollatzResearch.WordTrace]
  refine ⟨32661312944789273873491133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21774208629859515915660755 32661312944789273873491133)
  ·
    refine ⟨12247992354295977702559175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32661312944789273873491133 12247992354295977702559175)
    ·
      refine ⟨18371988531443966553838763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12247992354295977702559175 18371988531443966553838763)
      ·
        refine ⟨27557982797165949830758145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18371988531443966553838763 27557982797165949830758145)
        ·
          refine ⟨20668487097874462373068609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27557982797165949830758145 20668487097874462373068609)
          ·
            refine ⟨15501365323405846779801457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20668487097874462373068609 15501365323405846779801457)
            ·
              refine ⟨11626023992554385084851093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15501365323405846779801457 11626023992554385084851093)
              ·
                refine ⟨544969874650986800852395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11626023992554385084851093 544969874650986800852395)
                ·
                  refine ⟨817454811976480201278593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 544969874650986800852395 817454811976480201278593)
                  ·
                    refine ⟨613091108982360150958945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 817454811976480201278593 613091108982360150958945)
                    ·
                      refine ⟨459818331736770113219209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 613091108982360150958945 459818331736770113219209)
                      ·
                        rfl

theorem cell23_895493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 6, 1, 2, 2].length) (baseStart_895493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895493 prefixEnd_895493 := by exact prefixLift 895493
  have htrace : WordTrace (prefixWord ++ tailWord_895493) baseStart_895493 baseEnd_895493 := by
    simpa [prefixWord, tailWord_895493, baseEnd_895493] using wordTrace_append hprefix tailTrace_895493
  have hstable : (prefixWord ++ tailWord_895493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895493).length < 2 ^ (prefixWord ++ tailWord_895493).sum := by decide
  have hdescent : baseEnd_895493 < baseStart_895493 := by decide
  rcases family_descends (prefixWord ++ tailWord_895493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895509 : List Nat := [1, 3, 2, 1, 3, 1, 2, 3, 1, 3, 3]
def baseStart_895509 : Nat := 118140960795 + 895509 * 2 ^ 59
def prefixEnd_895509 : Nat := 4983230072969 + 3 ^ 40 * 895509 * 2
def baseEnd_895509 : Nat := 459826547427242050619135

theorem tailTrace_895509 : CollatzResearch.WordTrace tailWord_895509 prefixEnd_895509 459826547427242050619135 := by
  unfold tailWord_895509
  simp only [CollatzResearch.WordTrace]
  refine ⟨32661896512731308606073581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21774597675154205737382387 32661896512731308606073581)
  ·
    refine ⟨12248211192274240727277593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32661896512731308606073581 12248211192274240727277593)
    ·
      refine ⟨9186158394205680545458195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12248211192274240727277593 9186158394205680545458195)
      ·
        refine ⟨13779237591308520818187293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9186158394205680545458195 13779237591308520818187293)
        ·
          refine ⟨5167214096740695306820235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13779237591308520818187293 5167214096740695306820235)
          ·
            refine ⟨7750821145111042960230353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5167214096740695306820235 7750821145111042960230353)
            ·
              refine ⟨5813115858833282220172765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7750821145111042960230353 5813115858833282220172765)
              ·
                refine ⟨2179918447062480832564787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5813115858833282220172765 2179918447062480832564787)
                ·
                  refine ⟨3269877670593721248847181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2179918447062480832564787 3269877670593721248847181)
                  ·
                    refine ⟨1226204126472645468317693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3269877670593721248847181 1226204126472645468317693)
                    ·
                      refine ⟨459826547427242050619135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1226204126472645468317693 459826547427242050619135)
                      ·
                        rfl

theorem cell23_895509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_895509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895509 prefixEnd_895509 := by exact prefixLift 895509
  have htrace : WordTrace (prefixWord ++ tailWord_895509) baseStart_895509 baseEnd_895509 := by
    simpa [prefixWord, tailWord_895509, baseEnd_895509] using wordTrace_append hprefix tailTrace_895509
  have hstable : (prefixWord ++ tailWord_895509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895509).length < 2 ^ (prefixWord ++ tailWord_895509).sum := by decide
  have hdescent : baseEnd_895509 < baseStart_895509 := by decide
  rcases family_descends (prefixWord ++ tailWord_895509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895532 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 4]
def baseStart_895532 : Nat := 118140960795 + 895532 * 2 ^ 59
def prefixEnd_895532 : Nat := 4983230072969 + 3 ^ 40 * 895532 * 2
def baseEnd_895532 : Nat := 459838357482295460631529

theorem tailTrace_895532 : CollatzResearch.WordTrace tailWord_895532 prefixEnd_895532 459838357482295460631529 := by
  unfold tailWord_895532
  simp only [CollatzResearch.WordTrace]
  refine ⟨16331367695823991767080425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21775156927765322356107233 16331367695823991767080425)
  ·
    refine ⟨12248525771867993825310319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16331367695823991767080425 12248525771867993825310319)
    ·
      refine ⟨18372788657801990737965479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12248525771867993825310319 18372788657801990737965479)
      ·
        refine ⟨27559182986702986106948219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18372788657801990737965479 27559182986702986106948219)
        ·
          refine ⟨41338774480054479160422329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27559182986702986106948219 41338774480054479160422329)
          ·
            refine ⟨31004080860040859370316747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41338774480054479160422329 31004080860040859370316747)
            ·
              refine ⟨46506121290061289055475121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31004080860040859370316747 46506121290061289055475121)
              ·
                refine ⟨34879590967545966791606341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46506121290061289055475121 34879590967545966791606341)
                ·
                  refine ⟨6539923306414868773426189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34879590967545966791606341 6539923306414868773426189)
                  ·
                    refine ⟨2452471239905575790034821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6539923306414868773426189 2452471239905575790034821)
                    ·
                      refine ⟨459838357482295460631529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2452471239905575790034821 459838357482295460631529)
                      ·
                        rfl

theorem cell23_895532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_895532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895532 prefixEnd_895532 := by exact prefixLift 895532
  have htrace : WordTrace (prefixWord ++ tailWord_895532) baseStart_895532 baseEnd_895532 := by
    simpa [prefixWord, tailWord_895532, baseEnd_895532] using wordTrace_append hprefix tailTrace_895532
  have hstable : (prefixWord ++ tailWord_895532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895532).length < 2 ^ (prefixWord ++ tailWord_895532).sum := by decide
  have hdescent : baseEnd_895532 < baseStart_895532 := by decide
  rcases family_descends (prefixWord ++ tailWord_895532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895533 : List Nat := [1, 5, 4, 1, 2, 10]
def baseStart_895533 : Nat := 118140960795 + 895533 * 2 ^ 59
def prefixEnd_895533 : Nat := 4983230072969 + 3 ^ 40 * 895533 * 2
def baseEnd_895533 : Nat := 1892341032769341385675

theorem tailTrace_895533 : CollatzResearch.WordTrace tailWord_895533 prefixEnd_895533 1892341032769341385675 := by
  unfold tailWord_895533
  simp only [CollatzResearch.WordTrace]
  refine ⟨32662771864644360704947253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21775181243096240469964835 32662771864644360704947253)
  ·
    refine ⟨3062134862310408816088805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32662771864644360704947253 3062134862310408816088805)
    ·
      refine ⟨574150286683201653016651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3062134862310408816088805 574150286683201653016651)
      ·
        refine ⟨861225430024802479524977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574150286683201653016651 861225430024802479524977)
        ·
          refine ⟨645919072518601859643733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 861225430024802479524977 645919072518601859643733)
          ·
            refine ⟨1892341032769341385675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 645919072518601859643733 1892341032769341385675)
            ·
              rfl

theorem cell23_895533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 10].length) (baseStart_895533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895533 prefixEnd_895533 := by exact prefixLift 895533
  have htrace : WordTrace (prefixWord ++ tailWord_895533) baseStart_895533 baseEnd_895533 := by
    simpa [prefixWord, tailWord_895533, baseEnd_895533] using wordTrace_append hprefix tailTrace_895533
  have hstable : (prefixWord ++ tailWord_895533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895533).length < 2 ^ (prefixWord ++ tailWord_895533).sum := by decide
  have hdescent : baseEnd_895533 < baseStart_895533 := by decide
  rcases family_descends (prefixWord ++ tailWord_895533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895536 : List Nat := [2, 1, 1, 1, 2, 3, 2, 5, 1, 3, 2]
def baseStart_895536 : Nat := 118140960795 + 895536 * 2 ^ 59
def prefixEnd_895536 : Nat := 4983230072969 + 3 ^ 40 * 895536 * 2
def baseEnd_895536 : Nat := 459840411404913444981511

theorem tailTrace_895536 : CollatzResearch.WordTrace tailWord_895536 prefixEnd_895536 459840411404913444981511 := by
  unfold tailWord_895536
  simp only [CollatzResearch.WordTrace]
  refine ⟨16331440641816746108653231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21775254189088994811537641 16331440641816746108653231)
  ·
    refine ⟨24497160962725119162979847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16331440641816746108653231 24497160962725119162979847)
    ·
      refine ⟨36745741444087678744469771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24497160962725119162979847 36745741444087678744469771)
      ·
        refine ⟨55118612166131518116704657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36745741444087678744469771 55118612166131518116704657)
        ·
          refine ⟨41338959124598638587528493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55118612166131518116704657 41338959124598638587528493)
          ·
            refine ⟨15502109671724489470323185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41338959124598638587528493 15502109671724489470323185)
            ·
              refine ⟨11626582253793367102742389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15502109671724489470323185 11626582253793367102742389)
              ·
                refine ⟨1089992086293128165882099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11626582253793367102742389 1089992086293128165882099)
                ·
                  refine ⟨1634988129439692248823149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1089992086293128165882099 1634988129439692248823149)
                  ·
                    refine ⟨613120548539884593308681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1634988129439692248823149 613120548539884593308681)
                    ·
                      refine ⟨459840411404913444981511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 613120548539884593308681 459840411404913444981511)
                      ·
                        rfl

theorem cell23_895536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 1, 3, 2].length) (baseStart_895536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895536 prefixEnd_895536 := by exact prefixLift 895536
  have htrace : WordTrace (prefixWord ++ tailWord_895536) baseStart_895536 baseEnd_895536 := by
    simpa [prefixWord, tailWord_895536, baseEnd_895536] using wordTrace_append hprefix tailTrace_895536
  have hstable : (prefixWord ++ tailWord_895536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895536).length < 2 ^ (prefixWord ++ tailWord_895536).sum := by decide
  have hdescent : baseEnd_895536 < baseStart_895536 := by decide
  rcases family_descends (prefixWord ++ tailWord_895536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895549 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 2, 3, 4]
def baseStart_895549 : Nat := 118140960795 + 895549 * 2 ^ 59
def prefixEnd_895549 : Nat := 4983230072969 + 3 ^ 40 * 895549 * 2
def baseEnd_895549 : Nat := 459847086653421894118951

theorem tailTrace_895549 : CollatzResearch.WordTrace tailWord_895549 prefixEnd_895549 459847086653421894118951 := by
  unfold tailWord_895549
  simp only [CollatzResearch.WordTrace]
  refine ⟨32663355432586395437529701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21775570288390930291686467 32663355432586395437529701)
  ·
    refine ⟨6124379143609949144536819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32663355432586395437529701 6124379143609949144536819)
    ·
      refine ⟨9186568715414923716805229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6124379143609949144536819 9186568715414923716805229)
      ·
        refine ⟨3444963268280596393801961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9186568715414923716805229 3444963268280596393801961)
        ·
          refine ⟨2583722451210447295351471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3444963268280596393801961 2583722451210447295351471)
          ·
            refine ⟨3875583676815670943027207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2583722451210447295351471 3875583676815670943027207)
            ·
              refine ⟨5813375515223506414540811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3875583676815670943027207 5813375515223506414540811)
              ·
                refine ⟨8720063272835259621811217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5813375515223506414540811 8720063272835259621811217)
                ·
                  refine ⟨6540047454626444716358413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8720063272835259621811217 6540047454626444716358413)
                  ·
                    refine ⟨2452517795484916768634405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6540047454626444716358413 2452517795484916768634405)
                    ·
                      refine ⟨459847086653421894118951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2452517795484916768634405 459847086653421894118951)
                      ·
                        rfl

theorem cell23_895549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_895549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895549 prefixEnd_895549 := by exact prefixLift 895549
  have htrace : WordTrace (prefixWord ++ tailWord_895549) baseStart_895549 baseEnd_895549 := by
    simpa [prefixWord, tailWord_895549, baseEnd_895549] using wordTrace_append hprefix tailTrace_895549
  have hstable : (prefixWord ++ tailWord_895549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895549).length < 2 ^ (prefixWord ++ tailWord_895549).sum := by decide
  have hdescent : baseEnd_895549 < baseStart_895549 := by decide
  rcases family_descends (prefixWord ++ tailWord_895549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895552 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 5]
def baseStart_895552 : Nat := 118140960795 + 895552 * 2 ^ 59
def prefixEnd_895552 : Nat := 4983230072969 + 3 ^ 40 * 895552 * 2
def baseEnd_895552 : Nat := 459848627095385382381437

theorem tailTrace_895552 : CollatzResearch.WordTrace tailWord_895552 prefixEnd_895552 459848627095385382381437 := by
  unfold tailWord_895552
  simp only [CollatzResearch.WordTrace]
  refine ⟨16331732425787763474944455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21775643234383684633259273 16331732425787763474944455)
  ·
    refine ⟨24497598638681645212416683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16331732425787763474944455 24497598638681645212416683)
    ·
      refine ⟨36746397958022467818625025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24497598638681645212416683 36746397958022467818625025)
      ·
        refine ⟨27559798468516850863968769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36746397958022467818625025 27559798468516850863968769)
        ·
          refine ⟨20669848851387638147976577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27559798468516850863968769 20669848851387638147976577)
          ·
            refine ⟨15502386638540728610982433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20669848851387638147976577 15502386638540728610982433)
            ·
              refine ⟨11626789978905546458236825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15502386638540728610982433 11626789978905546458236825)
              ·
                refine ⟨8720092484179159843677619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11626789978905546458236825 8720092484179159843677619)
                ·
                  refine ⟨13080138726268739765516429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8720092484179159843677619 13080138726268739765516429)
                  ·
                    refine ⟨4905052022350777412068661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13080138726268739765516429 4905052022350777412068661)
                    ·
                      refine ⟨459848627095385382381437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4905052022350777412068661 459848627095385382381437)
                      ·
                        rfl

theorem cell23_895552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_895552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895552 prefixEnd_895552 := by exact prefixLift 895552
  have htrace : WordTrace (prefixWord ++ tailWord_895552) baseStart_895552 baseEnd_895552 := by
    simpa [prefixWord, tailWord_895552, baseEnd_895552] using wordTrace_append hprefix tailTrace_895552
  have hstable : (prefixWord ++ tailWord_895552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895552).length < 2 ^ (prefixWord ++ tailWord_895552).sum := by decide
  have hdescent : baseEnd_895552 < baseStart_895552 := by decide
  rcases family_descends (prefixWord ++ tailWord_895552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895559 : List Nat := [1, 1, 4, 1, 4, 2, 1, 1, 2, 6]
def baseStart_895559 : Nat := 118140960795 + 895559 * 2 ^ 59
def prefixEnd_895559 : Nat := 4983230072969 + 3 ^ 40 * 895559 * 2
def baseEnd_895559 : Nat := 153284073819988951664635

theorem tailTrace_895559 : CollatzResearch.WordTrace tailWord_895559 prefixEnd_895559 153284073819988951664635 := by
  unfold tailWord_895559
  simp only [CollatzResearch.WordTrace]
  refine ⟨32663720162550167145393731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21775813441700111430262487 32663720162550167145393731)
  ·
    refine ⟨48995580243825250718090597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32663720162550167145393731 48995580243825250718090597)
    ·
      refine ⟨9186671295717234509641987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48995580243825250718090597 9186671295717234509641987)
      ·
        refine ⟨13780006943575851764462981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9186671295717234509641987 13780006943575851764462981)
        ·
          refine ⟨2583751301920472205836809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13780006943575851764462981 2583751301920472205836809)
          ·
            refine ⟨1937813476440354154377607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2583751301920472205836809 1937813476440354154377607)
            ·
              refine ⟨2906720214660531231566411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1937813476440354154377607 2906720214660531231566411)
              ·
                refine ⟨4360080321990796847349617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2906720214660531231566411 4360080321990796847349617)
                ·
                  refine ⟨3270060241493097635512213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4360080321990796847349617 3270060241493097635512213)
                  ·
                    refine ⟨153284073819988951664635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3270060241493097635512213 153284073819988951664635)
                    ·
                      rfl

theorem cell23_895559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_895559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895559 prefixEnd_895559 := by exact prefixLift 895559
  have htrace : WordTrace (prefixWord ++ tailWord_895559) baseStart_895559 baseEnd_895559 := by
    simpa [prefixWord, tailWord_895559, baseEnd_895559] using wordTrace_append hprefix tailTrace_895559
  have hstable : (prefixWord ++ tailWord_895559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895559).length < 2 ^ (prefixWord ++ tailWord_895559).sum := by decide
  have hdescent : baseEnd_895559 < baseStart_895559 := by decide
  rcases family_descends (prefixWord ++ tailWord_895559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895566 : List Nat := [4, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2]
def baseStart_895566 : Nat := 118140960795 + 895566 * 2 ^ 59
def prefixEnd_895566 : Nat := 4983230072969 + 3 ^ 40 * 895566 * 2
def baseEnd_895566 : Nat := 459855815824548327606373

theorem tailTrace_895566 : CollatzResearch.WordTrace tailWord_895566 prefixEnd_895566 459855815824548327606373 := by
  unfold tailWord_895566
  simp only [CollatzResearch.WordTrace]
  refine ⟨4082996934190600917612319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21775983649016538227265701 4082996934190600917612319)
  ·
    refine ⟨6124495401285901376418479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4082996934190600917612319 6124495401285901376418479)
    ·
      refine ⟨9186743101928852064627719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6124495401285901376418479 9186743101928852064627719)
      ·
        refine ⟨13780114652893278096941579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9186743101928852064627719 13780114652893278096941579)
        ·
          refine ⟨20670171979339917145412369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13780114652893278096941579 20670171979339917145412369)
          ·
            refine ⟨15502628984504937859059277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20670171979339917145412369 15502628984504937859059277)
            ·
              refine ⟨5813485869189351697147229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15502628984504937859059277 5813485869189351697147229)
              ·
                refine ⟨2180057200946006886430211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5813485869189351697147229 2180057200946006886430211)
                ·
                  refine ⟨3270085801419010329645317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2180057200946006886430211 3270085801419010329645317)
                  ·
                    refine ⟨613141087766064436808497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3270085801419010329645317 613141087766064436808497)
                    ·
                      refine ⟨459855815824548327606373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 613141087766064436808497 459855815824548327606373)
                      ·
                        rfl

theorem cell23_895566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2].length) (baseStart_895566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895566 prefixEnd_895566 := by exact prefixLift 895566
  have htrace : WordTrace (prefixWord ++ tailWord_895566) baseStart_895566 baseEnd_895566 := by
    simpa [prefixWord, tailWord_895566, baseEnd_895566] using wordTrace_append hprefix tailTrace_895566
  have hstable : (prefixWord ++ tailWord_895566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895566).length < 2 ^ (prefixWord ++ tailWord_895566).sum := by decide
  have hdescent : baseEnd_895566 < baseStart_895566 := by decide
  rcases family_descends (prefixWord ++ tailWord_895566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895599 : List Nat := [1, 1, 2, 1, 3, 2, 3, 2, 2, 3, 3]
def baseStart_895599 : Nat := 118140960795 + 895599 * 2 ^ 59
def prefixEnd_895599 : Nat := 4983230072969 + 3 ^ 40 * 895599 * 2
def baseEnd_895599 : Nat := 459872760686146698493721

theorem tailTrace_895599 : CollatzResearch.WordTrace tailWord_895599 prefixEnd_895599 459872760686146698493721 := by
  unfold tailWord_895599
  simp only [CollatzResearch.WordTrace]
  refine ⟨32665179082405253976849851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21776786054936835984566567 32665179082405253976849851)
  ·
    refine ⟨48997768623607880965274777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32665179082405253976849851 48997768623607880965274777)
    ·
      refine ⟨36748326467705910723956083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48997768623607880965274777 36748326467705910723956083)
      ·
        refine ⟨55122489701558866085934125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36748326467705910723956083 55122489701558866085934125)
        ·
          refine ⟨20670933638084574782225297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55122489701558866085934125 20670933638084574782225297)
          ·
            refine ⟨15503200228563431086668973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20670933638084574782225297 15503200228563431086668973)
            ·
              refine ⟨5813700085711286657500865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15503200228563431086668973 5813700085711286657500865)
              ·
                refine ⟨4360275064283464993125649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5813700085711286657500865 4360275064283464993125649)
                ·
                  refine ⟨3270206298212598744844237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4360275064283464993125649 3270206298212598744844237)
                  ·
                    refine ⟨1226327361829724529316589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3270206298212598744844237 1226327361829724529316589)
                    ·
                      refine ⟨459872760686146698493721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1226327361829724529316589 459872760686146698493721)
                      ·
                        rfl

theorem cell23_895599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 3, 3].length) (baseStart_895599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895599 prefixEnd_895599 := by exact prefixLift 895599
  have htrace : WordTrace (prefixWord ++ tailWord_895599) baseStart_895599 baseEnd_895599 := by
    simpa [prefixWord, tailWord_895599, baseEnd_895599] using wordTrace_append hprefix tailTrace_895599
  have hstable : (prefixWord ++ tailWord_895599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895599).length < 2 ^ (prefixWord ++ tailWord_895599).sum := by decide
  have hdescent : baseEnd_895599 < baseStart_895599 := by decide
  rcases family_descends (prefixWord ++ tailWord_895599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895636 : List Nat := [2, 4, 2, 2, 1, 1, 2, 1, 1, 7]
def baseStart_895636 : Nat := 118140960795 + 895636 * 2 ^ 59
def prefixEnd_895636 : Nat := 4983230072969 + 3 ^ 40 * 895636 * 2
def baseEnd_895636 : Nat := 153297253156787684577017

theorem tailTrace_895636 : CollatzResearch.WordTrace tailWord_895636 prefixEnd_895636 153297253156787684577017 := by
  unfold tailWord_895636
  simp only [CollatzResearch.WordTrace]
  refine ⟨16333264291635604647973381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21777685722180806197297841 16333264291635604647973381)
  ·
    refine ⟨3062487054681675871495009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16333264291635604647973381 3062487054681675871495009)
    ·
      refine ⟨2296865291011256903621257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3062487054681675871495009 2296865291011256903621257)
      ·
        refine ⟨1722648968258442677715943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2296865291011256903621257 1722648968258442677715943)
        ·
          refine ⟨2583973452387664016573915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1722648968258442677715943 2583973452387664016573915)
          ·
            refine ⟨3875960178581496024860873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2583973452387664016573915 3875960178581496024860873)
            ·
              refine ⟨2906970133936122018645655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3875960178581496024860873 2906970133936122018645655)
              ·
                refine ⟨4360455200904183027968483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2906970133936122018645655 4360455200904183027968483)
                ·
                  refine ⟨6540682801356274541952725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4360455200904183027968483 6540682801356274541952725)
                  ·
                    refine ⟨153297253156787684577017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6540682801356274541952725 153297253156787684577017)
                    ·
                      rfl

theorem cell23_895636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_895636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895636 prefixEnd_895636 := by exact prefixLift 895636
  have htrace : WordTrace (prefixWord ++ tailWord_895636) baseStart_895636 baseEnd_895636 := by
    simpa [prefixWord, tailWord_895636, baseEnd_895636] using wordTrace_append hprefix tailTrace_895636
  have hstable : (prefixWord ++ tailWord_895636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895636).length < 2 ^ (prefixWord ++ tailWord_895636).sum := by decide
  have hdescent : baseEnd_895636 < baseStart_895636 := by decide
  rcases family_descends (prefixWord ++ tailWord_895636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895639 : List Nat := [1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 4]
def baseStart_895639 : Nat := 118140960795 + 895639 * 2 ^ 59
def prefixEnd_895639 : Nat := 4983230072969 + 3 ^ 40 * 895639 * 2
def baseEnd_895639 : Nat := 459893299912326541993537

theorem tailTrace_895639 : CollatzResearch.WordTrace tailWord_895639 prefixEnd_895639 459893299912326541993537 := by
  unfold tailWord_895639
  simp only [CollatzResearch.WordTrace]
  refine ⟨32666638002260340808305971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21777758668173560538870647 32666638002260340808305971)
  ·
    refine ⟨48999957003390511212458957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32666638002260340808305971 48999957003390511212458957)
    ·
      refine ⟨18374983876271441704672109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48999957003390511212458957 18374983876271441704672109)
      ·
        refine ⟨6890618953601790639252041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18374983876271441704672109 6890618953601790639252041)
        ·
          refine ⟨5167964215201342979439031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6890618953601790639252041 5167964215201342979439031)
          ·
            refine ⟨7751946322802014469158547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5167964215201342979439031 7751946322802014469158547)
            ·
              refine ⟨11627919484203021703737821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7751946322802014469158547 11627919484203021703737821)
              ·
                refine ⟨4360469806576133138901683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11627919484203021703737821 4360469806576133138901683)
                ·
                  refine ⟨6540704709864199708352525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4360469806576133138901683 6540704709864199708352525)
                  ·
                    refine ⟨2452764266199074890632197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6540704709864199708352525 2452764266199074890632197)
                    ·
                      refine ⟨459893299912326541993537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2452764266199074890632197 459893299912326541993537)
                      ·
                        rfl

theorem cell23_895639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_895639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895639 prefixEnd_895639 := by exact prefixLift 895639
  have htrace : WordTrace (prefixWord ++ tailWord_895639) baseStart_895639 baseEnd_895639 := by
    simpa [prefixWord, tailWord_895639, baseEnd_895639] using wordTrace_append hprefix tailTrace_895639
  have hstable : (prefixWord ++ tailWord_895639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895639).length < 2 ^ (prefixWord ++ tailWord_895639).sum := by decide
  have hdescent : baseEnd_895639 < baseStart_895639 := by decide
  rcases family_descends (prefixWord ++ tailWord_895639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895646 : List Nat := [4, 3, 1, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_895646 : Nat := 118140960795 + 895646 * 2 ^ 59
def prefixEnd_895646 : Nat := 4983230072969 + 3 ^ 40 * 895646 * 2
def baseEnd_895646 : Nat := 459896894276908014606005

theorem tailTrace_895646 : CollatzResearch.WordTrace tailWord_895646 prefixEnd_895646 459896894276908014606005 := by
  unfold tailWord_895646
  simp only [CollatzResearch.WordTrace]
  refine ⟨4083361664154372625476349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21777928875489987335873861 4083361664154372625476349)
  ·
    refine ⟨1531260624057889734553631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4083361664154372625476349 1531260624057889734553631)
    ·
      refine ⟨2296890936086834601830447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1531260624057889734553631 2296890936086834601830447)
      ·
        refine ⟨3445336404130251902745671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2296890936086834601830447 3445336404130251902745671)
        ·
          refine ⟨5168004606195377854118507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3445336404130251902745671 5168004606195377854118507)
          ·
            refine ⟨7752006909293066781177761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5168004606195377854118507 7752006909293066781177761)
            ·
              refine ⟨5814005181969800085883321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7752006909293066781177761 5814005181969800085883321)
              ·
                refine ⟨4360503886477350064412491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5814005181969800085883321 4360503886477350064412491)
                ·
                  refine ⟨6540755829716025096618737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4360503886477350064412491 6540755829716025096618737)
                  ·
                    refine ⟨4905566872287018822464053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6540755829716025096618737 4905566872287018822464053)
                    ·
                      refine ⟨459896894276908014606005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4905566872287018822464053 459896894276908014606005)
                      ·
                        rfl

theorem cell23_895646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_895646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895646 prefixEnd_895646 := by exact prefixLift 895646
  have htrace : WordTrace (prefixWord ++ tailWord_895646) baseStart_895646 baseEnd_895646 := by
    simpa [prefixWord, tailWord_895646, baseEnd_895646] using wordTrace_append hprefix tailTrace_895646
  have hstable : (prefixWord ++ tailWord_895646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895646).length < 2 ^ (prefixWord ++ tailWord_895646).sum := by decide
  have hdescent : baseEnd_895646 < baseStart_895646 := by decide
  rcases family_descends (prefixWord ++ tailWord_895646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895676 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 4, 2, 3]
def baseStart_895676 : Nat := 118140960795 + 895676 * 2 ^ 59
def prefixEnd_895676 : Nat := 4983230072969 + 3 ^ 40 * 895676 * 2
def baseEnd_895676 : Nat := 459912298696542897230867

theorem tailTrace_895676 : CollatzResearch.WordTrace tailWord_895676 prefixEnd_895676 459912298696542897230867 := by
  unfold tailWord_895676
  simp only [CollatzResearch.WordTrace]
  refine ⟨16333993751563148063701441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21778658335417530751601921 16333993751563148063701441)
  ·
    refine ⟨12250495313672361047776081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16333993751563148063701441 12250495313672361047776081)
    ·
      refine ⟨9187871485254270785832061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12250495313672361047776081 9187871485254270785832061)
      ·
        refine ⟨3445451806970351544687023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9187871485254270785832061 3445451806970351544687023)
        ·
          refine ⟨5168177710455527317030535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3445451806970351544687023 5168177710455527317030535)
          ·
            refine ⟨7752266565683290975545803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5168177710455527317030535 7752266565683290975545803)
            ·
              refine ⟨11628399848524936463318705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7752266565683290975545803 11628399848524936463318705)
              ·
                refine ⟨8721299886393702347489029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11628399848524936463318705 8721299886393702347489029)
                ·
                  refine ⟨1635243728698819190154193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8721299886393702347489029 1635243728698819190154193)
                  ·
                    refine ⟨1226432796524114392615645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1635243728698819190154193 1226432796524114392615645)
                    ·
                      refine ⟨459912298696542897230867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1226432796524114392615645 459912298696542897230867)
                      ·
                        rfl

theorem cell23_895676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_895676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895676 prefixEnd_895676 := by exact prefixLift 895676
  have htrace : WordTrace (prefixWord ++ tailWord_895676) baseStart_895676 baseEnd_895676 := by
    simpa [prefixWord, tailWord_895676, baseEnd_895676] using wordTrace_append hprefix tailTrace_895676
  have hstable : (prefixWord ++ tailWord_895676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895676).length < 2 ^ (prefixWord ++ tailWord_895676).sum := by decide
  have hdescent : baseEnd_895676 < baseStart_895676 := by decide
  rcases family_descends (prefixWord ++ tailWord_895676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895717 : List Nat := [1, 3, 1, 4, 1, 4, 2, 2, 1, 4]
def baseStart_895717 : Nat := 118140960795 + 895717 * 2 ^ 59
def prefixEnd_895717 : Nat := 4983230072969 + 3 ^ 40 * 895717 * 2
def baseEnd_895717 : Nat := 153311117134459078939393

theorem tailTrace_895717 : CollatzResearch.WordTrace tailWord_895717 prefixEnd_895717 153311117134459078939393 := by
  unfold tailWord_895717
  simp only [CollatzResearch.WordTrace]
  refine ⟨32669482895977760129645405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21779655263985173419763603 32669482895977760129645405)
  ·
    refine ⟨12251056085991660048617027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32669482895977760129645405 12251056085991660048617027)
    ·
      refine ⟨18376584128987490072925541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12251056085991660048617027 18376584128987490072925541)
      ·
        refine ⟨3445609524185154388673539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18376584128987490072925541 3445609524185154388673539)
        ·
          refine ⟨5168414286277731583010309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3445609524185154388673539 5168414286277731583010309)
          ·
            refine ⟨969077678677074671814433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5168414286277731583010309 969077678677074671814433)
            ·
              refine ⟨726808259007806003860825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 969077678677074671814433 726808259007806003860825)
              ·
                refine ⟨545106194255854502895619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 726808259007806003860825 545106194255854502895619)
                ·
                  refine ⟨817659291383781754343429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 545106194255854502895619 817659291383781754343429)
                  ·
                    refine ⟨153311117134459078939393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 817659291383781754343429 153311117134459078939393)
                    ·
                      rfl

theorem cell23_895717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 2, 1, 4].length) (baseStart_895717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895717 prefixEnd_895717 := by exact prefixLift 895717
  have htrace : WordTrace (prefixWord ++ tailWord_895717) baseStart_895717 baseEnd_895717 := by
    simpa [prefixWord, tailWord_895717, baseEnd_895717] using wordTrace_append hprefix tailTrace_895717
  have hstable : (prefixWord ++ tailWord_895717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895717).length < 2 ^ (prefixWord ++ tailWord_895717).sum := by decide
  have hdescent : baseEnd_895717 < baseStart_895717 := by decide
  rcases family_descends (prefixWord ++ tailWord_895717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895726 : List Nat := [4, 1, 2, 1, 1, 3, 1, 2, 3, 5]
def baseStart_895726 : Nat := 118140960795 + 895726 * 2 ^ 59
def prefixEnd_895726 : Nat := 4983230072969 + 3 ^ 40 * 895726 * 2
def baseEnd_895726 : Nat := 153312657576422567201879

theorem tailTrace_895726 : CollatzResearch.WordTrace tailWord_895726 prefixEnd_895726 153312657576422567201879 := by
  unfold tailWord_895726
  simp only [CollatzResearch.WordTrace]
  refine ⟨4083726394118144333340379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21779874101963436444482021 4083726394118144333340379)
  ·
    refine ⟨6125589591177216500010569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4083726394118144333340379 6125589591177216500010569)
    ·
      refine ⟨4594192193382912375007927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6125589591177216500010569 4594192193382912375007927)
      ·
        refine ⟨6891288290074368562511891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4594192193382912375007927 6891288290074368562511891)
        ·
          refine ⟨10336932435111552843767837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6891288290074368562511891 10336932435111552843767837)
          ·
            refine ⟨3876349663166832316412939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10336932435111552843767837 3876349663166832316412939)
            ·
              refine ⟨5814524494750248474619409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3876349663166832316412939 5814524494750248474619409)
              ·
                refine ⟨4360893371062686355964557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5814524494750248474619409 4360893371062686355964557)
                ·
                  refine ⟨1635335014148507383486709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4360893371062686355964557 1635335014148507383486709)
                  ·
                    refine ⟨153312657576422567201879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1635335014148507383486709 153312657576422567201879)
                    ·
                      rfl

theorem cell23_895726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_895726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895726 prefixEnd_895726 := by exact prefixLift 895726
  have htrace : WordTrace (prefixWord ++ tailWord_895726) baseStart_895726 baseEnd_895726 := by
    simpa [prefixWord, tailWord_895726, baseEnd_895726] using wordTrace_append hprefix tailTrace_895726
  have hstable : (prefixWord ++ tailWord_895726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895726).length < 2 ^ (prefixWord ++ tailWord_895726).sum := by decide
  have hdescent : baseEnd_895726 < baseStart_895726 := by decide
  rcases family_descends (prefixWord ++ tailWord_895726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895756 : List Nat := [2, 2, 1, 2, 2, 1, 1, 4, 4, 4]
def baseStart_895756 : Nat := 118140960795 + 895756 * 2 ^ 59
def prefixEnd_895756 : Nat := 4983230072969 + 3 ^ 40 * 895756 * 2
def baseEnd_895756 : Nat := 153317792382967528076833

theorem tailTrace_895756 : CollatzResearch.WordTrace tailWord_895756 prefixEnd_895756 153317792382967528076833 := by
  unfold tailWord_895756
  simp only [CollatzResearch.WordTrace]
  refine ⟨16335452671418234895157561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21780603561890979860210081 16335452671418234895157561)
  ·
    refine ⟨12251589503563676171368171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16335452671418234895157561 12251589503563676171368171)
    ·
      refine ⟨18377384255345514257052257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12251589503563676171368171 18377384255345514257052257)
      ·
        refine ⟨13783038191509135692789193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18377384255345514257052257 13783038191509135692789193)
        ·
          refine ⟨10337278643631851769591895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13783038191509135692789193 10337278643631851769591895)
          ·
            refine ⟨15505917965447777654387843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10337278643631851769591895 15505917965447777654387843)
            ·
              refine ⟨23258876948171666481581765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15505917965447777654387843 23258876948171666481581765)
              ·
                refine ⟨4361039427782187465296581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23258876948171666481581765 4361039427782187465296581)
                ·
                  refine ⟨817694892709160149743109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4361039427782187465296581 817694892709160149743109)
                  ·
                    refine ⟨153317792382967528076833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 817694892709160149743109 153317792382967528076833)
                    ·
                      rfl

theorem cell23_895756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 4, 4].length) (baseStart_895756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895756 prefixEnd_895756 := by exact prefixLift 895756
  have htrace : WordTrace (prefixWord ++ tailWord_895756) baseStart_895756 baseEnd_895756 := by
    simpa [prefixWord, tailWord_895756, baseEnd_895756] using wordTrace_append hprefix tailTrace_895756
  have hstable : (prefixWord ++ tailWord_895756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895756).length < 2 ^ (prefixWord ++ tailWord_895756).sum := by decide
  have hdescent : baseEnd_895756 < baseStart_895756 := by decide
  rcases family_descends (prefixWord ++ tailWord_895756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895763 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 5, 2, 2]
def baseStart_895763 : Nat := 118140960795 + 895763 * 2 ^ 59
def prefixEnd_895763 : Nat := 4983230072969 + 3 ^ 40 * 895763 * 2
def baseEnd_895763 : Nat := 459956971513484056842967

theorem tailTrace_895763 : CollatzResearch.WordTrace tailWord_895763 prefixEnd_895763 459956971513484056842967 := by
  unfold tailWord_895763
  simp only [CollatzResearch.WordTrace]
  refine ⟨32671160653811109985819943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21780773769207406657213295 32671160653811109985819943)
  ·
    refine ⟨49006740980716664978729915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32671160653811109985819943 49006740980716664978729915)
    ·
      refine ⟨73510111471074997468094873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49006740980716664978729915 73510111471074997468094873)
      ·
        refine ⟨55132583603306248101071155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73510111471074997468094873 55132583603306248101071155)
        ·
          refine ⟨82698875404959372151606733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55132583603306248101071155 82698875404959372151606733)
          ·
            refine ⟨31012078276859764556852525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82698875404959372151606733 31012078276859764556852525)
            ·
              refine ⟨11629529353822411708819697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31012078276859764556852525 11629529353822411708819697)
              ·
                refine ⟨8722147015366808781614773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11629529353822411708819697 8722147015366808781614773)
                ·
                  refine ⟨817701282690638323276385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8722147015366808781614773 817701282690638323276385)
                  ·
                    refine ⟨613275962017978742457289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 817701282690638323276385 613275962017978742457289)
                    ·
                      refine ⟨459956971513484056842967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 613275962017978742457289 459956971513484056842967)
                      ·
                        rfl

theorem cell23_895763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 5, 2, 2].length) (baseStart_895763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895763 prefixEnd_895763 := by exact prefixLift 895763
  have htrace : WordTrace (prefixWord ++ tailWord_895763) baseStart_895763 baseEnd_895763 := by
    simpa [prefixWord, tailWord_895763, baseEnd_895763] using wordTrace_append hprefix tailTrace_895763
  have hstable : (prefixWord ++ tailWord_895763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895763).length < 2 ^ (prefixWord ++ tailWord_895763).sum := by decide
  have hdescent : baseEnd_895763 < baseStart_895763 := by decide
  rcases family_descends (prefixWord ++ tailWord_895763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895779 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 7]
def baseStart_895779 : Nat := 118140960795 + 895779 * 2 ^ 59
def prefixEnd_895779 : Nat := 4983230072969 + 3 ^ 40 * 895779 * 2
def baseEnd_895779 : Nat := 459965187203955994242893

theorem tailTrace_895779 : CollatzResearch.WordTrace tailWord_895779 prefixEnd_895779 459965187203955994242893 := by
  unfold tailWord_895779
  simp only [CollatzResearch.WordTrace]
  refine ⟨32671744221753144718402391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21781162814502096478934927 32671744221753144718402391)
  ·
    refine ⟨49007616332629717077603587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32671744221753144718402391 49007616332629717077603587)
    ·
      refine ⟨73511424498944575616405381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49007616332629717077603587 73511424498944575616405381)
      ·
        refine ⟨13783392093552107928076009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73511424498944575616405381 13783392093552107928076009)
        ·
          refine ⟨10337544070164080946057007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13783392093552107928076009 10337544070164080946057007)
          ·
            refine ⟨15506316105246121419085511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10337544070164080946057007 15506316105246121419085511)
            ·
              refine ⟨23259474157869182128628267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15506316105246121419085511 23259474157869182128628267)
              ·
                refine ⟨34889211236803773192942401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23259474157869182128628267 34889211236803773192942401)
                ·
                  refine ⟨26166908427602829894706801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34889211236803773192942401 26166908427602829894706801)
                  ·
                    refine ⟨19625181320702122421030101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26166908427602829894706801 19625181320702122421030101)
                    ·
                      refine ⟨459965187203955994242893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19625181320702122421030101 459965187203955994242893)
                      ·
                        rfl

theorem cell23_895779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_895779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895779 prefixEnd_895779 := by exact prefixLift 895779
  have htrace : WordTrace (prefixWord ++ tailWord_895779) baseStart_895779 baseEnd_895779 := by
    simpa [prefixWord, tailWord_895779, baseEnd_895779] using wordTrace_append hprefix tailTrace_895779
  have hstable : (prefixWord ++ tailWord_895779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895779).length < 2 ^ (prefixWord ++ tailWord_895779).sum := by decide
  have hdescent : baseEnd_895779 < baseStart_895779 := by decide
  rcases family_descends (prefixWord ++ tailWord_895779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895790 : List Nat := [4, 1, 3, 2, 1, 3, 1, 1, 1, 6]
def baseStart_895790 : Nat := 118140960795 + 895790 * 2 ^ 59
def prefixEnd_895790 : Nat := 4983230072969 + 3 ^ 40 * 895790 * 2
def baseEnd_895790 : Nat := 153323611830385150401781

theorem tailTrace_895790 : CollatzResearch.WordTrace tailWord_895790 prefixEnd_895790 153323611830385150401781 := by
  unfold tailWord_895790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4084018178089161699631603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21781430283142195731368549 4084018178089161699631603)
  ·
    refine ⟨6126027267133742549447405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4084018178089161699631603 6126027267133742549447405)
    ·
      refine ⟨2297260225175153456042777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6126027267133742549447405 2297260225175153456042777)
      ·
        refine ⟨1722945168881365092032083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2297260225175153456042777 1722945168881365092032083)
        ·
          refine ⟨2584417753322047638048125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1722945168881365092032083 2584417753322047638048125)
          ·
            refine ⟨969156657495767864268047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2584417753322047638048125 969156657495767864268047)
            ·
              refine ⟨1453734986243651796402071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 969156657495767864268047 1453734986243651796402071)
              ·
                refine ⟨2180602479365477694603107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1453734986243651796402071 2180602479365477694603107)
                ·
                  refine ⟨3270903719048216541904661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2180602479365477694603107 3270903719048216541904661)
                  ·
                    refine ⟨153323611830385150401781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3270903719048216541904661 153323611830385150401781)
                    ·
                      rfl

theorem cell23_895790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_895790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895790 prefixEnd_895790 := by exact prefixLift 895790
  have htrace : WordTrace (prefixWord ++ tailWord_895790) baseStart_895790 baseEnd_895790 := by
    simpa [prefixWord, tailWord_895790, baseEnd_895790] using wordTrace_append hprefix tailTrace_895790
  have hstable : (prefixWord ++ tailWord_895790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895790).length < 2 ^ (prefixWord ++ tailWord_895790).sum := by decide
  have hdescent : baseEnd_895790 < baseStart_895790 := by decide
  rcases family_descends (prefixWord ++ tailWord_895790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895819 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 8]
def baseStart_895819 : Nat := 118140960795 + 895819 * 2 ^ 59
def prefixEnd_895819 : Nat := 4983230072969 + 3 ^ 40 * 895819 * 2
def baseEnd_895819 : Nat := 459985726430135837742709

theorem tailTrace_895819 : CollatzResearch.WordTrace tailWord_895819 prefixEnd_895819 459985726430135837742709 := by
  unfold tailWord_895819
  simp only [CollatzResearch.WordTrace]
  refine ⟨32673203141608231549858511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21782135427738821033239007 32673203141608231549858511)
  ·
    refine ⟨49009804712412347324787767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32673203141608231549858511 49009804712412347324787767)
    ·
      refine ⟨73514707068618520987181651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49009804712412347324787767 73514707068618520987181651)
      ·
        refine ⟨110272060602927781480772477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73514707068618520987181651 110272060602927781480772477)
        ·
          refine ⟨41352022726097918055289679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110272060602927781480772477 41352022726097918055289679)
          ·
            refine ⟨62028034089146877082934519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41352022726097918055289679 62028034089146877082934519)
            ·
              refine ⟨93042051133720315624401779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62028034089146877082934519 93042051133720315624401779)
              ·
                refine ⟨139563076700580473436602669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93042051133720315624401779 139563076700580473436602669)
                ·
                  refine ⟨52336153762717677538726001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139563076700580473436602669 52336153762717677538726001)
                  ·
                    refine ⟨39252115322038258154044501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52336153762717677538726001 39252115322038258154044501)
                    ·
                      refine ⟨459985726430135837742709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 39252115322038258154044501 459985726430135837742709)
                      ·
                        rfl

theorem cell23_895819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 8].length) (baseStart_895819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895819 prefixEnd_895819 := by exact prefixLift 895819
  have htrace : WordTrace (prefixWord ++ tailWord_895819) baseStart_895819 baseEnd_895819 := by
    simpa [prefixWord, tailWord_895819, baseEnd_895819] using wordTrace_append hprefix tailTrace_895819
  have hstable : (prefixWord ++ tailWord_895819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895819).length < 2 ^ (prefixWord ++ tailWord_895819).sum := by decide
  have hdescent : baseEnd_895819 < baseStart_895819 := by decide
  rcases family_descends (prefixWord ++ tailWord_895819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895826 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5]
def baseStart_895826 : Nat := 118140960795 + 895826 * 2 ^ 59
def prefixEnd_895826 : Nat := 4983230072969 + 3 ^ 40 * 895826 * 2
def baseEnd_895826 : Nat := 459989320794717310355177

theorem tailTrace_895826 : CollatzResearch.WordTrace tailWord_895826 prefixEnd_895826 459989320794717310355177 := by
  unfold tailWord_895826
  simp only [CollatzResearch.WordTrace]
  refine ⟨8168364613145717936340833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21782305635055247830242221 8168364613145717936340833)
  ·
    refine ⟨6126273459859288452255625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8168364613145717936340833 6126273459859288452255625)
    ·
      refine ⟨4594705094894466339191719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6126273459859288452255625 4594705094894466339191719)
      ·
        refine ⟨6892057642341699508787579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4594705094894466339191719 6892057642341699508787579)
        ·
          refine ⟨10338086463512549263181369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6892057642341699508787579 10338086463512549263181369)
          ·
            refine ⟨7753564847634411947386027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10338086463512549263181369 7753564847634411947386027)
            ·
              refine ⟨11630347271451617921079041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7753564847634411947386027 11630347271451617921079041)
              ·
                refine ⟨8722760453588713440809281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11630347271451617921079041 8722760453588713440809281)
                ·
                  refine ⟨6542070340191535080606961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8722760453588713440809281 6542070340191535080606961)
                  ·
                    refine ⟨4906552755143651310455221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6542070340191535080606961 4906552755143651310455221)
                    ·
                      refine ⟨459989320794717310355177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4906552755143651310455221 459989320794717310355177)
                      ·
                        rfl

theorem cell23_895826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_895826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895826 prefixEnd_895826 := by exact prefixLift 895826
  have htrace : WordTrace (prefixWord ++ tailWord_895826) baseStart_895826 baseEnd_895826 := by
    simpa [prefixWord, tailWord_895826, baseEnd_895826] using wordTrace_append hprefix tailTrace_895826
  have hstable : (prefixWord ++ tailWord_895826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895826).length < 2 ^ (prefixWord ++ tailWord_895826).sum := by decide
  have hdescent : baseEnd_895826 < baseStart_895826 := by decide
  rcases family_descends (prefixWord ++ tailWord_895826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895847 : List Nat := [1, 1, 5, 1, 2, 2, 4, 1, 2, 1, 3]
def baseStart_895847 : Nat := 118140960795 + 895847 * 2 ^ 59
def prefixEnd_895847 : Nat := 4983230072969 + 3 ^ 40 * 895847 * 2
def baseEnd_895847 : Nat := 460000103888461728192581

theorem tailTrace_895847 : CollatzResearch.WordTrace tailWord_895847 prefixEnd_895847 460000103888461728192581 := by
  unfold tailWord_895847
  simp only [CollatzResearch.WordTrace]
  refine ⟨32674224385506792331877795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21782816257004528221251863 32674224385506792331877795)
  ·
    refine ⟨49011336578260188497816693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32674224385506792331877795 49011336578260188497816693)
    ·
      refine ⟨4594812804211892671670315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49011336578260188497816693 4594812804211892671670315)
      ·
        refine ⟨6892219206317839007505473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4594812804211892671670315 6892219206317839007505473)
        ·
          refine ⟨5169164404738379255629105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6892219206317839007505473 5169164404738379255629105)
          ·
            refine ⟨3876873303553784441721829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5169164404738379255629105 3876873303553784441721829)
            ·
              refine ⟨726913744416334582822843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3876873303553784441721829 726913744416334582822843)
              ·
                refine ⟨1090370616624501874234265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 726913744416334582822843 1090370616624501874234265)
                ·
                  refine ⟨817777962468376405675699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1090370616624501874234265 817777962468376405675699)
                  ·
                    refine ⟨1226666943702564608513549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 817777962468376405675699 1226666943702564608513549)
                    ·
                      refine ⟨460000103888461728192581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1226666943702564608513549 460000103888461728192581)
                      ·
                        rfl

theorem cell23_895847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_895847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895847 prefixEnd_895847 := by exact prefixLift 895847
  have htrace : WordTrace (prefixWord ++ tailWord_895847) baseStart_895847 baseEnd_895847 := by
    simpa [prefixWord, tailWord_895847, baseEnd_895847] using wordTrace_append hprefix tailTrace_895847
  have hstable : (prefixWord ++ tailWord_895847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895847).length < 2 ^ (prefixWord ++ tailWord_895847).sum := by decide
  have hdescent : baseEnd_895847 < baseStart_895847 := by decide
  rcases family_descends (prefixWord ++ tailWord_895847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895856 : List Nat := [2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 5]
def baseStart_895856 : Nat := 118140960795 + 895856 * 2 ^ 59
def prefixEnd_895856 : Nat := 4983230072969 + 3 ^ 40 * 895856 * 2
def baseEnd_895856 : Nat := 460004725214352192980039

theorem tailTrace_895856 : CollatzResearch.WordTrace tailWord_895856 prefixEnd_895856 460004725214352192980039 := by
  unfold tailWord_895856
  simp only [CollatzResearch.WordTrace]
  refine ⟨16337276321237093434477711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21783035094982791245970281 16337276321237093434477711)
  ·
    refine ⟨24505914481855640151716567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16337276321237093434477711 24505914481855640151716567)
    ·
      refine ⟨36758871722783460227574851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24505914481855640151716567 36758871722783460227574851)
      ·
        refine ⟨55138307584175190341362277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36758871722783460227574851 55138307584175190341362277)
        ·
          refine ⟨10338432672032848189005427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55138307584175190341362277 10338432672032848189005427)
          ·
            refine ⟨15507649008049272283508141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10338432672032848189005427 15507649008049272283508141)
            ·
              refine ⟨5815368378018477106315553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15507649008049272283508141 5815368378018477106315553)
              ·
                refine ⟨4361526283513857829736665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5815368378018477106315553 4361526283513857829736665)
                ·
                  refine ⟨3271144712635393372302499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4361526283513857829736665 3271144712635393372302499)
                  ·
                    refine ⟨4906717068953090058453749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3271144712635393372302499 4906717068953090058453749)
                    ·
                      refine ⟨460004725214352192980039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4906717068953090058453749 460004725214352192980039)
                      ·
                        rfl

theorem cell23_895856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 5].length) (baseStart_895856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895856 prefixEnd_895856 := by exact prefixLift 895856
  have htrace : WordTrace (prefixWord ++ tailWord_895856) baseStart_895856 baseEnd_895856 := by
    simpa [prefixWord, tailWord_895856, baseEnd_895856] using wordTrace_append hprefix tailTrace_895856
  have hstable : (prefixWord ++ tailWord_895856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895856).length < 2 ^ (prefixWord ++ tailWord_895856).sum := by decide
  have hdescent : baseEnd_895856 < baseStart_895856 := by decide
  rcases family_descends (prefixWord ++ tailWord_895856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895857 : List Nat := [1, 2, 2, 2, 1, 6, 1, 2, 1, 3, 2]
def baseStart_895857 : Nat := 118140960795 + 895857 * 2 ^ 59
def prefixEnd_895857 : Nat := 4983230072969 + 3 ^ 40 * 895857 * 2
def baseEnd_895857 : Nat := 460005238695006689067535

theorem tailTrace_895857 : CollatzResearch.WordTrace tailWord_895857 prefixEnd_895857 460005238695006689067535 := by
  unfold tailWord_895857
  simp only [CollatzResearch.WordTrace]
  refine ⟨32674589115470564039741825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21783059410313709359827883 32674589115470564039741825)
  ·
    refine ⟨24505941836602923029806369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32674589115470564039741825 24505941836602923029806369)
    ·
      refine ⟨18379456377452192272354777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24505941836602923029806369 18379456377452192272354777)
      ·
        refine ⟨13784592283089144204266083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18379456377452192272354777 13784592283089144204266083)
        ·
          refine ⟨20676888424633716306399125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13784592283089144204266083 20676888424633716306399125)
          ·
            refine ⟨969229144904705451862459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20676888424633716306399125 969229144904705451862459)
            ·
              refine ⟨1453843717357058177793689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 969229144904705451862459 1453843717357058177793689)
              ·
                refine ⟨1090382788017793633345267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1453843717357058177793689 1090382788017793633345267)
                ·
                  refine ⟨1635574182026690450017901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1090382788017793633345267 1635574182026690450017901)
                  ·
                    refine ⟨613340318260008918756713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1635574182026690450017901 613340318260008918756713)
                    ·
                      refine ⟨460005238695006689067535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 613340318260008918756713 460005238695006689067535)
                      ·
                        rfl

theorem cell23_895857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 3, 2].length) (baseStart_895857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895857 prefixEnd_895857 := by exact prefixLift 895857
  have htrace : WordTrace (prefixWord ++ tailWord_895857) baseStart_895857 baseEnd_895857 := by
    simpa [prefixWord, tailWord_895857, baseEnd_895857] using wordTrace_append hprefix tailTrace_895857
  have hstable : (prefixWord ++ tailWord_895857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895857).length < 2 ^ (prefixWord ++ tailWord_895857).sum := by decide
  have hdescent : baseEnd_895857 < baseStart_895857 := by decide
  rcases family_descends (prefixWord ++ tailWord_895857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895866 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 4, 2, 4]
def baseStart_895866 : Nat := 118140960795 + 895866 * 2 ^ 59
def prefixEnd_895866 : Nat := 4983230072969 + 3 ^ 40 * 895866 * 2
def baseEnd_895866 : Nat := 460009860020897153854993

theorem tailTrace_895866 : CollatzResearch.WordTrace tailWord_895866 prefixEnd_895866 460009860020897153854993 := by
  unfold tailWord_895866
  simp only [CollatzResearch.WordTrace]
  refine ⟨8168729343109489644204863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21783278248291972384546301 8168729343109489644204863)
  ·
    refine ⟨12253094014664234466307295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8168729343109489644204863 12253094014664234466307295)
    ·
      refine ⟨18379641021996351699460943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12253094014664234466307295 18379641021996351699460943)
      ·
        refine ⟨27569461532994527549191415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18379641021996351699460943 27569461532994527549191415)
        ·
          refine ⟨41354192299491791323787123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27569461532994527549191415 41354192299491791323787123)
          ·
            refine ⟨62031288449237686985680685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41354192299491791323787123 62031288449237686985680685)
            ·
              refine ⟨23261733168464132619630257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62031288449237686985680685 23261733168464132619630257)
              ·
                refine ⟨17446299876348099464722693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23261733168464132619630257 17446299876348099464722693)
                ·
                  refine ⟨3271181226815268649635505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17446299876348099464722693 3271181226815268649635505)
                  ·
                    refine ⟨2453385920111451487226629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3271181226815268649635505 2453385920111451487226629)
                    ·
                      refine ⟨460009860020897153854993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2453385920111451487226629 460009860020897153854993)
                      ·
                        rfl

theorem cell23_895866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_895866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895866 prefixEnd_895866 := by exact prefixLift 895866
  have htrace : WordTrace (prefixWord ++ tailWord_895866) baseStart_895866 baseEnd_895866 := by
    simpa [prefixWord, tailWord_895866, baseEnd_895866] using wordTrace_append hprefix tailTrace_895866
  have hstable : (prefixWord ++ tailWord_895866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895866).length < 2 ^ (prefixWord ++ tailWord_895866).sum := by decide
  have hdescent : baseEnd_895866 < baseStart_895866 := by decide
  rcases family_descends (prefixWord ++ tailWord_895866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895900 : List Nat := [2, 2, 3, 3, 2, 1, 1, 1, 2, 2, 4]
def baseStart_895900 : Nat := 118140960795 + 895900 * 2 ^ 59
def prefixEnd_895900 : Nat := 4983230072969 + 3 ^ 40 * 895900 * 2
def baseEnd_895900 : Nat := 460027318363150020829837

theorem tailTrace_895900 : CollatzResearch.WordTrace tailWord_895900 prefixEnd_895900 460027318363150020829837 := by
  unfold tailWord_895900
  simp only [CollatzResearch.WordTrace]
  refine ⟨16338078727157391191778577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21784104969543188255704769 16338078727157391191778577)
  ·
    refine ⟨12253559045368043393833933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16338078727157391191778577 12253559045368043393833933)
    ·
      refine ⟨4595084642013016272687725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12253559045368043393833933 4595084642013016272687725)
      ·
        refine ⟨1723156740754881102257897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4595084642013016272687725 1723156740754881102257897)
        ·
          refine ⟨1292367555566160826693423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1723156740754881102257897 1292367555566160826693423)
          ·
            refine ⟨1938551333349241240040135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1292367555566160826693423 1938551333349241240040135)
            ·
              refine ⟨2907827000023861860060203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1938551333349241240040135 2907827000023861860060203)
              ·
                refine ⟨4361740500035792790090305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2907827000023861860060203 4361740500035792790090305)
                ·
                  refine ⟨3271305375026844592567729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4361740500035792790090305 3271305375026844592567729)
                  ·
                    refine ⟨2453479031270133444425797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3271305375026844592567729 2453479031270133444425797)
                    ·
                      refine ⟨460027318363150020829837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2453479031270133444425797 460027318363150020829837)
                      ·
                        rfl

theorem cell23_895900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_895900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895900 prefixEnd_895900 := by exact prefixLift 895900
  have htrace : WordTrace (prefixWord ++ tailWord_895900) baseStart_895900 baseEnd_895900 := by
    simpa [prefixWord, tailWord_895900, baseEnd_895900] using wordTrace_append hprefix tailTrace_895900
  have hstable : (prefixWord ++ tailWord_895900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895900).length < 2 ^ (prefixWord ++ tailWord_895900).sum := by decide
  have hdescent : baseEnd_895900 < baseStart_895900 := by decide
  rcases family_descends (prefixWord ++ tailWord_895900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895903 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 1, 5, 3]
def baseStart_895903 : Nat := 118140960795 + 895903 * 2 ^ 59
def prefixEnd_895903 : Nat := 4983230072969 + 3 ^ 40 * 895903 * 2
def baseEnd_895903 : Nat := 460028858805113509092323

theorem tailTrace_895903 : CollatzResearch.WordTrace tailWord_895903 prefixEnd_895903 460028858805113509092323 := by
  unfold tailWord_895903
  simp only [CollatzResearch.WordTrace]
  refine ⟨32676266873303913895916363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21784177915535942597277575 32676266873303913895916363)
  ·
    refine ⟨49014400309955870843874545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32676266873303913895916363 49014400309955870843874545)
    ·
      refine ⟨36760800232466903132905909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49014400309955870843874545 36760800232466903132905909)
      ·
        refine ⟨3446325021793772168709929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36760800232466903132905909 3446325021793772168709929)
        ·
          refine ⟨2584743766345329126532447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3446325021793772168709929 2584743766345329126532447)
          ·
            refine ⟨3877115649517993689798671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2584743766345329126532447 3877115649517993689798671)
            ·
              refine ⟨5815673474276990534698007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3877115649517993689798671 5815673474276990534698007)
              ·
                refine ⟨8723510211415485802047011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5815673474276990534698007 8723510211415485802047011)
                ·
                  refine ⟨13085265317123228703070517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8723510211415485802047011 13085265317123228703070517)
                  ·
                    refine ⟨1226743623480302690912861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13085265317123228703070517 1226743623480302690912861)
                    ·
                      refine ⟨460028858805113509092323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1226743623480302690912861 460028858805113509092323)
                      ·
                        rfl

theorem cell23_895903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_895903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895903 prefixEnd_895903 := by exact prefixLift 895903
  have htrace : WordTrace (prefixWord ++ tailWord_895903) baseStart_895903 baseEnd_895903 := by
    simpa [prefixWord, tailWord_895903, baseEnd_895903] using wordTrace_append hprefix tailTrace_895903
  have hstable : (prefixWord ++ tailWord_895903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895903).length < 2 ^ (prefixWord ++ tailWord_895903).sum := by decide
  have hdescent : baseEnd_895903 < baseStart_895903 := by decide
  rcases family_descends (prefixWord ++ tailWord_895903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895913 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 2, 5, 2]
def baseStart_895913 : Nat := 118140960795 + 895913 * 2 ^ 59
def prefixEnd_895913 : Nat := 4983230072969 + 3 ^ 40 * 895913 * 2
def baseEnd_895913 : Nat := 460033993611658469967277

theorem tailTrace_895913 : CollatzResearch.WordTrace tailWord_895913 prefixEnd_895913 460033993611658469967277 := by
  unfold tailWord_895913
  simp only [CollatzResearch.WordTrace]
  refine ⟨32676631603267685603780393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21784421068845123735853595 32676631603267685603780393)
  ·
    refine ⟨24507473702450764202835295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32676631603267685603780393 24507473702450764202835295)
    ·
      refine ⟨36761210553676146304252943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24507473702450764202835295 36761210553676146304252943)
      ·
        refine ⟨55141815830514219456379415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36761210553676146304252943 55141815830514219456379415)
        ·
          refine ⟨82712723745771329184569123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55141815830514219456379415 82712723745771329184569123)
          ·
            refine ⟨124069085618656993776853685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82712723745771329184569123 124069085618656993776853685)
            ·
              refine ⟨11631476776749093166580033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124069085618656993776853685 11631476776749093166580033)
              ·
                refine ⟨8723607582561819874935025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11631476776749093166580033 8723607582561819874935025)
                ·
                  refine ⟨6542705686921364906201269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8723607582561819874935025 6542705686921364906201269)
                  ·
                    refine ⟨613378658148877959956369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6542705686921364906201269 613378658148877959956369)
                    ·
                      refine ⟨460033993611658469967277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 613378658148877959956369 460033993611658469967277)
                      ·
                        rfl

theorem cell23_895913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 5, 2].length) (baseStart_895913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895913 prefixEnd_895913 := by exact prefixLift 895913
  have htrace : WordTrace (prefixWord ++ tailWord_895913) baseStart_895913 baseEnd_895913 := by
    simpa [prefixWord, tailWord_895913, baseEnd_895913] using wordTrace_append hprefix tailTrace_895913
  have hstable : (prefixWord ++ tailWord_895913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895913).length < 2 ^ (prefixWord ++ tailWord_895913).sum := by decide
  have hdescent : baseEnd_895913 < baseStart_895913 := by decide
  rcases family_descends (prefixWord ++ tailWord_895913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895943 : List Nat := [1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 4]
def baseStart_895943 : Nat := 118140960795 + 895943 * 2 ^ 59
def prefixEnd_895943 : Nat := 4983230072969 + 3 ^ 40 * 895943 * 2
def baseEnd_895943 : Nat := 460049398031293352592139

theorem tailTrace_895943 : CollatzResearch.WordTrace tailWord_895943 prefixEnd_895943 460049398031293352592139 := by
  unfold tailWord_895943
  simp only [CollatzResearch.WordTrace]
  refine ⟨32677725793159000727372483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21785150528772667151581655 32677725793159000727372483)
  ·
    refine ⟨49016588689738501091058725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32677725793159000727372483 49016588689738501091058725)
    ·
      refine ⟨9190610379325968954573511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49016588689738501091058725 9190610379325968954573511)
      ·
        refine ⟨13785915568988953431860267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9190610379325968954573511 13785915568988953431860267)
        ·
          refine ⟨20678873353483430147790401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13785915568988953431860267 20678873353483430147790401)
          ·
            refine ⟨15509155015112572610842801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20678873353483430147790401 15509155015112572610842801)
            ·
              refine ⟨11631866261334429458132101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15509155015112572610842801 11631866261334429458132101)
              ·
                refine ⟨2180974924000205523399769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11631866261334429458132101 2180974924000205523399769)
                ·
                  refine ⟨1635731193000154142549827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2180974924000205523399769 1635731193000154142549827)
                  ·
                    refine ⟨2453596789500231213824741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1635731193000154142549827 2453596789500231213824741)
                    ·
                      refine ⟨460049398031293352592139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2453596789500231213824741 460049398031293352592139)
                      ·
                        rfl

theorem cell23_895943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_895943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895943 prefixEnd_895943 := by exact prefixLift 895943
  have htrace : WordTrace (prefixWord ++ tailWord_895943) baseStart_895943 baseEnd_895943 := by
    simpa [prefixWord, tailWord_895943, baseEnd_895943] using wordTrace_append hprefix tailTrace_895943
  have hstable : (prefixWord ++ tailWord_895943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895943).length < 2 ^ (prefixWord ++ tailWord_895943).sum := by decide
  have hdescent : baseEnd_895943 < baseStart_895943 := by decide
  rcases family_descends (prefixWord ++ tailWord_895943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895960 : List Nat := [2, 1, 2, 2, 2, 3, 2, 1, 2, 4, 2]
def baseStart_895960 : Nat := 118140960795 + 895960 * 2 ^ 59
def prefixEnd_895960 : Nat := 4983230072969 + 3 ^ 40 * 895960 * 2
def baseEnd_895960 : Nat := 460058127202419786079561

theorem tailTrace_895960 : CollatzResearch.WordTrace tailWord_895960 prefixEnd_895960 460058127202419786079561 := by
  unfold tailWord_895960
  simp only [CollatzResearch.WordTrace]
  refine ⟨16339172917048706315370667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21785563889398275087160889 16339172917048706315370667)
  ·
    refine ⟨24508759375573059473056001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16339172917048706315370667 24508759375573059473056001)
    ·
      refine ⟨18381569531679794604792001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24508759375573059473056001 18381569531679794604792001)
      ·
        refine ⟨13786177148759845953594001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18381569531679794604792001 13786177148759845953594001)
        ·
          refine ⟨10339632861569884465195501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13786177148759845953594001 10339632861569884465195501)
          ·
            refine ⟨3877362323088706674448313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10339632861569884465195501 3877362323088706674448313)
            ·
              refine ⟨2908021742316530005836235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3877362323088706674448313 2908021742316530005836235)
              ·
                refine ⟨4362032613474795008754353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2908021742316530005836235 4362032613474795008754353)
                ·
                  refine ⟨3271524460106096256565765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4362032613474795008754353 3271524460106096256565765)
                  ·
                    refine ⟨613410836269893048106081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3271524460106096256565765 613410836269893048106081)
                    ·
                      refine ⟨460058127202419786079561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 613410836269893048106081 460058127202419786079561)
                      ·
                        rfl

theorem cell23_895960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 2, 4, 2].length) (baseStart_895960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_895960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_895960 prefixEnd_895960 := by exact prefixLift 895960
  have htrace : WordTrace (prefixWord ++ tailWord_895960) baseStart_895960 baseEnd_895960 := by
    simpa [prefixWord, tailWord_895960, baseEnd_895960] using wordTrace_append hprefix tailTrace_895960
  have hstable : (prefixWord ++ tailWord_895960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895960).length < 2 ^ (prefixWord ++ tailWord_895960).sum := by decide
  have hdescent : baseEnd_895960 < baseStart_895960 := by decide
  rcases family_descends (prefixWord ++ tailWord_895960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896037 : List Nat := [1, 3, 1, 2, 2, 2, 4, 1, 2, 3, 2]
def baseStart_896037 : Nat := 118140960795 + 896037 * 2 ^ 59
def prefixEnd_896037 : Nat := 4983230072969 + 3 ^ 40 * 896037 * 2
def baseEnd_896037 : Nat := 460097665212815984816707

theorem tailTrace_896037 : CollatzResearch.WordTrace tailWord_896037 prefixEnd_896037 460097665212815984816707 := by
  unfold tailWord_896037
  simp only [CollatzResearch.WordTrace]
  refine ⟨32681154254818454781294365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21787436169878969854196243 32681154254818454781294365)
  ·
    refine ⟨12255432845556920542985387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32681154254818454781294365 12255432845556920542985387)
    ·
      refine ⟨18383149268335380814478081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12255432845556920542985387 18383149268335380814478081)
      ·
        refine ⟨13787361951251535610858561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18383149268335380814478081 13787361951251535610858561)
        ·
          refine ⟨10340521463438651708143921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13787361951251535610858561 10340521463438651708143921)
          ·
            refine ⟨7755391097578988781107941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10340521463438651708143921 7755391097578988781107941)
            ·
              refine ⟨1454135830796060396457739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7755391097578988781107941 1454135830796060396457739)
              ·
                refine ⟨2181203746194090594686609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1454135830796060396457739 2181203746194090594686609)
                ·
                  refine ⟨1635902809645567946014957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2181203746194090594686609 1635902809645567946014957)
                  ·
                    refine ⟨613463553617087979755609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1635902809645567946014957 613463553617087979755609)
                    ·
                      refine ⟨460097665212815984816707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 613463553617087979755609 460097665212815984816707)
                      ·
                        rfl

theorem cell23_896037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 3, 2].length) (baseStart_896037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896037 prefixEnd_896037 := by exact prefixLift 896037
  have htrace : WordTrace (prefixWord ++ tailWord_896037) baseStart_896037 baseEnd_896037 := by
    simpa [prefixWord, tailWord_896037, baseEnd_896037] using wordTrace_append hprefix tailTrace_896037
  have hstable : (prefixWord ++ tailWord_896037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896037).length < 2 ^ (prefixWord ++ tailWord_896037).sum := by decide
  have hdescent : baseEnd_896037 < baseStart_896037 := by decide
  rcases family_descends (prefixWord ++ tailWord_896037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896043 : List Nat := [1, 1, 1, 1, 2, 1, 7, 2, 1, 6]
def baseStart_896043 : Nat := 118140960795 + 896043 * 2 ^ 59
def prefixEnd_896043 : Nat := 4983230072969 + 3 ^ 40 * 896043 * 2
def baseEnd_896043 : Nat := 153366915365580987113893

theorem tailTrace_896043 : CollatzResearch.WordTrace tailWord_896043 prefixEnd_896043 153366915365580987113893 := by
  unfold tailWord_896043
  simp only [CollatzResearch.WordTrace]
  refine ⟨32681373092796717806012783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21787582061864478537341855 32681373092796717806012783)
  ·
    refine ⟨49022059639195076709019175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32681373092796717806012783 49022059639195076709019175)
    ·
      refine ⟨73533089458792615063528763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49022059639195076709019175 73533089458792615063528763)
      ·
        refine ⟨110299634188188922595293145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73533089458792615063528763 110299634188188922595293145)
        ·
          refine ⟨82724725641141691946469859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110299634188188922595293145 82724725641141691946469859)
          ·
            refine ⟨124087088461712537919704789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82724725641141691946469859 124087088461712537919704789)
            ·
              refine ⟨2908291135821387607493081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 124087088461712537919704789 2908291135821387607493081)
              ·
                refine ⟨2181218351866040705619811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2908291135821387607493081 2181218351866040705619811)
                ·
                  refine ⟨3271827527799061058429717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2181218351866040705619811 3271827527799061058429717)
                  ·
                    refine ⟨153366915365580987113893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3271827527799061058429717 153366915365580987113893)
                    ·
                      rfl

theorem cell23_896043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 6].length) (baseStart_896043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896043 prefixEnd_896043 := by exact prefixLift 896043
  have htrace : WordTrace (prefixWord ++ tailWord_896043) baseStart_896043 baseEnd_896043 := by
    simpa [prefixWord, tailWord_896043, baseEnd_896043] using wordTrace_append hprefix tailTrace_896043
  have hstable : (prefixWord ++ tailWord_896043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896043).length < 2 ^ (prefixWord ++ tailWord_896043).sum := by decide
  have hdescent : baseEnd_896043 < baseStart_896043 := by decide
  rcases family_descends (prefixWord ++ tailWord_896043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896054 : List Nat := [5, 1, 2, 1, 1, 2, 2, 2, 2, 3, 2]
def baseStart_896054 : Nat := 118140960795 + 896054 * 2 ^ 59
def prefixEnd_896054 : Nat := 4983230072969 + 3 ^ 40 * 896054 * 2
def baseEnd_896054 : Nat := 460106394383942418304129

theorem tailTrace_896054 : CollatzResearch.WordTrace tailWord_896054 prefixEnd_896054 460106394383942418304129 := by
  unfold tailWord_896054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2042610893484804167791451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21787849530504577789775477 2042610893484804167791451)
  ·
    refine ⟨3063916340227206251687177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2042610893484804167791451 3063916340227206251687177)
    ·
      refine ⟨2297937255170404688765383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3063916340227206251687177 2297937255170404688765383)
      ·
        refine ⟨3446905882755607033148075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2297937255170404688765383 3446905882755607033148075)
        ·
          refine ⟨5170358824133410549722113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3446905882755607033148075 5170358824133410549722113)
          ·
            refine ⟨3877769118100057912291585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5170358824133410549722113 3877769118100057912291585)
            ·
              refine ⟨2908326838575043434218689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3877769118100057912291585 2908326838575043434218689)
              ·
                refine ⟨2181245128931282575664017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2908326838575043434218689 2181245128931282575664017)
                ·
                  refine ⟨1635933846698461931748013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2181245128931282575664017 1635933846698461931748013)
                  ·
                    refine ⟨613475192511923224405505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1635933846698461931748013 613475192511923224405505)
                    ·
                      refine ⟨460106394383942418304129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 613475192511923224405505 460106394383942418304129)
                      ·
                        rfl

theorem cell23_896054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_896054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896054 prefixEnd_896054 := by exact prefixLift 896054
  have htrace : WordTrace (prefixWord ++ tailWord_896054) baseStart_896054 baseEnd_896054 := by
    simpa [prefixWord, tailWord_896054, baseEnd_896054] using wordTrace_append hprefix tailTrace_896054
  have hstable : (prefixWord ++ tailWord_896054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896054).length < 2 ^ (prefixWord ++ tailWord_896054).sum := by decide
  have hdescent : baseEnd_896054 < baseStart_896054 := by decide
  rcases family_descends (prefixWord ++ tailWord_896054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896061 : List Nat := [1, 4, 1, 3, 1, 2, 4, 2, 1, 1, 3]
def baseStart_896061 : Nat := 118140960795 + 896061 * 2 ^ 59
def prefixEnd_896061 : Nat := 4983230072969 + 3 ^ 40 * 896061 * 2
def baseEnd_896061 : Nat := 460109988748523890916597

theorem tailTrace_896061 : CollatzResearch.WordTrace tailWord_896061 prefixEnd_896061 460109988748523890916597 := by
  unfold tailWord_896061
  simp only [CollatzResearch.WordTrace]
  refine ⟨32682029606731506880168037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21788019737821004586778691 32682029606731506880168037)
  ·
    refine ⟨6127880551262157540031507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32682029606731506880168037 6127880551262157540031507)
    ·
      refine ⟨9191820826893236310047261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6127880551262157540031507 9191820826893236310047261)
      ·
        refine ⟨3446932810084963616267723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9191820826893236310047261 3446932810084963616267723)
        ·
          refine ⟨5170399215127445424401585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3446932810084963616267723 5170399215127445424401585)
          ·
            refine ⟨3877799411345584068301189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5170399215127445424401585 3877799411345584068301189)
            ·
              refine ⟨727087389627297012806473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3877799411345584068301189 727087389627297012806473)
              ·
                refine ⟨545315542220472759604855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 727087389627297012806473 545315542220472759604855)
                ·
                  refine ⟨817973313330709139407283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 545315542220472759604855 817973313330709139407283)
                  ·
                    refine ⟨1226959969996063709110925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 817973313330709139407283 1226959969996063709110925)
                    ·
                      refine ⟨460109988748523890916597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1226959969996063709110925 460109988748523890916597)
                      ·
                        rfl

theorem cell23_896061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_896061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896061 prefixEnd_896061 := by exact prefixLift 896061
  have htrace : WordTrace (prefixWord ++ tailWord_896061) baseStart_896061 baseEnd_896061 := by
    simpa [prefixWord, tailWord_896061, baseEnd_896061] using wordTrace_append hprefix tailTrace_896061
  have hstable : (prefixWord ++ tailWord_896061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896061).length < 2 ^ (prefixWord ++ tailWord_896061).sum := by decide
  have hdescent : baseEnd_896061 < baseStart_896061 := by decide
  rcases family_descends (prefixWord ++ tailWord_896061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896063 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 4]
def baseStart_896063 : Nat := 118140960795 + 896063 * 2 ^ 59
def prefixEnd_896063 : Nat := 4983230072969 + 3 ^ 40 * 896063 * 2
def baseEnd_896063 : Nat := 460111015709832883091587

theorem tailTrace_896063 : CollatzResearch.WordTrace tailWord_896063 prefixEnd_896063 460111015709832883091587 := by
  unfold tailWord_896063
  simp only [CollatzResearch.WordTrace]
  refine ⟨32682102552724261221740843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21788068368482840814493895 32682102552724261221740843)
  ·
    refine ⟨49023153829086391832611265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32682102552724261221740843 49023153829086391832611265)
    ·
      refine ⟨36767365371814793874458449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49023153829086391832611265 36767365371814793874458449)
      ·
        refine ⟨27575524028861095405843837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36767365371814793874458449 27575524028861095405843837)
        ·
          refine ⟨10340821510822910777191439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27575524028861095405843837 10340821510822910777191439)
          ·
            refine ⟨15511232266234366165787159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10340821510822910777191439 15511232266234366165787159)
            ·
              refine ⟨23266848399351549248680739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15511232266234366165787159 23266848399351549248680739)
              ·
                refine ⟨34900272599027323873021109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23266848399351549248680739 34900272599027323873021109)
                ·
                  refine ⟨3271900556158811613095729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34900272599027323873021109 3271900556158811613095729)
                  ·
                    refine ⟨2453925417119108709821797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3271900556158811613095729 2453925417119108709821797)
                    ·
                      refine ⟨460111015709832883091587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2453925417119108709821797 460111015709832883091587)
                      ·
                        rfl

theorem cell23_896063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_896063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896063 prefixEnd_896063 := by exact prefixLift 896063
  have htrace : WordTrace (prefixWord ++ tailWord_896063) baseStart_896063 baseEnd_896063 := by
    simpa [prefixWord, tailWord_896063, baseEnd_896063] using wordTrace_append hprefix tailTrace_896063
  have hstable : (prefixWord ++ tailWord_896063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896063).length < 2 ^ (prefixWord ++ tailWord_896063).sum := by decide
  have hdescent : baseEnd_896063 < baseStart_896063 := by decide
  rcases family_descends (prefixWord ++ tailWord_896063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896067 : List Nat := [1, 1, 1, 3, 1, 2, 4, 3, 3, 2, 2]
def baseStart_896067 : Nat := 118140960795 + 896067 * 2 ^ 59
def prefixEnd_896067 : Nat := 4983230072969 + 3 ^ 40 * 896067 * 2
def baseEnd_896067 : Nat := 460113069632450867441569

theorem tailTrace_896067 : CollatzResearch.WordTrace tailWord_896067 prefixEnd_896067 460113069632450867441569 := by
  unfold tailWord_896067
  simp only [CollatzResearch.WordTrace]
  refine ⟨32682248444709769904886455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21788165629806513269924303 32682248444709769904886455)
  ·
    refine ⟨49023372667064654857329683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32682248444709769904886455 49023372667064654857329683)
    ·
      refine ⟨73535059000596982285994525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49023372667064654857329683 73535059000596982285994525)
      ·
        refine ⟨27575647125223868357247947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73535059000596982285994525 27575647125223868357247947)
        ·
          refine ⟨41363470687835802535871921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27575647125223868357247947 41363470687835802535871921)
          ·
            refine ⟨31022603015876851901903941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41363470687835802535871921 31022603015876851901903941)
            ·
              refine ⟨5816738065476909731606989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31022603015876851901903941 5816738065476909731606989)
              ·
                refine ⟨2181276774553841149352621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5816738065476909731606989 2181276774553841149352621)
                ·
                  refine ⟨817978790457690431007233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2181276774553841149352621 817978790457690431007233)
                  ·
                    refine ⟨613484092843267823255425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 817978790457690431007233 613484092843267823255425)
                    ·
                      refine ⟨460113069632450867441569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 613484092843267823255425 460113069632450867441569)
                      ·
                        rfl

theorem cell23_896067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 3, 2, 2].length) (baseStart_896067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896067 prefixEnd_896067 := by exact prefixLift 896067
  have htrace : WordTrace (prefixWord ++ tailWord_896067) baseStart_896067 baseEnd_896067 := by
    simpa [prefixWord, tailWord_896067, baseEnd_896067] using wordTrace_append hprefix tailTrace_896067
  have hstable : (prefixWord ++ tailWord_896067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896067).length < 2 ^ (prefixWord ++ tailWord_896067).sum := by decide
  have hdescent : baseEnd_896067 < baseStart_896067 := by decide
  rcases family_descends (prefixWord ++ tailWord_896067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896077 : List Nat := [1, 6, 1, 1, 1, 3, 2, 1, 1, 6]
def baseStart_896077 : Nat := 118140960795 + 896077 * 2 ^ 59
def prefixEnd_896077 : Nat := 4983230072969 + 3 ^ 40 * 896077 * 2
def baseEnd_896077 : Nat := 153372734812998609438841

theorem tailTrace_896077 : CollatzResearch.WordTrace tailWord_896077 prefixEnd_896077 153372734812998609438841 := by
  unfold tailWord_896077
  simp only [CollatzResearch.WordTrace]
  refine ⟨32682613174673541612750485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21788408783115694408500323 32682613174673541612750485)
  ·
    refine ⟨1531997492562822263097679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32682613174673541612750485 1531997492562822263097679)
    ·
      refine ⟨2297996238844233394646519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1531997492562822263097679 2297996238844233394646519)
      ·
        refine ⟨3446994358266350091969779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2297996238844233394646519 3446994358266350091969779)
        ·
          refine ⟨5170491537399525137954669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3446994358266350091969779 5170491537399525137954669)
          ·
            refine ⟨1938934326524821926733001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5170491537399525137954669 1938934326524821926733001)
            ·
              refine ⟨1454200744893616445049751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1938934326524821926733001 1454200744893616445049751)
              ·
                refine ⟨2181301117340424667574627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1454200744893616445049751 2181301117340424667574627)
                ·
                  refine ⟨3271951676010637001361941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2181301117340424667574627 3271951676010637001361941)
                  ·
                    refine ⟨153372734812998609438841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3271951676010637001361941 153372734812998609438841)
                    ·
                      rfl

theorem cell23_896077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_896077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896077 prefixEnd_896077 := by exact prefixLift 896077
  have htrace : WordTrace (prefixWord ++ tailWord_896077) baseStart_896077 baseEnd_896077 := by
    simpa [prefixWord, tailWord_896077, baseEnd_896077] using wordTrace_append hprefix tailTrace_896077
  have hstable : (prefixWord ++ tailWord_896077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896077).length < 2 ^ (prefixWord ++ tailWord_896077).sum := by decide
  have hdescent : baseEnd_896077 < baseStart_896077 := by decide
  rcases family_descends (prefixWord ++ tailWord_896077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896094 : List Nat := [4, 4, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_896094 : Nat := 118140960795 + 896094 * 2 ^ 59
def prefixEnd_896094 : Nat := 4983230072969 + 3 ^ 40 * 896094 * 2
def baseEnd_896094 : Nat := 153375644536707420601315

theorem tailTrace_896094 : CollatzResearch.WordTrace tailWord_896094 prefixEnd_896094 153375644536707420601315 := by
  unfold tailWord_896094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4085404151951494189514917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21788822143741302344079557 4085404151951494189514917)
  ·
    refine ⟨766013278490905160534047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4085404151951494189514917 766013278490905160534047)
    ·
      refine ⟨1149019917736357740801071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 766013278490905160534047 1149019917736357740801071)
      ·
        refine ⟨1723529876604536611201607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1149019917736357740801071 1723529876604536611201607)
        ·
          refine ⟨2585294814906804916802411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1723529876604536611201607 2585294814906804916802411)
          ·
            refine ⟨3877942222360207375203617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2585294814906804916802411 3877942222360207375203617)
            ·
              refine ⟨2908456666770155531402713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3877942222360207375203617 2908456666770155531402713)
              ·
                refine ⟨2181342500077616648552035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2908456666770155531402713 2181342500077616648552035)
                ·
                  refine ⟨3272013750116424972828053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2181342500077616648552035 3272013750116424972828053)
                  ·
                    refine ⟨153375644536707420601315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3272013750116424972828053 153375644536707420601315)
                    ·
                      rfl

theorem cell23_896094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_896094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896094 prefixEnd_896094 := by exact prefixLift 896094
  have htrace : WordTrace (prefixWord ++ tailWord_896094) baseStart_896094 baseEnd_896094 := by
    simpa [prefixWord, tailWord_896094, baseEnd_896094] using wordTrace_append hprefix tailTrace_896094
  have hstable : (prefixWord ++ tailWord_896094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896094).length < 2 ^ (prefixWord ++ tailWord_896094).sum := by decide
  have hdescent : baseEnd_896094 < baseStart_896094 := by decide
  rcases family_descends (prefixWord ++ tailWord_896094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896101 : List Nat := [1, 3, 1, 3, 2, 1, 4, 3, 1, 2, 2]
def baseStart_896101 : Nat := 118140960795 + 896101 * 2 ^ 59
def prefixEnd_896101 : Nat := 4983230072969 + 3 ^ 40 * 896101 * 2
def baseEnd_896101 : Nat := 460130527974703734416413

theorem tailTrace_896101 : CollatzResearch.WordTrace tailWord_896101 prefixEnd_896101 460130527974703734416413 := by
  unfold tailWord_896101
  simp only [CollatzResearch.WordTrace]
  refine ⟨32683488526586593711624157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21788992351057729141082771 32683488526586593711624157)
  ·
    refine ⟨12256308197469972641859059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32683488526586593711624157 12256308197469972641859059)
    ·
      refine ⟨18384462296204958962788589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12256308197469972641859059 18384462296204958962788589)
      ·
        refine ⟨6894173361076859611045721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18384462296204958962788589 6894173361076859611045721)
        ·
          refine ⟨5170630020807644708284291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6894173361076859611045721 5170630020807644708284291)
          ·
            refine ⟨7755945031211467062426437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5170630020807644708284291 7755945031211467062426437)
            ·
              refine ⟨1454239693352150074204957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7755945031211467062426437 1454239693352150074204957)
              ·
                refine ⟨545339885007056277826859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1454239693352150074204957 545339885007056277826859)
                ·
                  refine ⟨818009827510584416740289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 545339885007056277826859 818009827510584416740289)
                  ·
                    refine ⟨613507370632938312555217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 818009827510584416740289 613507370632938312555217)
                    ·
                      refine ⟨460130527974703734416413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 613507370632938312555217 460130527974703734416413)
                      ·
                        rfl

theorem cell23_896101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_896101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896101 prefixEnd_896101 := by exact prefixLift 896101
  have htrace : WordTrace (prefixWord ++ tailWord_896101) baseStart_896101 baseEnd_896101 := by
    simpa [prefixWord, tailWord_896101, baseEnd_896101] using wordTrace_append hprefix tailTrace_896101
  have hstable : (prefixWord ++ tailWord_896101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896101).length < 2 ^ (prefixWord ++ tailWord_896101).sum := by decide
  have hdescent : baseEnd_896101 < baseStart_896101 := by decide
  rcases family_descends (prefixWord ++ tailWord_896101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896113 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 4, 2, 5]
def baseStart_896113 : Nat := 118140960795 + 896113 * 2 ^ 59
def prefixEnd_896113 : Nat := 4983230072969 + 3 ^ 40 * 896113 * 2
def baseEnd_896113 : Nat := 460136689742557687466357

theorem tailTrace_896113 : CollatzResearch.WordTrace tailWord_896113 prefixEnd_896113 460136689742557687466357 := by
  unfold tailWord_896113
  simp only [CollatzResearch.WordTrace]
  refine ⟨32683926202543119761060993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21789284135028746507373995 32683926202543119761060993)
  ·
    refine ⟨24512944651907339820795745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32683926202543119761060993 24512944651907339820795745)
    ·
      refine ⟨18384708488930504865596809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24512944651907339820795745 18384708488930504865596809)
      ·
        refine ⟨13788531366697878649197607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18384708488930504865596809 13788531366697878649197607)
        ·
          refine ⟨20682797050046817973796411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13788531366697878649197607 20682797050046817973796411)
          ·
            refine ⟨31024195575070226960694617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20682797050046817973796411 31024195575070226960694617)
            ·
              refine ⟨23268146681302670220520963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31024195575070226960694617 23268146681302670220520963)
              ·
                refine ⟨34902220021954005330781445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23268146681302670220520963 34902220021954005330781445)
                ·
                  refine ⟨6544166254116375999521521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34902220021954005330781445 6544166254116375999521521)
                  ·
                    refine ⟨4908124690587281999641141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6544166254116375999521521 4908124690587281999641141)
                    ·
                      refine ⟨460136689742557687466357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4908124690587281999641141 460136689742557687466357)
                      ·
                        rfl

theorem cell23_896113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_896113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896113 prefixEnd_896113 := by exact prefixLift 896113
  have htrace : WordTrace (prefixWord ++ tailWord_896113) baseStart_896113 baseEnd_896113 := by
    simpa [prefixWord, tailWord_896113, baseEnd_896113] using wordTrace_append hprefix tailTrace_896113
  have hstable : (prefixWord ++ tailWord_896113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896113).length < 2 ^ (prefixWord ++ tailWord_896113).sum := by decide
  have hdescent : baseEnd_896113 < baseStart_896113 := by decide
  rcases family_descends (prefixWord ++ tailWord_896113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896123 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 4]
def baseStart_896123 : Nat := 118140960795 + 896123 * 2 ^ 59
def prefixEnd_896123 : Nat := 4983230072969 + 3 ^ 40 * 896123 * 2
def baseEnd_896123 : Nat := 460141824549102648341311

theorem tailTrace_896123 : CollatzResearch.WordTrace tailWord_896123 prefixEnd_896123 460141824549102648341311 := by
  unfold tailWord_896123
  simp only [CollatzResearch.WordTrace]
  refine ⟨32684290932506891468925023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21789527288337927645950015 32684290932506891468925023)
  ·
    refine ⟨49026436398760337203387535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32684290932506891468925023 49026436398760337203387535)
    ·
      refine ⟨73539654598140505805081303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49026436398760337203387535 73539654598140505805081303)
      ·
        refine ⟨110309481897210758707621955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73539654598140505805081303 110309481897210758707621955)
        ·
          refine ⟨165464222845816138061432933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110309481897210758707621955 165464222845816138061432933)
          ·
            refine ⟨31024541783590525886518675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165464222845816138061432933 31024541783590525886518675)
            ·
              refine ⟨46536812675385788829778013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31024541783590525886518675 46536812675385788829778013)
              ·
                refine ⟨17451304753269670811166755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46536812675385788829778013 17451304753269670811166755)
                ·
                  refine ⟨26176957129904506216750133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17451304753269670811166755 26176957129904506216750133)
                  ·
                    refine ⟨2454089730928547457820325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26176957129904506216750133 2454089730928547457820325)
                    ·
                      refine ⟨460141824549102648341311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2454089730928547457820325 460141824549102648341311)
                      ·
                        rfl

theorem cell23_896123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 4].length) (baseStart_896123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896123 prefixEnd_896123 := by exact prefixLift 896123
  have htrace : WordTrace (prefixWord ++ tailWord_896123) baseStart_896123 baseEnd_896123 := by
    simpa [prefixWord, tailWord_896123, baseEnd_896123] using wordTrace_append hprefix tailTrace_896123
  have hstable : (prefixWord ++ tailWord_896123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896123).length < 2 ^ (prefixWord ++ tailWord_896123).sum := by decide
  have hdescent : baseEnd_896123 < baseStart_896123 := by decide
  rcases family_descends (prefixWord ++ tailWord_896123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896157 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 3, 4, 2]
def baseStart_896157 : Nat := 118140960795 + 896157 * 2 ^ 59
def prefixEnd_896157 : Nat := 4983230072969 + 3 ^ 40 * 896157 * 2
def baseEnd_896157 : Nat := 460159282891355515316155

theorem tailTrace_896157 : CollatzResearch.WordTrace tailWord_896157 prefixEnd_896157 460159282891355515316155 := by
  unfold tailWord_896157
  simp only [CollatzResearch.WordTrace]
  refine ⟨32685531014383715275662725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21790354009589143517108483 32685531014383715275662725)
  ·
    refine ⟨6128537065196946614186761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32685531014383715275662725 6128537065196946614186761)
    ·
      refine ⟨4596402798897709960640071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6128537065196946614186761 4596402798897709960640071)
      ·
        refine ⟨6894604198346564940960107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4596402798897709960640071 6894604198346564940960107)
        ·
          refine ⟨10341906297519847411440161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6894604198346564940960107 10341906297519847411440161)
          ·
            refine ⟨7756429723139885558580121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10341906297519847411440161 7756429723139885558580121)
            ·
              refine ⟨5817322292354914168935091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7756429723139885558580121 5817322292354914168935091)
              ·
                refine ⟨8725983438532371253402637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5817322292354914168935091 8725983438532371253402637)
                ·
                  refine ⟨3272243789449639220025989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8725983438532371253402637 3272243789449639220025989)
                  ·
                    refine ⟨613545710521807353754873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3272243789449639220025989 613545710521807353754873)
                    ·
                      refine ⟨460159282891355515316155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 613545710521807353754873 460159282891355515316155)
                      ·
                        rfl

theorem cell23_896157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_896157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896157 prefixEnd_896157 := by exact prefixLift 896157
  have htrace : WordTrace (prefixWord ++ tailWord_896157) baseStart_896157 baseEnd_896157 := by
    simpa [prefixWord, tailWord_896157, baseEnd_896157] using wordTrace_append hprefix tailTrace_896157
  have hstable : (prefixWord ++ tailWord_896157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896157).length < 2 ^ (prefixWord ++ tailWord_896157).sum := by decide
  have hdescent : baseEnd_896157 < baseStart_896157 := by decide
  rcases family_descends (prefixWord ++ tailWord_896157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896160 : List Nat := [2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 5]
def baseStart_896160 : Nat := 118140960795 + 896160 * 2 ^ 59
def prefixEnd_896160 : Nat := 4983230072969 + 3 ^ 40 * 896160 * 2
def baseEnd_896160 : Nat := 460160823333319003578641

theorem tailTrace_896160 : CollatzResearch.WordTrace tailWord_896160 prefixEnd_896160 460160823333319003578641 := by
  unfold tailWord_896160
  simp only [CollatzResearch.WordTrace]
  refine ⟨16342820216686423394010967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21790426955581897858681289 16342820216686423394010967)
  ·
    refine ⟨24514230325029635091016451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16342820216686423394010967 24514230325029635091016451)
    ·
      refine ⟨36771345487544452636524677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24514230325029635091016451 36771345487544452636524677)
      ·
        refine ⟨6894627278914584869348377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36771345487544452636524677 6894627278914584869348377)
        ·
          refine ⟨5170970459185938652011283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6894627278914584869348377 5170970459185938652011283)
          ·
            refine ⟨7756455688778907978016925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5170970459185938652011283 7756455688778907978016925)
            ·
              refine ⟨2908670883292090491756347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7756455688778907978016925 2908670883292090491756347)
              ·
                refine ⟨4363006324938135737634521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2908670883292090491756347 4363006324938135737634521)
                ·
                  refine ⟨3272254743703601803225891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4363006324938135737634521 3272254743703601803225891)
                  ·
                    refine ⟨4908382115555402704838837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3272254743703601803225891 4908382115555402704838837)
                    ·
                      refine ⟨460160823333319003578641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4908382115555402704838837 460160823333319003578641)
                      ·
                        rfl

theorem cell23_896160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_896160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896160 prefixEnd_896160 := by exact prefixLift 896160
  have htrace : WordTrace (prefixWord ++ tailWord_896160) baseStart_896160 baseEnd_896160 := by
    simpa [prefixWord, tailWord_896160, baseEnd_896160] using wordTrace_append hprefix tailTrace_896160
  have hstable : (prefixWord ++ tailWord_896160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896160).length < 2 ^ (prefixWord ++ tailWord_896160).sum := by decide
  have hdescent : baseEnd_896160 < baseStart_896160 := by decide
  rcases family_descends (prefixWord ++ tailWord_896160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896163 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 9]
def baseStart_896163 : Nat := 118140960795 + 896163 * 2 ^ 59
def prefixEnd_896163 : Nat := 4983230072969 + 3 ^ 40 * 896163 * 2
def baseEnd_896163 : Nat := 51129151530586943537903

theorem tailTrace_896163 : CollatzResearch.WordTrace tailWord_896163 prefixEnd_896163 51129151530586943537903 := by
  unfold tailWord_896163
  simp only [CollatzResearch.WordTrace]
  refine ⟨32685749852361978300381143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21790499901574652200254095 32685749852361978300381143)
  ·
    refine ⟨49028624778542967450571715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32685749852361978300381143 49028624778542967450571715)
    ·
      refine ⟨73542937167814451175857573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49028624778542967450571715 73542937167814451175857573)
      ·
        refine ⟨13789300718965209595473295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73542937167814451175857573 13789300718965209595473295)
        ·
          refine ⟨20683951078447814393209943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13789300718965209595473295 20683951078447814393209943)
          ·
            refine ⟨31025926617671721589814915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20683951078447814393209943 31025926617671721589814915)
            ·
              refine ⟨46538889926507582384722373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31025926617671721589814915 46538889926507582384722373)
              ·
                refine ⟨8726041861220171697135445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46538889926507582384722373 8726041861220171697135445)
                ·
                  refine ⟨51129151530586943537903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8726041861220171697135445 51129151530586943537903)
                  ·
                    rfl

theorem cell23_896163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 9].length) (baseStart_896163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896163 prefixEnd_896163 := by exact prefixLift 896163
  have htrace : WordTrace (prefixWord ++ tailWord_896163) baseStart_896163 baseEnd_896163 := by
    simpa [prefixWord, tailWord_896163, baseEnd_896163] using wordTrace_append hprefix tailTrace_896163
  have hstable : (prefixWord ++ tailWord_896163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896163).length < 2 ^ (prefixWord ++ tailWord_896163).sum := by decide
  have hdescent : baseEnd_896163 < baseStart_896163 := by decide
  rcases family_descends (prefixWord ++ tailWord_896163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896191 : List Nat := [1, 1, 2, 2, 2, 2, 6, 1, 2, 2, 2]
def baseStart_896191 : Nat := 118140960795 + 896191 * 2 ^ 59
def prefixEnd_896191 : Nat := 4983230072969 + 3 ^ 40 * 896191 * 2
def baseEnd_896191 : Nat := 460176741233608382290999

theorem tailTrace_896191 : CollatzResearch.WordTrace tailWord_896191 prefixEnd_896191 460176741233608382290999 := by
  unfold tailWord_896191
  simp only [CollatzResearch.WordTrace]
  refine ⟨32686771096260539082400427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21791180730840359388266951 32686771096260539082400427)
  ·
    refine ⟨49030156644390808623600641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32686771096260539082400427 49030156644390808623600641)
    ·
      refine ⟨36772617483293106467700481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49030156644390808623600641 36772617483293106467700481)
      ·
        refine ⟨27579463112469829850775361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36772617483293106467700481 27579463112469829850775361)
        ·
          refine ⟨20684597334352372388081521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27579463112469829850775361 20684597334352372388081521)
          ·
            refine ⟨15513448000764279291061141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20684597334352372388081521 15513448000764279291061141)
            ·
              refine ⟨727192875035825591768491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15513448000764279291061141 727192875035825591768491)
              ·
                refine ⟨1090789312553738387652737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 727192875035825591768491 1090789312553738387652737)
                ·
                  refine ⟨818091984415303790739553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1090789312553738387652737 818091984415303790739553)
                  ·
                    refine ⟨613568988311477843054665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 818091984415303790739553 613568988311477843054665)
                    ·
                      refine ⟨460176741233608382290999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 613568988311477843054665 460176741233608382290999)
                      ·
                        rfl

theorem cell23_896191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 2, 2, 2].length) (baseStart_896191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896191 prefixEnd_896191 := by exact prefixLift 896191
  have htrace : WordTrace (prefixWord ++ tailWord_896191) baseStart_896191 baseEnd_896191 := by
    simpa [prefixWord, tailWord_896191, baseEnd_896191] using wordTrace_append hprefix tailTrace_896191
  have hstable : (prefixWord ++ tailWord_896191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896191).length < 2 ^ (prefixWord ++ tailWord_896191).sum := by decide
  have hdescent : baseEnd_896191 < baseStart_896191 := by decide
  rcases family_descends (prefixWord ++ tailWord_896191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896237 : List Nat := [1, 5, 1, 2, 2, 1, 2, 1, 1, 2, 5]
def baseStart_896237 : Nat := 118140960795 + 896237 * 2 ^ 59
def prefixEnd_896237 : Nat := 4983230072969 + 3 ^ 40 * 896237 * 2
def baseEnd_896237 : Nat := 460200361343715202315787

theorem tailTrace_896237 : CollatzResearch.WordTrace tailWord_896237 prefixEnd_896237 460200361343715202315787 := by
  unfold tailWord_896237
  simp only [CollatzResearch.WordTrace]
  refine ⟨32688448854093888938574965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21792299236062592625716643 32688448854093888938574965)
  ·
    refine ⟨3064542080071302087991403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32688448854093888938574965 3064542080071302087991403)
    ·
      refine ⟨4596813120106953131987105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3064542080071302087991403 4596813120106953131987105)
      ·
        refine ⟨3447609840080214848990329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4596813120106953131987105 3447609840080214848990329)
        ·
          refine ⟨2585707380060161136742747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3447609840080214848990329 2585707380060161136742747)
          ·
            refine ⟨3878561070090241705114121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2585707380060161136742747 3878561070090241705114121)
            ·
              refine ⟨2908920802567681278835591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3878561070090241705114121 2908920802567681278835591)
              ·
                refine ⟨4363381203851521918253387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2908920802567681278835591 4363381203851521918253387)
                ·
                  refine ⟨6545071805777282877380081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4363381203851521918253387 6545071805777282877380081)
                  ·
                    refine ⟨4908803854332962158035061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6545071805777282877380081 4908803854332962158035061)
                    ·
                      refine ⟨460200361343715202315787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4908803854332962158035061 460200361343715202315787)
                      ·
                        rfl

theorem cell23_896237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_896237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896237 prefixEnd_896237 := by exact prefixLift 896237
  have htrace : WordTrace (prefixWord ++ tailWord_896237) baseStart_896237 baseEnd_896237 := by
    simpa [prefixWord, tailWord_896237, baseEnd_896237] using wordTrace_append hprefix tailTrace_896237
  have hstable : (prefixWord ++ tailWord_896237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896237).length < 2 ^ (prefixWord ++ tailWord_896237).sum := by decide
  have hdescent : baseEnd_896237 < baseStart_896237 := by decide
  rcases family_descends (prefixWord ++ tailWord_896237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896247 : List Nat := [1, 1, 3, 1, 1, 1, 2, 5, 2, 4, 2]
def baseStart_896247 : Nat := 118140960795 + 896247 * 2 ^ 59
def prefixEnd_896247 : Nat := 4983230072969 + 3 ^ 40 * 896247 * 2
def baseEnd_896247 : Nat := 460205496150260163190741

theorem tailTrace_896247 : CollatzResearch.WordTrace tailWord_896247 prefixEnd_896247 460205496150260163190741 := by
  unfold tailWord_896247
  simp only [CollatzResearch.WordTrace]
  refine ⟨32688813584057660646438995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21792542389371773764292663 32688813584057660646438995)
  ·
    refine ⟨49033220376086490969658493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32688813584057660646438995 49033220376086490969658493)
    ·
      refine ⟨18387457641032434113621935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49033220376086490969658493 18387457641032434113621935)
      ·
        refine ⟨27581186461548651170432903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18387457641032434113621935 27581186461548651170432903)
        ·
          refine ⟨41371779692322976755649355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27581186461548651170432903 41371779692322976755649355)
          ·
            refine ⟨62057669538484465133474033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41371779692322976755649355 62057669538484465133474033)
            ·
              refine ⟨46543252153863348850105525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62057669538484465133474033 46543252153863348850105525)
              ·
                refine ⟨4363429889424688954697393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46543252153863348850105525 4363429889424688954697393)
                ·
                  refine ⟨3272572417068516716023045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4363429889424688954697393 3272572417068516716023045)
                  ·
                    refine ⟨613607328200346884254321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3272572417068516716023045 613607328200346884254321)
                    ·
                      refine ⟨460205496150260163190741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 613607328200346884254321 460205496150260163190741)
                      ·
                        rfl

theorem cell23_896247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 4, 2].length) (baseStart_896247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896247 prefixEnd_896247 := by exact prefixLift 896247
  have htrace : WordTrace (prefixWord ++ tailWord_896247) baseStart_896247 baseEnd_896247 := by
    simpa [prefixWord, tailWord_896247, baseEnd_896247] using wordTrace_append hprefix tailTrace_896247
  have hstable : (prefixWord ++ tailWord_896247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896247).length < 2 ^ (prefixWord ++ tailWord_896247).sum := by decide
  have hdescent : baseEnd_896247 < baseStart_896247 := by decide
  rcases family_descends (prefixWord ++ tailWord_896247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896257 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 5, 4]
def baseStart_896257 : Nat := 118140960795 + 896257 * 2 ^ 59
def prefixEnd_896257 : Nat := 4983230072969 + 3 ^ 40 * 896257 * 2
def baseEnd_896257 : Nat := 153403543652268374688565

theorem tailTrace_896257 : CollatzResearch.WordTrace tailWord_896257 prefixEnd_896257 153403543652268374688565 := by
  unfold tailWord_896257
  simp only [CollatzResearch.WordTrace]
  refine ⟨32689178314021432354303025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21792785542680954902868683 32689178314021432354303025)
  ·
    refine ⟨24516883735516074265727269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32689178314021432354303025 24516883735516074265727269)
    ·
      refine ⟨4596915700409263924823863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24516883735516074265727269 4596915700409263924823863)
      ·
        refine ⟨6895373550613895887235795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4596915700409263924823863 6895373550613895887235795)
        ·
          refine ⟨10343060325920843830853693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6895373550613895887235795 10343060325920843830853693)
          ·
            refine ⟨3878647622220316436570135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10343060325920843830853693 3878647622220316436570135)
            ·
              refine ⟨5817971433330474654855203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3878647622220316436570135 5817971433330474654855203)
              ·
                refine ⟨8726957149995711982282805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5817971433330474654855203 8726957149995711982282805)
                ·
                  refine ⟨818152232812097998339013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8726957149995711982282805 818152232812097998339013)
                  ·
                    refine ⟨153403543652268374688565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 818152232812097998339013 153403543652268374688565)
                    ·
                      rfl

theorem cell23_896257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_896257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896257 prefixEnd_896257 := by exact prefixLift 896257
  have htrace : WordTrace (prefixWord ++ tailWord_896257) baseStart_896257 baseEnd_896257 := by
    simpa [prefixWord, tailWord_896257, baseEnd_896257] using wordTrace_append hprefix tailTrace_896257
  have hstable : (prefixWord ++ tailWord_896257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896257).length < 2 ^ (prefixWord ++ tailWord_896257).sum := by decide
  have hdescent : baseEnd_896257 < baseStart_896257 := by decide
  rcases family_descends (prefixWord ++ tailWord_896257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896267 : List Nat := [1, 1, 1, 1, 5, 4, 1, 1, 1, 4, 3]
def baseStart_896267 : Nat := 118140960795 + 896267 * 2 ^ 59
def prefixEnd_896267 : Nat := 4983230072969 + 3 ^ 40 * 896267 * 2
def baseEnd_896267 : Nat := 460215765763350084940649

theorem tailTrace_896267 : CollatzResearch.WordTrace tailWord_896267 prefixEnd_896267 460215765763350084940649 := by
  unfold tailWord_896267
  simp only [CollatzResearch.WordTrace]
  refine ⟨32689543043985204062167055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21793028695990136041444703 32689543043985204062167055)
  ·
    refine ⟨49034314565977806093250583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32689543043985204062167055 49034314565977806093250583)
    ·
      refine ⟨73551471848966709139875875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49034314565977806093250583 73551471848966709139875875)
      ·
        refine ⟨110327207773450063709813813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73551471848966709139875875 110327207773450063709813813)
        ·
          refine ⟨10343175728760943472795045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110327207773450063709813813 10343175728760943472795045)
          ·
            refine ⟨1939345449142676901149071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10343175728760943472795045 1939345449142676901149071)
            ·
              refine ⟨2909018173714015351723607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1939345449142676901149071 2909018173714015351723607)
              ·
                refine ⟨4363527260571023027585411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2909018173714015351723607 4363527260571023027585411)
                ·
                  refine ⟨6545290890856534541378117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4363527260571023027585411 6545290890856534541378117)
                  ·
                    refine ⟨1227242042035600226508397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6545290890856534541378117 1227242042035600226508397)
                    ·
                      refine ⟨460215765763350084940649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1227242042035600226508397 460215765763350084940649)
                      ·
                        rfl

theorem cell23_896267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 4, 3].length) (baseStart_896267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896267 prefixEnd_896267 := by exact prefixLift 896267
  have htrace : WordTrace (prefixWord ++ tailWord_896267) baseStart_896267 baseEnd_896267 := by
    simpa [prefixWord, tailWord_896267, baseEnd_896267] using wordTrace_append hprefix tailTrace_896267
  have hstable : (prefixWord ++ tailWord_896267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896267).length < 2 ^ (prefixWord ++ tailWord_896267).sum := by decide
  have hdescent : baseEnd_896267 < baseStart_896267 := by decide
  rcases family_descends (prefixWord ++ tailWord_896267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896287 : List Nat := [1, 1, 2, 4, 4, 1, 1, 1, 8]
def baseStart_896287 : Nat := 118140960795 + 896287 * 2 ^ 59
def prefixEnd_896287 : Nat := 4983230072969 + 3 ^ 40 * 896287 * 2
def baseEnd_896287 : Nat := 51136226152937778521173

theorem tailTrace_896287 : CollatzResearch.WordTrace tailWord_896287 prefixEnd_896287 51136226152937778521173 := by
  unfold tailWord_896287
  simp only [CollatzResearch.WordTrace]
  refine ⟨32690272503912747477895115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21793515002608498318596743 32690272503912747477895115)
  ·
    refine ⟨49035408755869121216842673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32690272503912747477895115 49035408755869121216842673)
    ·
      refine ⟨36776556566901840912632005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49035408755869121216842673 36776556566901840912632005)
      ·
        refine ⟨6895604356294095171118501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36776556566901840912632005 6895604356294095171118501)
        ·
          refine ⟨1292925816805142844584719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6895604356294095171118501 1292925816805142844584719)
          ·
            refine ⟨1939388725207714266877079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1292925816805142844584719 1939388725207714266877079)
            ·
              refine ⟨2909083087811571400315619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1939388725207714266877079 2909083087811571400315619)
              ·
                refine ⟨4363624631717357100473429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2909083087811571400315619 4363624631717357100473429)
                ·
                  refine ⟨51136226152937778521173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4363624631717357100473429 51136226152937778521173)
                  ·
                    rfl

theorem cell23_896287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 8].length) (baseStart_896287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896287 prefixEnd_896287 := by exact prefixLift 896287
  have htrace : WordTrace (prefixWord ++ tailWord_896287) baseStart_896287 baseEnd_896287 := by
    simpa [prefixWord, tailWord_896287, baseEnd_896287] using wordTrace_append hprefix tailTrace_896287
  have hstable : (prefixWord ++ tailWord_896287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896287).length < 2 ^ (prefixWord ++ tailWord_896287).sum := by decide
  have hdescent : baseEnd_896287 < baseStart_896287 := by decide
  rcases family_descends (prefixWord ++ tailWord_896287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896314 : List Nat := [3, 1, 1, 1, 4, 1, 1, 4, 3, 1, 3]
def baseStart_896314 : Nat := 118140960795 + 896314 * 2 ^ 59
def prefixEnd_896314 : Nat := 4983230072969 + 3 ^ 40 * 896314 * 2
def baseEnd_896314 : Nat := 460239899354111401052933

theorem tailTrace_896314 : CollatzResearch.WordTrace tailWord_896314 prefixEnd_896314 460239899354111401052933 := by
  unfold tailWord_896314
  simp only [CollatzResearch.WordTrace]
  refine ⟨8172814318703732772281999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21794171516543287392751997 8172814318703732772281999)
  ·
    refine ⟨12259221478055599158422999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8172814318703732772281999 12259221478055599158422999)
    ·
      refine ⟨18388832217083398737634499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12259221478055599158422999 18388832217083398737634499)
      ·
        refine ⟨27583248325625098106451749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18388832217083398737634499 27583248325625098106451749)
        ·
          refine ⟨5171859061054705894959703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27583248325625098106451749 5171859061054705894959703)
          ·
            refine ⟨7757788591582058842439555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5171859061054705894959703 7757788591582058842439555)
            ·
              refine ⟨11636682887373088263659333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7757788591582058842439555 11636682887373088263659333)
              ·
                refine ⟨2181878041382454049436125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11636682887373088263659333 2181878041382454049436125)
                ·
                  refine ⟨818204265518420268538547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2181878041382454049436125 818204265518420268538547)
                  ·
                    refine ⟨1227306398277630402807821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 818204265518420268538547 1227306398277630402807821)
                    ·
                      refine ⟨460239899354111401052933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1227306398277630402807821 460239899354111401052933)
                      ·
                        rfl

theorem cell23_896314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 3, 1, 3].length) (baseStart_896314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896314 prefixEnd_896314 := by exact prefixLift 896314
  have htrace : WordTrace (prefixWord ++ tailWord_896314) baseStart_896314 baseEnd_896314 := by
    simpa [prefixWord, tailWord_896314, baseEnd_896314] using wordTrace_append hprefix tailTrace_896314
  have hstable : (prefixWord ++ tailWord_896314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896314).length < 2 ^ (prefixWord ++ tailWord_896314).sum := by decide
  have hdescent : baseEnd_896314 < baseStart_896314 := by decide
  rcases family_descends (prefixWord ++ tailWord_896314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896341 : List Nat := [1, 3, 2, 2, 3, 2, 1, 2, 2, 3, 2]
def baseStart_896341 : Nat := 118140960795 + 896341 * 2 ^ 59
def prefixEnd_896341 : Nat := 4983230072969 + 3 ^ 40 * 896341 * 2
def baseEnd_896341 : Nat := 460253763331782795415309

theorem tailTrace_896341 : CollatzResearch.WordTrace tailWord_896341 prefixEnd_896341 460253763331782795415309 := by
  unfold tailWord_896341
  simp only [CollatzResearch.WordTrace]
  refine ⟨32692242045717114700360877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21794828030478076466907251 32692242045717114700360877)
  ·
    refine ⟨12259590767143918012635329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32692242045717114700360877 12259590767143918012635329)
    ·
      refine ⟨9194693075357938509476497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12259590767143918012635329 9194693075357938509476497)
      ·
        refine ⟨6896019806518453882107373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9194693075357938509476497 6896019806518453882107373)
        ·
          refine ⟨2586007427444420205790265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6896019806518453882107373 2586007427444420205790265)
          ·
            refine ⟨1939505570583315154342699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2586007427444420205790265 1939505570583315154342699)
            ·
              refine ⟨2909258355874972731514049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1939505570583315154342699 2909258355874972731514049)
              ·
                refine ⟨2181943766906229548635537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2909258355874972731514049 2181943766906229548635537)
                ·
                  refine ⟨1636457825179672161476653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2181943766906229548635537 1636457825179672161476653)
                  ·
                    refine ⟨613671684442377060553745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1636457825179672161476653 613671684442377060553745)
                    ·
                      refine ⟨460253763331782795415309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 613671684442377060553745 460253763331782795415309)
                      ·
                        rfl

theorem cell23_896341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_896341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896341 prefixEnd_896341 := by exact prefixLift 896341
  have htrace : WordTrace (prefixWord ++ tailWord_896341) baseStart_896341 baseEnd_896341 := by
    simpa [prefixWord, tailWord_896341, baseEnd_896341] using wordTrace_append hprefix tailTrace_896341
  have hstable : (prefixWord ++ tailWord_896341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896341).length < 2 ^ (prefixWord ++ tailWord_896341).sum := by decide
  have hdescent : baseEnd_896341 < baseStart_896341 := by decide
  rcases family_descends (prefixWord ++ tailWord_896341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896342 : List Nat := [5, 2, 3, 1, 1, 2, 1, 1, 3, 4]
def baseStart_896342 : Nat := 118140960795 + 896342 * 2 ^ 59
def prefixEnd_896342 : Nat := 4983230072969 + 3 ^ 40 * 896342 * 2
def baseEnd_896342 : Nat := 153418092270812430500935

theorem tailTrace_896342 : CollatzResearch.WordTrace tailWord_896342 prefixEnd_896342 153418092270812430500935 := by
  unfold tailWord_896342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2043267407419593241946705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21794852345808994580764853 2043267407419593241946705)
  ·
    refine ⟨1532450555564694931460029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2043267407419593241946705 1532450555564694931460029)
    ·
      refine ⟨574668958336760599297511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1532450555564694931460029 574668958336760599297511)
      ·
        refine ⟨862003437505140898946267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574668958336760599297511 862003437505140898946267)
        ·
          refine ⟨1293005156257711348419401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 862003437505140898946267 1293005156257711348419401)
          ·
            refine ⟨969753867193283511314551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1293005156257711348419401 969753867193283511314551)
            ·
              refine ⟨1454630800789925266971827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 969753867193283511314551 1454630800789925266971827)
              ·
                refine ⟨2181946201184887900457741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1454630800789925266971827 2181946201184887900457741)
                ·
                  refine ⟨818229825444332962671653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2181946201184887900457741 818229825444332962671653)
                  ·
                    refine ⟨153418092270812430500935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 818229825444332962671653 153418092270812430500935)
                    ·
                      rfl

theorem cell23_896342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_896342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896342 prefixEnd_896342 := by exact prefixLift 896342
  have htrace : WordTrace (prefixWord ++ tailWord_896342) baseStart_896342 baseEnd_896342 := by
    simpa [prefixWord, tailWord_896342, baseEnd_896342] using wordTrace_append hprefix tailTrace_896342
  have hstable : (prefixWord ++ tailWord_896342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896342).length < 2 ^ (prefixWord ++ tailWord_896342).sum := by decide
  have hdescent : baseEnd_896342 < baseStart_896342 := by decide
  rcases family_descends (prefixWord ++ tailWord_896342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896354 : List Nat := [3, 3, 2, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_896354 : Nat := 118140960795 + 896354 * 2 ^ 59
def prefixEnd_896354 : Nat := 4983230072969 + 3 ^ 40 * 896354 * 2
def baseEnd_896354 : Nat := 460260438580291244552749

theorem tailTrace_896354 : CollatzResearch.WordTrace tailWord_896354 prefixEnd_896354 460260438580291244552749 := by
  unfold tailWord_896354
  simp only [CollatzResearch.WordTrace]
  refine ⟨8173179048667504480146029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21795144129780011947056077 8173179048667504480146029)
  ·
    refine ⟨3064942143250314180054761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8173179048667504480146029 3064942143250314180054761)
    ·
      refine ⟨2298706607437735635041071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3064942143250314180054761 2298706607437735635041071)
      ·
        refine ⟨3448059911156603452561607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2298706607437735635041071 3448059911156603452561607)
        ·
          refine ⟨5172089866734905178842411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3448059911156603452561607 5172089866734905178842411)
          ·
            refine ⟨7758134800102357768263617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5172089866734905178842411 7758134800102357768263617)
            ·
              refine ⟨5818601100076768326197713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7758134800102357768263617 5818601100076768326197713)
              ·
                refine ⟨4363950825057576244648285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5818601100076768326197713 4363950825057576244648285)
                ·
                  refine ⟨1636481559396591091743107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4363950825057576244648285 1636481559396591091743107)
                  ·
                    refine ⟨2454722339094886637614661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1636481559396591091743107 2454722339094886637614661)
                    ·
                      refine ⟨460260438580291244552749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2454722339094886637614661 460260438580291244552749)
                      ·
                        rfl

theorem cell23_896354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_896354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896354 prefixEnd_896354 := by exact prefixLift 896354
  have htrace : WordTrace (prefixWord ++ tailWord_896354) baseStart_896354 baseEnd_896354 := by
    simpa [prefixWord, tailWord_896354, baseEnd_896354] using wordTrace_append hprefix tailTrace_896354
  have hstable : (prefixWord ++ tailWord_896354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896354).length < 2 ^ (prefixWord ++ tailWord_896354).sum := by decide
  have hdescent : baseEnd_896354 < baseStart_896354 := by decide
  rcases family_descends (prefixWord ++ tailWord_896354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896357 : List Nat := [1, 3, 1, 3, 1, 2, 1, 4, 1, 1, 5]
def baseStart_896357 : Nat := 118140960795 + 896357 * 2 ^ 59
def prefixEnd_896357 : Nat := 4983230072969 + 3 ^ 40 * 896357 * 2
def baseEnd_896357 : Nat := 460261979022254732815235

theorem tailTrace_896357 : CollatzResearch.WordTrace tailWord_896357 prefixEnd_896357 460261979022254732815235 := by
  unfold tailWord_896357
  simp only [CollatzResearch.WordTrace]
  refine ⟨32692825613659149432943325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21795217075772766288628883 32692825613659149432943325)
  ·
    refine ⟨12259809605122181037353747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32692825613659149432943325 12259809605122181037353747)
    ·
      refine ⟨18389714407683271556030621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12259809605122181037353747 18389714407683271556030621)
      ·
        refine ⟨6896142902881226833511483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18389714407683271556030621 6896142902881226833511483)
        ·
          refine ⟨10344214354321840250267225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6896142902881226833511483 10344214354321840250267225)
          ·
            refine ⟨7758160765741380187700419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10344214354321840250267225 7758160765741380187700419)
            ·
              refine ⟨11637241148612070281550629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7758160765741380187700419 11637241148612070281550629)
              ·
                refine ⟨2181982715364763177790743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11637241148612070281550629 2181982715364763177790743)
                ·
                  refine ⟨3272974073047144766686115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2181982715364763177790743 3272974073047144766686115)
                  ·
                    refine ⟨4909461109570717150029173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3272974073047144766686115 4909461109570717150029173)
                    ·
                      refine ⟨460261979022254732815235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4909461109570717150029173 460261979022254732815235)
                      ·
                        rfl

theorem cell23_896357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_896357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896357 prefixEnd_896357 := by exact prefixLift 896357
  have htrace : WordTrace (prefixWord ++ tailWord_896357) baseStart_896357 baseEnd_896357 := by
    simpa [prefixWord, tailWord_896357, baseEnd_896357] using wordTrace_append hprefix tailTrace_896357
  have hstable : (prefixWord ++ tailWord_896357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896357).length < 2 ^ (prefixWord ++ tailWord_896357).sum := by decide
  have hdescent : baseEnd_896357 < baseStart_896357 := by decide
  rcases family_descends (prefixWord ++ tailWord_896357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896367 : List Nat := [1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 4]
def baseStart_896367 : Nat := 118140960795 + 896367 * 2 ^ 59
def prefixEnd_896367 : Nat := 4983230072969 + 3 ^ 40 * 896367 * 2
def baseEnd_896367 : Nat := 460267113828799693690189

theorem tailTrace_896367 : CollatzResearch.WordTrace tailWord_896367 prefixEnd_896367 460267113828799693690189 := by
  unfold tailWord_896367
  simp only [CollatzResearch.WordTrace]
  refine ⟨32693190343622921140807355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21795460229081947427204903 32693190343622921140807355)
  ·
    refine ⟨49039785515434381711211033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32693190343622921140807355 49039785515434381711211033)
    ·
      refine ⟨36779839136575786283408275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49039785515434381711211033 36779839136575786283408275)
      ·
        refine ⟨55169758704863679425112413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36779839136575786283408275 55169758704863679425112413)
        ·
          refine ⟨20688659514323879784417155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55169758704863679425112413 20688659514323879784417155)
          ·
            refine ⟨31032989271485819676625733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20688659514323879784417155 31032989271485819676625733)
            ·
              refine ⟨5818685488403591189367325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31032989271485819676625733 5818685488403591189367325)
              ·
                refine ⟨2182007058151346696012747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5818685488403591189367325 2182007058151346696012747)
                ·
                  refine ⟨3273010587227020044019121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2182007058151346696012747 3273010587227020044019121)
                  ·
                    refine ⟨2454757940420265033014341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3273010587227020044019121 2454757940420265033014341)
                    ·
                      refine ⟨460267113828799693690189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2454757940420265033014341 460267113828799693690189)
                      ·
                        rfl

theorem cell23_896367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 4].length) (baseStart_896367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896367 prefixEnd_896367 := by exact prefixLift 896367
  have htrace : WordTrace (prefixWord ++ tailWord_896367) baseStart_896367 baseEnd_896367 := by
    simpa [prefixWord, tailWord_896367, baseEnd_896367] using wordTrace_append hprefix tailTrace_896367
  have hstable : (prefixWord ++ tailWord_896367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896367).length < 2 ^ (prefixWord ++ tailWord_896367).sum := by decide
  have hdescent : baseEnd_896367 < baseStart_896367 := by decide
  rcases family_descends (prefixWord ++ tailWord_896367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896398 : List Nat := [4, 1, 1, 4, 2, 1, 2, 2, 2, 4]
def baseStart_896398 : Nat := 118140960795 + 896398 * 2 ^ 59
def prefixEnd_896398 : Nat := 4983230072969 + 3 ^ 40 * 896398 * 2
def baseEnd_896398 : Nat := 153427677243029690800849

theorem tailTrace_896398 : CollatzResearch.WordTrace tailWord_896398 prefixEnd_896398 153427677243029690800849 := by
  unfold tailWord_896398
  simp only [CollatzResearch.WordTrace]
  refine ⟨4086790125813826679398231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21796214004340408956790565 4086790125813826679398231)
  ·
    refine ⟨6130185188720740019097347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4086790125813826679398231 6130185188720740019097347)
    ·
      refine ⟨9195277783081110028646021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6130185188720740019097347 9195277783081110028646021)
      ·
        refine ⟨1724114584327708130371129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9195277783081110028646021 1724114584327708130371129)
        ·
          refine ⟨1293085938245781097778347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1724114584327708130371129 1293085938245781097778347)
          ·
            refine ⟨1939628907368671646667521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1293085938245781097778347 1939628907368671646667521)
            ·
              refine ⟨1454721680526503735000641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1939628907368671646667521 1454721680526503735000641)
              ·
                refine ⟨1091041260394877801250481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1454721680526503735000641 1091041260394877801250481)
                ·
                  refine ⟨818280945296158350937861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1091041260394877801250481 818280945296158350937861)
                  ·
                    refine ⟨153427677243029690800849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 818280945296158350937861 153427677243029690800849)
                    ·
                      rfl

theorem cell23_896398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_896398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896398 prefixEnd_896398 := by exact prefixLift 896398
  have htrace : WordTrace (prefixWord ++ tailWord_896398) baseStart_896398 baseEnd_896398 := by
    simpa [prefixWord, tailWord_896398, baseEnd_896398] using wordTrace_append hprefix tailTrace_896398
  have hstable : (prefixWord ++ tailWord_896398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896398).length < 2 ^ (prefixWord ++ tailWord_896398).sum := by decide
  have hdescent : baseEnd_896398 < baseStart_896398 := by decide
  rcases family_descends (prefixWord ++ tailWord_896398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896405 : List Nat := [1, 3, 2, 1, 1, 2, 6, 2, 1, 2, 2]
def baseStart_896405 : Nat := 118140960795 + 896405 * 2 ^ 59
def prefixEnd_896405 : Nat := 4983230072969 + 3 ^ 40 * 896405 * 2
def baseEnd_896405 : Nat := 460286626093670545015015

theorem tailTrace_896405 : CollatzResearch.WordTrace tailWord_896405 prefixEnd_896405 460286626093670545015015 := by
  unfold tailWord_896405
  simp only [CollatzResearch.WordTrace]
  refine ⟨32694576317485253630690669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21796384211656835753793779 32694576317485253630690669)
  ·
    refine ⟨12260466119056970111509001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32694576317485253630690669 12260466119056970111509001)
    ·
      refine ⟨9195349589292727583631751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12260466119056970111509001 9195349589292727583631751)
      ·
        refine ⟨13793024383939091375447627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9195349589292727583631751 13793024383939091375447627)
        ·
          refine ⟨20689536575908637063171441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13793024383939091375447627 20689536575908637063171441)
          ·
            refine ⟨15517152431931477797378581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20689536575908637063171441 15517152431931477797378581)
            ·
              refine ⟨727366520246788021752121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15517152431931477797378581 727366520246788021752121)
              ·
                refine ⟨545524890185091016314091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 727366520246788021752121 545524890185091016314091)
                ·
                  refine ⟨818287335277636524471137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 545524890185091016314091 818287335277636524471137)
                  ·
                    refine ⟨613715501458227393353353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 818287335277636524471137 613715501458227393353353)
                    ·
                      refine ⟨460286626093670545015015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 613715501458227393353353 460286626093670545015015)
                      ·
                        rfl

theorem cell23_896405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 2, 1, 2, 2].length) (baseStart_896405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896405 prefixEnd_896405 := by exact prefixLift 896405
  have htrace : WordTrace (prefixWord ++ tailWord_896405) baseStart_896405 baseEnd_896405 := by
    simpa [prefixWord, tailWord_896405, baseEnd_896405] using wordTrace_append hprefix tailTrace_896405
  have hstable : (prefixWord ++ tailWord_896405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896405).length < 2 ^ (prefixWord ++ tailWord_896405).sum := by decide
  have hdescent : baseEnd_896405 < baseStart_896405 := by decide
  rcases family_descends (prefixWord ++ tailWord_896405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896447 : List Nat := [1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 5]
def baseStart_896447 : Nat := 118140960795 + 896447 * 2 ^ 59
def prefixEnd_896447 : Nat := 4983230072969 + 3 ^ 40 * 896447 * 2
def baseEnd_896447 : Nat := 460308192281159380689821

theorem tailTrace_896447 : CollatzResearch.WordTrace tailWord_896447 prefixEnd_896447 460308192281159380689821 := by
  unfold tailWord_896447
  simp only [CollatzResearch.WordTrace]
  refine ⟨32696108183333094803719595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21797405455555396535813063 32696108183333094803719595)
  ·
    refine ⟨49044162274999642205579393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32696108183333094803719595 49044162274999642205579393)
    ·
      refine ⟨36783121706249731654184545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49044162274999642205579393 36783121706249731654184545)
      ·
        refine ⟨27587341279687298740638409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36783121706249731654184545 27587341279687298740638409)
        ·
          refine ⟨20690505959765474055478807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27587341279687298740638409 20690505959765474055478807)
          ·
            refine ⟨31035758939648211083218211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20690505959765474055478807 31035758939648211083218211)
            ·
              refine ⟨46553638409472316624827317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31035758939648211083218211 46553638409472316624827317)
              ·
                refine ⟨4364403600888029683577561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46553638409472316624827317 4364403600888029683577561)
                ·
                  refine ⟨3273302700666022262683171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4364403600888029683577561 3273302700666022262683171)
                  ·
                    refine ⟨4909954050999033394024757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3273302700666022262683171 4909954050999033394024757)
                    ·
                      refine ⟨460308192281159380689821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4909954050999033394024757 460308192281159380689821)
                      ·
                        rfl

theorem cell23_896447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_896447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896447 prefixEnd_896447 := by exact prefixLift 896447
  have htrace : WordTrace (prefixWord ++ tailWord_896447) baseStart_896447 baseEnd_896447 := by
    simpa [prefixWord, tailWord_896447, baseEnd_896447] using wordTrace_append hprefix tailTrace_896447
  have hstable : (prefixWord ++ tailWord_896447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896447).length < 2 ^ (prefixWord ++ tailWord_896447).sum := by decide
  have hdescent : baseEnd_896447 < baseStart_896447 := by decide
  rcases family_descends (prefixWord ++ tailWord_896447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896448 : List Nat := [2, 1, 1, 2, 3, 1, 6, 1, 1, 3, 2]
def baseStart_896448 : Nat := 118140960795 + 896448 * 2 ^ 59
def prefixEnd_896448 : Nat := 4983230072969 + 3 ^ 40 * 896448 * 2
def baseEnd_896448 : Nat := 460308705761813876777317

theorem tailTrace_896448 : CollatzResearch.WordTrace tailWord_896448 prefixEnd_896448 460308705761813876777317 := by
  unfold tailWord_896448
  simp only [CollatzResearch.WordTrace]
  refine ⟨16348072328164735987252999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21797429770886314649670665 16348072328164735987252999)
  ·
    refine ⟨24522108492247103980879499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16348072328164735987252999 24522108492247103980879499)
    ·
      refine ⟨36783162738370655971319249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24522108492247103980879499 36783162738370655971319249)
      ·
        refine ⟨27587372053777991978489437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36783162738370655971319249 27587372053777991978489437)
        ·
          refine ⟨10345264520166746991933539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27587372053777991978489437 10345264520166746991933539)
          ·
            refine ⟨15517896780250120487900309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10345264520166746991933539 15517896780250120487900309)
            ·
              refine ⟨727401411574224397870327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15517896780250120487900309 727401411574224397870327)
              ·
                refine ⟨1091102117361336596805491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 727401411574224397870327 1091102117361336596805491)
                ·
                  refine ⟨1636653176042004895208237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1091102117361336596805491 1636653176042004895208237)
                  ·
                    refine ⟨613744941015751835703089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1636653176042004895208237 613744941015751835703089)
                    ·
                      refine ⟨460308705761813876777317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 613744941015751835703089 460308705761813876777317)
                      ·
                        rfl

theorem cell23_896448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 1, 3, 2].length) (baseStart_896448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896448 prefixEnd_896448 := by exact prefixLift 896448
  have htrace : WordTrace (prefixWord ++ tailWord_896448) baseStart_896448 baseEnd_896448 := by
    simpa [prefixWord, tailWord_896448, baseEnd_896448] using wordTrace_append hprefix tailTrace_896448
  have hstable : (prefixWord ++ tailWord_896448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896448).length < 2 ^ (prefixWord ++ tailWord_896448).sum := by decide
  have hdescent : baseEnd_896448 < baseStart_896448 := by decide
  rcases family_descends (prefixWord ++ tailWord_896448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896474 : List Nat := [3, 1, 1, 2, 3, 2, 2, 1, 2, 2, 4]
def baseStart_896474 : Nat := 118140960795 + 896474 * 2 ^ 59
def prefixEnd_896474 : Nat := 4983230072969 + 3 ^ 40 * 896474 * 2
def baseEnd_896474 : Nat := 460322056258830775052197

theorem tailTrace_896474 : CollatzResearch.WordTrace tailWord_896474 prefixEnd_896474 460322056258830775052197 := by
  unfold tailWord_896474
  simp only [CollatzResearch.WordTrace]
  refine ⟨8174273238558819603738119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21798061969490185609968317 8174273238558819603738119)
  ·
    refine ⟨12261409857838229405607179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8174273238558819603738119 12261409857838229405607179)
    ·
      refine ⟨18392114786757344108410769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12261409857838229405607179 18392114786757344108410769)
      ·
        refine ⟨13794086090068008081308077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18392114786757344108410769 13794086090068008081308077)
        ·
          refine ⟨5172782283775503030490529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13794086090068008081308077 5172782283775503030490529)
          ·
            refine ⟨3879586712831627272867897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5172782283775503030490529 3879586712831627272867897)
            ·
              refine ⟨2909690034623720454650923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3879586712831627272867897 2909690034623720454650923)
              ·
                refine ⟨4364535051935580681976385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2909690034623720454650923 4364535051935580681976385)
                ·
                  refine ⟨3273401288951685511482289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4364535051935580681976385 3273401288951685511482289)
                  ·
                    refine ⟨2455050966713764133611717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3273401288951685511482289 2455050966713764133611717)
                    ·
                      refine ⟨460322056258830775052197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2455050966713764133611717 460322056258830775052197)
                      ·
                        rfl

theorem cell23_896474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_896474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896474 prefixEnd_896474 := by exact prefixLift 896474
  have htrace : WordTrace (prefixWord ++ tailWord_896474) baseStart_896474 baseEnd_896474 := by
    simpa [prefixWord, tailWord_896474, baseEnd_896474] using wordTrace_append hprefix tailTrace_896474
  have hstable : (prefixWord ++ tailWord_896474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896474).length < 2 ^ (prefixWord ++ tailWord_896474).sum := by decide
  have hdescent : baseEnd_896474 < baseStart_896474 := by decide
  rcases family_descends (prefixWord ++ tailWord_896474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896507 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 5]
def baseStart_896507 : Nat := 118140960795 + 896507 * 2 ^ 59
def prefixEnd_896507 : Nat := 4983230072969 + 3 ^ 40 * 896507 * 2
def baseEnd_896507 : Nat := 460339001120429145939545

theorem tailTrace_896507 : CollatzResearch.WordTrace tailWord_896507 prefixEnd_896507 460339001120429145939545 := by
  unfold tailWord_896507
  simp only [CollatzResearch.WordTrace]
  refine ⟨32698296563115725050903775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21798864375410483367269183 32698296563115725050903775)
  ·
    refine ⟨49047444844673587576355663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32698296563115725050903775 49047444844673587576355663)
    ·
      refine ⟨73571167267010381364533495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49047444844673587576355663 73571167267010381364533495)
      ·
        refine ⟨110356750900515572046800243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73571167267010381364533495 110356750900515572046800243)
        ·
          refine ⟨165535126350773358070200365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110356750900515572046800243 165535126350773358070200365)
          ·
            refine ⟨62075672381540009276325137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165535126350773358070200365 62075672381540009276325137)
            ·
              refine ⟨46556754286155006957243853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62075672381540009276325137 46556754286155006957243853)
              ·
                refine ⟨17458782857308127608966445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46556754286155006957243853 17458782857308127608966445)
                ·
                  refine ⟨6547043571490547853362417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17458782857308127608966445 6547043571490547853362417)
                  ·
                    refine ⟨4910282678617910890021813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6547043571490547853362417 4910282678617910890021813)
                    ·
                      refine ⟨460339001120429145939545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4910282678617910890021813 460339001120429145939545)
                      ·
                        rfl

theorem cell23_896507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 5].length) (baseStart_896507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896507 prefixEnd_896507 := by exact prefixLift 896507
  have htrace : WordTrace (prefixWord ++ tailWord_896507) baseStart_896507 baseEnd_896507 := by
    simpa [prefixWord, tailWord_896507, baseEnd_896507] using wordTrace_append hprefix tailTrace_896507
  have hstable : (prefixWord ++ tailWord_896507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896507).length < 2 ^ (prefixWord ++ tailWord_896507).sum := by decide
  have hdescent : baseEnd_896507 < baseStart_896507 := by decide
  rcases family_descends (prefixWord ++ tailWord_896507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896584 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 4, 5, 3]
def baseStart_896584 : Nat := 118140960795 + 896584 * 2 ^ 59
def prefixEnd_896584 : Nat := 4983230072969 + 3 ^ 40 * 896584 * 2
def baseEnd_896584 : Nat := 460378539130825344676691

theorem tailTrace_896584 : CollatzResearch.WordTrace tailWord_896584 prefixEnd_896584 460378539130825344676691 := by
  unfold tailWord_896584
  simp only [CollatzResearch.WordTrace]
  refine ⟨16350552491918383600728403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21800736655891178134304537 16350552491918383600728403)
  ·
    refine ⟨24525828737877575401092605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16350552491918383600728403 24525828737877575401092605)
    ·
      refine ⟨9197185776704090775409727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24525828737877575401092605 9197185776704090775409727)
      ·
        refine ⟨13795778665056136163114591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9197185776704090775409727 13795778665056136163114591)
        ·
          refine ⟨20693667997584204244671887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13795778665056136163114591 20693667997584204244671887)
          ·
            refine ⟨31040501996376306367007831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20693667997584204244671887 31040501996376306367007831)
            ·
              refine ⟨46560752994564459550511747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31040501996376306367007831 46560752994564459550511747)
              ·
                refine ⟨69841129491846689325767621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46560752994564459550511747 69841129491846689325767621)
                ·
                  refine ⟨13095211779721254248581429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69841129491846689325767621 13095211779721254248581429)
                  ·
                    refine ⟨1227676104348867585804509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13095211779721254248581429 1227676104348867585804509)
                    ·
                      refine ⟨460378539130825344676691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1227676104348867585804509 460378539130825344676691)
                      ·
                        rfl

theorem cell23_896584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_896584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896584 prefixEnd_896584 := by exact prefixLift 896584
  have htrace : WordTrace (prefixWord ++ tailWord_896584) baseStart_896584 baseEnd_896584 := by
    simpa [prefixWord, tailWord_896584, baseEnd_896584] using wordTrace_append hprefix tailTrace_896584
  have hstable : (prefixWord ++ tailWord_896584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896584).length < 2 ^ (prefixWord ++ tailWord_896584).sum := by decide
  have hdescent : baseEnd_896584 < baseStart_896584 := by decide
  rcases family_descends (prefixWord ++ tailWord_896584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896605 : List Nat := [1, 4, 4, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_896605 : Nat := 118140960795 + 896605 * 2 ^ 59
def prefixEnd_896605 : Nat := 4983230072969 + 3 ^ 40 * 896605 * 2
def baseEnd_896605 : Nat := 460389322224569762514095

theorem tailTrace_896605 : CollatzResearch.WordTrace tailWord_896605 prefixEnd_896605 460389322224569762514095 := by
  unfold tailWord_896605
  simp only [CollatzResearch.WordTrace]
  refine ⟨32701870916760687787971269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21801247277840458525314179 32701870916760687787971269)
  ·
    refine ⟨6131600796892628960244613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32701870916760687787971269 6131600796892628960244613)
    ·
      refine ⟨1149675149417367930045865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6131600796892628960244613 1149675149417367930045865)
      ·
        refine ⟨862256362063025947534399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1149675149417367930045865 862256362063025947534399)
        ·
          refine ⟨1293384543094538921301599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 862256362063025947534399 1293384543094538921301599)
          ·
            refine ⟨1940076814641808381952399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1293384543094538921301599 1940076814641808381952399)
            ·
              refine ⟨2910115221962712572928599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1940076814641808381952399 2910115221962712572928599)
              ·
                refine ⟨4365172832944068859392899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2910115221962712572928599 4365172832944068859392899)
                ·
                  refine ⟨6547759249416103289089349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4365172832944068859392899 6547759249416103289089349)
                  ·
                    refine ⟨1227704859265519366704253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6547759249416103289089349 1227704859265519366704253)
                    ·
                      refine ⟨460389322224569762514095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1227704859265519366704253 460389322224569762514095)
                      ·
                        rfl

theorem cell23_896605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_896605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896605 prefixEnd_896605 := by exact prefixLift 896605
  have htrace : WordTrace (prefixWord ++ tailWord_896605) baseStart_896605 baseEnd_896605 := by
    simpa [prefixWord, tailWord_896605, baseEnd_896605] using wordTrace_append hprefix tailTrace_896605
  have hstable : (prefixWord ++ tailWord_896605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896605).length < 2 ^ (prefixWord ++ tailWord_896605).sum := by decide
  have hdescent : baseEnd_896605 < baseStart_896605 := by decide
  rcases family_descends (prefixWord ++ tailWord_896605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896661 : List Nat := [1, 3, 2, 1, 1, 1, 1, 5, 3, 2, 3]
def baseStart_896661 : Nat := 118140960795 + 896661 * 2 ^ 59
def prefixEnd_896661 : Nat := 4983230072969 + 3 ^ 40 * 896661 * 2
def baseEnd_896661 : Nat := 460418077141221543413837

theorem tailTrace_896661 : CollatzResearch.WordTrace tailWord_896661 prefixEnd_896661 460418077141221543413837 := by
  unfold tailWord_896661
  simp only [CollatzResearch.WordTrace]
  refine ⟨32703913404557809352009837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21802608936371872901339891 32703913404557809352009837)
  ·
    refine ⟨12263967526709178507003689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32703913404557809352009837 12263967526709178507003689)
    ·
      refine ⟨9197975645031883880252767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12263967526709178507003689 9197975645031883880252767)
      ·
        refine ⟨13796963467547825820379151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9197975645031883880252767 13796963467547825820379151)
        ·
          refine ⟨20695445201321738730568727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13796963467547825820379151 20695445201321738730568727)
          ·
            refine ⟨31043167801982608095853091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20695445201321738730568727 31043167801982608095853091)
            ·
              refine ⟨46564751702973912143779637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31043167801982608095853091 46564751702973912143779637)
              ·
                refine ⟨4365445472153804263479341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46564751702973912143779637 4365445472153804263479341)
                ·
                  refine ⟨1637042052057676598804753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4365445472153804263479341 1637042052057676598804753)
                  ·
                    refine ⟨1227781539043257449103565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1637042052057676598804753 1227781539043257449103565)
                    ·
                      refine ⟨460418077141221543413837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1227781539043257449103565 460418077141221543413837)
                      ·
                        rfl

theorem cell23_896661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_896661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896661 prefixEnd_896661 := by exact prefixLift 896661
  have htrace : WordTrace (prefixWord ++ tailWord_896661) baseStart_896661 baseEnd_896661 := by
    simpa [prefixWord, tailWord_896661, baseEnd_896661] using wordTrace_append hprefix tailTrace_896661
  have hstable : (prefixWord ++ tailWord_896661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896661).length < 2 ^ (prefixWord ++ tailWord_896661).sum := by decide
  have hdescent : baseEnd_896661 < baseStart_896661 := by decide
  rcases family_descends (prefixWord ++ tailWord_896661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896686 : List Nat := [4, 1, 4, 1, 2, 1, 3, 2, 1, 1, 3]
def baseStart_896686 : Nat := 118140960795 + 896686 * 2 ^ 59
def prefixEnd_896686 : Nat := 4983230072969 + 3 ^ 40 * 896686 * 2
def baseEnd_896686 : Nat := 460430914157583945601223

theorem tailTrace_896686 : CollatzResearch.WordTrace tailWord_896686 prefixEnd_896686 460430914157583945601223 := by
  unfold tailWord_896686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4088103153683404827708739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21803216819644825747779941 4088103153683404827708739)
  ·
    refine ⟨6132154730525107241563109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4088103153683404827708739 6132154730525107241563109)
    ·
      refine ⟨1149779011973457607793083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6132154730525107241563109 1149779011973457607793083)
      ·
        refine ⟨1724668517960186411689625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1149779011973457607793083 1724668517960186411689625)
        ·
          refine ⟨1293501388470139808767219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1724668517960186411689625 1293501388470139808767219)
          ·
            refine ⟨1940252082705209713150829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1293501388470139808767219 1940252082705209713150829)
            ·
              refine ⟨727594531014453642431561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1940252082705209713150829 727594531014453642431561)
              ·
                refine ⟨545695898260840231823671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 727594531014453642431561 545695898260840231823671)
                ·
                  refine ⟨818543847391260347735507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 545695898260840231823671 818543847391260347735507)
                  ·
                    refine ⟨1227815771086890521603261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 818543847391260347735507 1227815771086890521603261)
                    ·
                      refine ⟨460430914157583945601223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1227815771086890521603261 460430914157583945601223)
                      ·
                        rfl

theorem cell23_896686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_896686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896686 prefixEnd_896686 := by exact prefixLift 896686
  have htrace : WordTrace (prefixWord ++ tailWord_896686) baseStart_896686 baseEnd_896686 := by
    simpa [prefixWord, tailWord_896686, baseEnd_896686] using wordTrace_append hprefix tailTrace_896686
  have hstable : (prefixWord ++ tailWord_896686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896686).length < 2 ^ (prefixWord ++ tailWord_896686).sum := by decide
  have hdescent : baseEnd_896686 < baseStart_896686 := by decide
  rcases family_descends (prefixWord ++ tailWord_896686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896702 : List Nat := [4, 2, 1, 1, 2, 4, 2, 1, 2, 4]
def baseStart_896702 : Nat := 118140960795 + 896702 * 2 ^ 59
def prefixEnd_896702 : Nat := 4983230072969 + 3 ^ 40 * 896702 * 2
def baseEnd_896702 : Nat := 153479709949351961000383

theorem tailTrace_896702 : CollatzResearch.WordTrace tailWord_896702 prefixEnd_896702 153479709949351961000383 := by
  unfold tailWord_896702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4088176099676159169281545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21803605864939515569501573 4088176099676159169281545)
  ·
    refine ⟨3066132074757119376961159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4088176099676159169281545 3066132074757119376961159)
    ·
      refine ⟨4599198112135679065441739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3066132074757119376961159 4599198112135679065441739)
      ·
        refine ⟨6898797168203518598162609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4599198112135679065441739 6898797168203518598162609)
        ·
          refine ⟨5174097876152638948621957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6898797168203518598162609 5174097876152638948621957)
          ·
            refine ⟨970143351778619802866617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5174097876152638948621957 970143351778619802866617)
            ·
              refine ⟨727607513833964852149963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 970143351778619802866617 727607513833964852149963)
              ·
                refine ⟨1091411270750947278224945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 727607513833964852149963 1091411270750947278224945)
                ·
                  refine ⟨818558453063210458668709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1091411270750947278224945 818558453063210458668709)
                  ·
                    refine ⟨153479709949351961000383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 818558453063210458668709 153479709949351961000383)
                    ·
                      rfl

theorem cell23_896702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_896702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896702 prefixEnd_896702 := by exact prefixLift 896702
  have htrace : WordTrace (prefixWord ++ tailWord_896702) baseStart_896702 baseEnd_896702 := by
    simpa [prefixWord, tailWord_896702, baseEnd_896702] using wordTrace_append hprefix tailTrace_896702
  have hstable : (prefixWord ++ tailWord_896702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896702).length < 2 ^ (prefixWord ++ tailWord_896702).sum := by decide
  have hdescent : baseEnd_896702 < baseStart_896702 := by decide
  rcases family_descends (prefixWord ++ tailWord_896702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896706 : List Nat := [3, 5, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_896706 : Nat := 118140960795 + 896706 * 2 ^ 59
def prefixEnd_896706 : Nat := 4983230072969 + 3 ^ 40 * 896706 * 2
def baseEnd_896706 : Nat := 153480394590224622450377

theorem tailTrace_896706 : CollatzResearch.WordTrace tailWord_896706 prefixEnd_896706 153480394590224622450377 := by
  unfold tailWord_896706
  simp only [CollatzResearch.WordTrace]
  refine ⟨8176388672348695509349493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21803703126263188024931981 8176388672348695509349493)
  ·
    refine ⟨766536438032690204001515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8176388672348695509349493 766536438032690204001515)
    ·
      refine ⟨1149804657049035306002273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 766536438032690204001515 1149804657049035306002273)
      ·
        refine ⟨862353492786776479501705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1149804657049035306002273 862353492786776479501705)
        ·
          refine ⟨646765119590082359626279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 862353492786776479501705 646765119590082359626279)
          ·
            refine ⟨970147679385123539439419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646765119590082359626279 970147679385123539439419)
            ·
              refine ⟨1455221519077685309159129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 970147679385123539439419 1455221519077685309159129)
              ·
                refine ⟨1091416139308263981869347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1455221519077685309159129 1091416139308263981869347)
                ·
                  refine ⟨1637124208962395972804021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1091416139308263981869347 1637124208962395972804021)
                  ·
                    refine ⟨153480394590224622450377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1637124208962395972804021 153480394590224622450377)
                    ·
                      rfl

theorem cell23_896706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_896706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896706 prefixEnd_896706 := by exact prefixLift 896706
  have htrace : WordTrace (prefixWord ++ tailWord_896706) baseStart_896706 baseEnd_896706 := by
    simpa [prefixWord, tailWord_896706, baseEnd_896706] using wordTrace_append hprefix tailTrace_896706
  have hstable : (prefixWord ++ tailWord_896706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896706).length < 2 ^ (prefixWord ++ tailWord_896706).sum := by decide
  have hdescent : baseEnd_896706 < baseStart_896706 := by decide
  rcases family_descends (prefixWord ++ tailWord_896706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896708 : List Nat := [2, 3, 3, 1, 1, 1, 2, 3, 1, 3, 3]
def baseStart_896708 : Nat := 118140960795 + 896708 * 2 ^ 59
def prefixEnd_896708 : Nat := 4983230072969 + 3 ^ 40 * 896708 * 2
def baseEnd_896708 : Nat := 460442210731982859526121

theorem tailTrace_896708 : CollatzResearch.WordTrace tailWord_896708 prefixEnd_896708 460442210731982859526121 := by
  unfold tailWord_896708
  simp only [CollatzResearch.WordTrace]
  refine ⟨16352813817693768189485389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21803751756925024252647185 16352813817693768189485389)
  ·
    refine ⟨6132305181635163071057021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16352813817693768189485389 6132305181635163071057021)
    ·
      refine ⟨2299614443113186151646383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6132305181635163071057021 2299614443113186151646383)
      ·
        refine ⟨3449421664669779227469575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2299614443113186151646383 3449421664669779227469575)
        ·
          refine ⟨5174132497004668841204363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3449421664669779227469575 5174132497004668841204363)
          ·
            refine ⟨7761198745507003261806545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5174132497004668841204363 7761198745507003261806545)
            ·
              refine ⟨5820899059130252446354909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7761198745507003261806545 5820899059130252446354909)
              ·
                refine ⟨2182837147173844667383091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5820899059130252446354909 2182837147173844667383091)
                ·
                  refine ⟨3274255720760767001074637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2182837147173844667383091 3274255720760767001074637)
                  ·
                    refine ⟨1227845895285287625402989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3274255720760767001074637 1227845895285287625402989)
                    ·
                      refine ⟨460442210731982859526121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1227845895285287625402989 460442210731982859526121)
                      ·
                        rfl

theorem cell23_896708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_896708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896708 prefixEnd_896708 := by exact prefixLift 896708
  have htrace : WordTrace (prefixWord ++ tailWord_896708) baseStart_896708 baseEnd_896708 := by
    simpa [prefixWord, tailWord_896708, baseEnd_896708] using wordTrace_append hprefix tailTrace_896708
  have hstable : (prefixWord ++ tailWord_896708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896708).length < 2 ^ (prefixWord ++ tailWord_896708).sum := by decide
  have hdescent : baseEnd_896708 < baseStart_896708 := by decide
  rcases family_descends (prefixWord ++ tailWord_896708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896741 : List Nat := [1, 3, 1, 4, 1, 1, 2, 2, 2, 6]
def baseStart_896741 : Nat := 118140960795 + 896741 * 2 ^ 59
def prefixEnd_896741 : Nat := 4983230072969 + 3 ^ 40 * 896741 * 2
def baseEnd_896741 : Nat := 153486385197860410137823

theorem tailTrace_896741 : CollatzResearch.WordTrace tailWord_896741 prefixEnd_896741 153486385197860410137823 := by
  unfold tailWord_896741
  simp only [CollatzResearch.WordTrace]
  refine ⟨32706831244267983014922077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21804554162845322009948051 32706831244267983014922077)
  ·
    refine ⟨12265061716600493630595779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32706831244267983014922077 12265061716600493630595779)
    ·
      refine ⟨18397592574900740445893669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12265061716600493630595779 18397592574900740445893669)
      ·
        refine ⟨3449548607793888833605063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18397592574900740445893669 3449548607793888833605063)
        ·
          refine ⟨5174322911690833250407595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3449548607793888833605063 5174322911690833250407595)
          ·
            refine ⟨7761484367536249875611393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5174322911690833250407595 7761484367536249875611393)
            ·
              refine ⟨5821113275652187406708545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7761484367536249875611393 5821113275652187406708545)
              ·
                refine ⟨4365834956739140555031409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5821113275652187406708545 4365834956739140555031409)
                ·
                  refine ⟨3274376217554355416273557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4365834956739140555031409 3274376217554355416273557)
                  ·
                    refine ⟨153486385197860410137823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3274376217554355416273557 153486385197860410137823)
                    ·
                      rfl

theorem cell23_896741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 6].length) (baseStart_896741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896741 prefixEnd_896741 := by exact prefixLift 896741
  have htrace : WordTrace (prefixWord ++ tailWord_896741) baseStart_896741 baseEnd_896741 := by
    simpa [prefixWord, tailWord_896741, baseEnd_896741] using wordTrace_append hprefix tailTrace_896741
  have hstable : (prefixWord ++ tailWord_896741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896741).length < 2 ^ (prefixWord ++ tailWord_896741).sum := by decide
  have hdescent : baseEnd_896741 < baseStart_896741 := by decide
  rcases family_descends (prefixWord ++ tailWord_896741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896743 : List Nat := [1, 1, 5, 4, 1, 2, 2, 2, 1, 2, 2]
def baseStart_896743 : Nat := 118140960795 + 896743 * 2 ^ 59
def prefixEnd_896743 : Nat := 4983230072969 + 3 ^ 40 * 896743 * 2
def baseEnd_896743 : Nat := 460460182554890222588461

theorem tailTrace_896743 : CollatzResearch.WordTrace tailWord_896743 prefixEnd_896743 460460182554890222588461 := by
  unfold tailWord_896743
  simp only [CollatzResearch.WordTrace]
  refine ⟨32706904190260737356494883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21804602793507158237663255 32706904190260737356494883)
  ·
    refine ⟨49060356285391106034742325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32706904190260737356494883 49060356285391106034742325)
    ·
      refine ⟨4599408401755416190757093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49060356285391106034742325 4599408401755416190757093)
      ·
        refine ⟨862389075329140535766955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4599408401755416190757093 862389075329140535766955)
        ·
          refine ⟨1293583612993710803650433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 862389075329140535766955 1293583612993710803650433)
          ·
            refine ⟨970187709745283102737825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1293583612993710803650433 970187709745283102737825)
            ·
              refine ⟨727640782308962327053369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 970187709745283102737825 727640782308962327053369)
              ·
                refine ⟨545730586731721745290027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 727640782308962327053369 545730586731721745290027)
                ·
                  refine ⟨818595880097582617935041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 545730586731721745290027 818595880097582617935041)
                  ·
                    refine ⟨613946910073186963451281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 818595880097582617935041 613946910073186963451281)
                    ·
                      refine ⟨460460182554890222588461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 613946910073186963451281 460460182554890222588461)
                      ·
                        rfl

theorem cell23_896743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_896743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896743 prefixEnd_896743 := by exact prefixLift 896743
  have htrace : WordTrace (prefixWord ++ tailWord_896743) baseStart_896743 baseEnd_896743 := by
    simpa [prefixWord, tailWord_896743, baseEnd_896743] using wordTrace_append hprefix tailTrace_896743
  have hstable : (prefixWord ++ tailWord_896743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896743).length < 2 ^ (prefixWord ++ tailWord_896743).sum := by decide
  have hdescent : baseEnd_896743 < baseStart_896743 := by decide
  rcases family_descends (prefixWord ++ tailWord_896743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896751 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 1, 6, 3]
def baseStart_896751 : Nat := 118140960795 + 896751 * 2 ^ 59
def prefixEnd_896751 : Nat := 4983230072969 + 3 ^ 40 * 896751 * 2
def baseEnd_896751 : Nat := 460464290400126191288423

theorem tailTrace_896751 : CollatzResearch.WordTrace tailWord_896751 prefixEnd_896751 460464290400126191288423 := by
  unfold tailWord_896751
  simp only [CollatzResearch.WordTrace]
  refine ⟨32707195974231754722786107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21804797316154503148524071 32707195974231754722786107)
  ·
    refine ⟨49060793961347632084179161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32707195974231754722786107 49060793961347632084179161)
    ·
      refine ⟨36795595471010724063134371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49060793961347632084179161 36795595471010724063134371)
      ·
        refine ⟨55193393206516086094701557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36795595471010724063134371 55193393206516086094701557)
        ·
          refine ⟨5174380613110883071378271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55193393206516086094701557 5174380613110883071378271)
          ·
            refine ⟨7761570919666324607067407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5174380613110883071378271 7761570919666324607067407)
            ·
              refine ⟨11642356379499486910601111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7761570919666324607067407 11642356379499486910601111)
              ·
                refine ⟨17463534569249230365901667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11642356379499486910601111 17463534569249230365901667)
                ·
                  refine ⟨26195301853873845548852501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17463534569249230365901667 26195301853873845548852501)
                  ·
                    refine ⟨1227904774400336510102461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26195301853873845548852501 1227904774400336510102461)
                    ·
                      refine ⟨460464290400126191288423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1227904774400336510102461 460464290400126191288423)
                      ·
                        rfl

theorem cell23_896751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 6, 3].length) (baseStart_896751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896751 prefixEnd_896751 := by exact prefixLift 896751
  have htrace : WordTrace (prefixWord ++ tailWord_896751) baseStart_896751 baseEnd_896751 := by
    simpa [prefixWord, tailWord_896751, baseEnd_896751] using wordTrace_append hprefix tailTrace_896751
  have hstable : (prefixWord ++ tailWord_896751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896751).length < 2 ^ (prefixWord ++ tailWord_896751).sum := by decide
  have hdescent : baseEnd_896751 < baseStart_896751 := by decide
  rcases family_descends (prefixWord ++ tailWord_896751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896758 : List Nat := [5, 1, 1, 1, 1, 4, 1, 1, 2, 6]
def baseStart_896758 : Nat := 118140960795 + 896758 * 2 ^ 59
def prefixEnd_896758 : Nat := 4983230072969 + 3 ^ 40 * 896758 * 2
def baseEnd_896758 : Nat := 153489294921569221300297

theorem tailTrace_896758 : CollatzResearch.WordTrace tailWord_896758 prefixEnd_896758 153489294921569221300297 := by
  unfold tailWord_896758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2044215705325399682393183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21804967523470929945527285 2044215705325399682393183)
  ·
    refine ⟨3066323557988099523589775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2044215705325399682393183 3066323557988099523589775)
    ·
      refine ⟨4599485336982149285384663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3066323557988099523589775 4599485336982149285384663)
      ·
        refine ⟨6899228005473223928076995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4599485336982149285384663 6899228005473223928076995)
        ·
          refine ⟨10348842008209835892115493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6899228005473223928076995 10348842008209835892115493)
          ·
            refine ⟨1940407876539344229771655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10348842008209835892115493 1940407876539344229771655)
            ·
              refine ⟨2910611814809016344657483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1940407876539344229771655 2910611814809016344657483)
              ·
                refine ⟨4365917722213524516986225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2910611814809016344657483 4365917722213524516986225)
                ·
                  refine ⟨3274438291660143387739669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4365917722213524516986225 3274438291660143387739669)
                  ·
                    refine ⟨153489294921569221300297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3274438291660143387739669 153489294921569221300297)
                    ·
                      rfl

theorem cell23_896758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_896758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896758 prefixEnd_896758 := by exact prefixLift 896758
  have htrace : WordTrace (prefixWord ++ tailWord_896758) baseStart_896758 baseEnd_896758 := by
    simpa [prefixWord, tailWord_896758, baseEnd_896758] using wordTrace_append hprefix tailTrace_896758
  have hstable : (prefixWord ++ tailWord_896758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896758).length < 2 ^ (prefixWord ++ tailWord_896758).sum := by decide
  have hdescent : baseEnd_896758 < baseStart_896758 := by decide
  rcases family_descends (prefixWord ++ tailWord_896758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896786 : List Nat := [3, 2, 4, 1, 1, 3, 2, 1, 1, 3, 2]
def baseStart_896786 : Nat := 118140960795 + 896786 * 2 ^ 59
def prefixEnd_896786 : Nat := 4983230072969 + 3 ^ 40 * 896786 * 2
def baseEnd_896786 : Nat := 460482262223033554350763

theorem tailTrace_896786 : CollatzResearch.WordTrace tailWord_896786 prefixEnd_896786 460482262223033554350763 := by
  unfold tailWord_896786
  simp only [CollatzResearch.WordTrace]
  refine ⟨8177118132276238925077553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21805648352736637133540141 8177118132276238925077553)
  ·
    refine ⟨6132838599207179193808165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8177118132276238925077553 6132838599207179193808165)
    ·
      refine ⟨1149907237351346098839031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6132838599207179193808165 1149907237351346098839031)
      ·
        refine ⟨1724860856027019148258547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1149907237351346098839031 1724860856027019148258547)
        ·
          refine ⟨2587291284040528722387821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1724860856027019148258547 2587291284040528722387821)
          ·
            refine ⟨970234231515198270895433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2587291284040528722387821 970234231515198270895433)
            ·
              refine ⟨727675673636398703171575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 970234231515198270895433 727675673636398703171575)
              ·
                refine ⟨1091513510454598054757363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 727675673636398703171575 1091513510454598054757363)
                ·
                  refine ⟨1637270265681897082136045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1091513510454598054757363 1637270265681897082136045)
                  ·
                    refine ⟨613976349630711405801017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1637270265681897082136045 613976349630711405801017)
                    ·
                      refine ⟨460482262223033554350763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 613976349630711405801017 460482262223033554350763)
                      ·
                        rfl

theorem cell23_896786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_896786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896786 prefixEnd_896786 := by exact prefixLift 896786
  have htrace : WordTrace (prefixWord ++ tailWord_896786) baseStart_896786 baseEnd_896786 := by
    simpa [prefixWord, tailWord_896786, baseEnd_896786] using wordTrace_append hprefix tailTrace_896786
  have hstable : (prefixWord ++ tailWord_896786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896786).length < 2 ^ (prefixWord ++ tailWord_896786).sum := by decide
  have hdescent : baseEnd_896786 < baseStart_896786 := by decide
  rcases family_descends (prefixWord ++ tailWord_896786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896855 : List Nat := [1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 4]
def baseStart_896855 : Nat := 118140960795 + 896855 * 2 ^ 59
def prefixEnd_896855 : Nat := 4983230072969 + 3 ^ 40 * 896855 * 2
def baseEnd_896855 : Nat := 460517692388193784387945

theorem tailTrace_896855 : CollatzResearch.WordTrace tailWord_896855 prefixEnd_896855 460517692388193784387945 := by
  unfold tailWord_896855
  simp only [CollatzResearch.WordTrace]
  refine ⟨32710989165854980484572019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21807326110569986989714679 32710989165854980484572019)
  ·
    refine ⟨49066483748782470726858029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32710989165854980484572019 49066483748782470726858029)
    ·
      refine ⟨18399931405793426522571761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49066483748782470726858029 18399931405793426522571761)
      ·
        refine ⟨13799948554345069891928821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18399931405793426522571761 13799948554345069891928821)
        ·
          refine ⟨1293745176969850302368327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13799948554345069891928821 1293745176969850302368327)
          ·
            refine ⟨1940617765454775453552491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1293745176969850302368327 1940617765454775453552491)
            ·
              refine ⟨2910926648182163180328737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1940617765454775453552491 2910926648182163180328737)
              ·
                refine ⟨2183194986136622385246553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2910926648182163180328737 2183194986136622385246553)
                ·
                  refine ⟨1637396239602466788934915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2183194986136622385246553 1637396239602466788934915)
                  ·
                    refine ⟨2456094359403700183402373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1637396239602466788934915 2456094359403700183402373)
                    ·
                      refine ⟨460517692388193784387945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2456094359403700183402373 460517692388193784387945)
                      ·
                        rfl

theorem cell23_896855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_896855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896855 prefixEnd_896855 := by exact prefixLift 896855
  have htrace : WordTrace (prefixWord ++ tailWord_896855) baseStart_896855 baseEnd_896855 := by
    simpa [prefixWord, tailWord_896855, baseEnd_896855] using wordTrace_append hprefix tailTrace_896855
  have hstable : (prefixWord ++ tailWord_896855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896855).length < 2 ^ (prefixWord ++ tailWord_896855).sum := by decide
  have hdescent : baseEnd_896855 < baseStart_896855 := by decide
  rcases family_descends (prefixWord ++ tailWord_896855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896916 : List Nat := [2, 4, 2, 1, 1, 4, 2, 2, 1, 4]
def baseStart_896916 : Nat := 118140960795 + 896916 * 2 ^ 59
def prefixEnd_896916 : Nat := 4983230072969 + 3 ^ 40 * 896916 * 2
def baseEnd_896916 : Nat := 153516338236039348575055

theorem tailTrace_896916 : CollatzResearch.WordTrace tailWord_896916 prefixEnd_896916 153516338236039348575055 := by
  unfold tailWord_896916
  simp only [CollatzResearch.WordTrace]
  refine ⟨16356607009316993951271301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21808809345755991935028401 16356607009316993951271301)
  ·
    refine ⟨3066863814246936365863369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16356607009316993951271301 3066863814246936365863369)
    ·
      refine ⟨2300147860685202274397527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3066863814246936365863369 2300147860685202274397527)
      ·
        refine ⟨3450221791027803411596291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2300147860685202274397527 3450221791027803411596291)
        ·
          refine ⟨5175332686541705117394437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3450221791027803411596291 5175332686541705117394437)
          ·
            refine ⟨970374878726569709511457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5175332686541705117394437 970374878726569709511457)
            ·
              refine ⟨727781159044927282133593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 970374878726569709511457 727781159044927282133593)
              ·
                refine ⟨545835869283695461600195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 727781159044927282133593 545835869283695461600195)
                ·
                  refine ⟨818753803925543192400293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 545835869283695461600195 818753803925543192400293)
                  ·
                    refine ⟨153516338236039348575055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 818753803925543192400293 153516338236039348575055)
                    ·
                      rfl

theorem cell23_896916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_896916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896916 prefixEnd_896916 := by exact prefixLift 896916
  have htrace : WordTrace (prefixWord ++ tailWord_896916) baseStart_896916 baseEnd_896916 := by
    simpa [prefixWord, tailWord_896916, baseEnd_896916] using wordTrace_append hprefix tailTrace_896916
  have hstable : (prefixWord ++ tailWord_896916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896916).length < 2 ^ (prefixWord ++ tailWord_896916).sum := by decide
  have hdescent : baseEnd_896916 < baseStart_896916 := by decide
  rcases family_descends (prefixWord ++ tailWord_896916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896945 : List Nat := [1, 2, 2, 4, 2, 1, 2, 1, 3, 1, 4]
def baseStart_896945 : Nat := 118140960795 + 896945 * 2 ^ 59
def prefixEnd_896945 : Nat := 4983230072969 + 3 ^ 40 * 896945 * 2
def baseEnd_896945 : Nat := 460563905647098432262531

theorem tailTrace_896945 : CollatzResearch.WordTrace tailWord_896945 prefixEnd_896945 460563905647098432262531 := by
  unfold tailWord_896945
  simp only [CollatzResearch.WordTrace]
  refine ⟨32714271735528925855348289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21809514490352617236898859 32714271735528925855348289)
  ·
    refine ⟨24535703801646694391511217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32714271735528925855348289 24535703801646694391511217)
    ·
      refine ⟨18401777851235020793633413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24535703801646694391511217 18401777851235020793633413)
      ·
        refine ⟨3450333347106566398806265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18401777851235020793633413 3450333347106566398806265)
        ·
          refine ⟨2587750010329924799104699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3450333347106566398806265 2587750010329924799104699)
          ·
            refine ⟨3881625015494887198657049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2587750010329924799104699 3881625015494887198657049)
            ·
              refine ⟨2911218761621165398992787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3881625015494887198657049 2911218761621165398992787)
              ·
                refine ⟨4366828142431748098489181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2911218761621165398992787 4366828142431748098489181)
                ·
                  refine ⟨1637560553411905536933443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4366828142431748098489181 1637560553411905536933443)
                  ·
                    refine ⟨2456340830117858305400165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1637560553411905536933443 2456340830117858305400165)
                    ·
                      refine ⟨460563905647098432262531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2456340830117858305400165 460563905647098432262531)
                      ·
                        rfl

theorem cell23_896945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_896945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896945 prefixEnd_896945 := by exact prefixLift 896945
  have htrace : WordTrace (prefixWord ++ tailWord_896945) baseStart_896945 baseEnd_896945 := by
    simpa [prefixWord, tailWord_896945, baseEnd_896945] using wordTrace_append hprefix tailTrace_896945
  have hstable : (prefixWord ++ tailWord_896945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896945).length < 2 ^ (prefixWord ++ tailWord_896945).sum := by decide
  have hdescent : baseEnd_896945 < baseStart_896945 := by decide
  rcases family_descends (prefixWord ++ tailWord_896945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896949 : List Nat := [1, 3, 3, 2, 1, 4, 1, 1, 2, 3, 2]
def baseStart_896949 : Nat := 118140960795 + 896949 * 2 ^ 59
def prefixEnd_896949 : Nat := 4983230072969 + 3 ^ 40 * 896949 * 2
def baseEnd_896949 : Nat := 460565959569716416612513

theorem tailTrace_896949 : CollatzResearch.WordTrace tailWord_896949 prefixEnd_896949 460565959569716416612513 := by
  unfold tailWord_896949
  simp only [CollatzResearch.WordTrace]
  refine ⟨32714417627514434538493901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21809611751676289692329267 32714417627514434538493901)
  ·
    refine ⟨12267906610317912951935213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32714417627514434538493901 12267906610317912951935213)
    ·
      refine ⟨4600464978869217356975705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12267906610317912951935213 4600464978869217356975705)
      ·
        refine ⟨3450348734151913017731779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4600464978869217356975705 3450348734151913017731779)
        ·
          refine ⟨5175523101227869526597669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3450348734151913017731779 5175523101227869526597669)
          ·
            refine ⟨970410581480225536237063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5175523101227869526597669 970410581480225536237063)
            ·
              refine ⟨1455615872220338304355595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 970410581480225536237063 1455615872220338304355595)
              ·
                refine ⟨2183423808330507456533393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1455615872220338304355595 2183423808330507456533393)
                ·
                  refine ⟨1637567856247880592400045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2183423808330507456533393 1637567856247880592400045)
                  ·
                    refine ⟨614087946092955222150017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1637567856247880592400045 614087946092955222150017)
                    ·
                      refine ⟨460565959569716416612513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 614087946092955222150017 460565959569716416612513)
                      ·
                        rfl

theorem cell23_896949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_896949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896949 prefixEnd_896949 := by exact prefixLift 896949
  have htrace : WordTrace (prefixWord ++ tailWord_896949) baseStart_896949 baseEnd_896949 := by
    simpa [prefixWord, tailWord_896949, baseEnd_896949] using wordTrace_append hprefix tailTrace_896949
  have hstable : (prefixWord ++ tailWord_896949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896949).length < 2 ^ (prefixWord ++ tailWord_896949).sum := by decide
  have hdescent : baseEnd_896949 < baseStart_896949 := by decide
  rcases family_descends (prefixWord ++ tailWord_896949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896968 : List Nat := [2, 1, 3, 1, 4, 2, 10]
def baseStart_896968 : Nat := 118140960795 + 896968 * 2 ^ 59
def prefixEnd_896968 : Nat := 4983230072969 + 3 ^ 40 * 896968 * 2
def baseEnd_896968 : Nat := 5686119946940146200925

theorem tailTrace_896968 : CollatzResearch.WordTrace tailWord_896968 prefixEnd_896968 5686119946940146200925 := by
  unfold tailWord_896968
  simp only [CollatzResearch.WordTrace]
  refine ⟨16357555307222800391717779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21810073742963733855623705 16357555307222800391717779)
  ·
    refine ⟨24536332960834200587576669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16357555307222800391717779 24536332960834200587576669)
    ·
      refine ⟨9201124860312825220341251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24536332960834200587576669 9201124860312825220341251)
      ·
        refine ⟨13801687290469237830511877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9201124860312825220341251 13801687290469237830511877)
        ·
          refine ⟨2587816366962982093220977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13801687290469237830511877 2587816366962982093220977)
          ·
            refine ⟨1940862275222236569915733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2587816366962982093220977 1940862275222236569915733)
            ·
              refine ⟨5686119946940146200925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1940862275222236569915733 5686119946940146200925)
              ·
                rfl

theorem cell23_896968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 10].length) (baseStart_896968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896968 prefixEnd_896968 := by exact prefixLift 896968
  have htrace : WordTrace (prefixWord ++ tailWord_896968) baseStart_896968 baseEnd_896968 := by
    simpa [prefixWord, tailWord_896968, baseEnd_896968] using wordTrace_append hprefix tailTrace_896968
  have hstable : (prefixWord ++ tailWord_896968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896968).length < 2 ^ (prefixWord ++ tailWord_896968).sum := by decide
  have hdescent : baseEnd_896968 < baseStart_896968 := by decide
  rcases family_descends (prefixWord ++ tailWord_896968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896972 : List Nat := [2, 2, 1, 4, 1, 2, 3, 2, 2, 4]
def baseStart_896972 : Nat := 118140960795 + 896972 * 2 ^ 59
def prefixEnd_896972 : Nat := 4983230072969 + 3 ^ 40 * 896972 * 2
def baseEnd_896972 : Nat := 153525923208256608874969

theorem tailTrace_896972 : CollatzResearch.WordTrace tailWord_896972 prefixEnd_896972 153525923208256608874969 := by
  unfold tailWord_896972
  simp only [CollatzResearch.WordTrace]
  refine ⟨16357628253215554733290585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21810171004287406311054113 16357628253215554733290585)
  ·
    refine ⟨12268221189911666049967939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16357628253215554733290585 12268221189911666049967939)
    ·
      refine ⟨18402331784867499074951909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12268221189911666049967939 18402331784867499074951909)
      ·
        refine ⟨3450437209662656076553483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18402331784867499074951909 3450437209662656076553483)
        ·
          refine ⟨5175655814493984114830225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3450437209662656076553483 5175655814493984114830225)
          ·
            refine ⟨3881741860870488086122669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5175655814493984114830225 3881741860870488086122669)
            ·
              refine ⟨1455653197826433032296001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3881741860870488086122669 1455653197826433032296001)
              ·
                refine ⟨1091739898369824774222001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1455653197826433032296001 1091739898369824774222001)
                ·
                  refine ⟨818804923777368580666501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1091739898369824774222001 818804923777368580666501)
                  ·
                    refine ⟨153525923208256608874969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 818804923777368580666501 153525923208256608874969)
                    ·
                      rfl

theorem cell23_896972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 2, 4].length) (baseStart_896972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896972 prefixEnd_896972 := by exact prefixLift 896972
  have htrace : WordTrace (prefixWord ++ tailWord_896972) baseStart_896972 baseEnd_896972 := by
    simpa [prefixWord, tailWord_896972, baseEnd_896972] using wordTrace_append hprefix tailTrace_896972
  have hstable : (prefixWord ++ tailWord_896972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896972).length < 2 ^ (prefixWord ++ tailWord_896972).sum := by decide
  have hdescent : baseEnd_896972 < baseStart_896972 := by decide
  rcases family_descends (prefixWord ++ tailWord_896972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896989 : List Nat := [1, 4, 3, 1, 4, 1, 1, 1, 1, 6]
def baseStart_896989 : Nat := 118140960795 + 896989 * 2 ^ 59
def prefixEnd_896989 : Nat := 4983230072969 + 3 ^ 40 * 896989 * 2
def baseEnd_896989 : Nat := 153528832931965420037443

theorem tailTrace_896989 : CollatzResearch.WordTrace tailWord_896989 prefixEnd_896989 153528832931965420037443 := by
  unfold tailWord_896989
  simp only [CollatzResearch.WordTrace]
  refine ⟨32715876547369521369950021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21810584364913014246633347 32715876547369521369950021)
  ·
    refine ⟨6134226852631785256865629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32715876547369521369950021 6134226852631785256865629)
    ·
      refine ⟨2300335069736919471324611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6134226852631785256865629 2300335069736919471324611)
      ·
        refine ⟨3450502604605379206986917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2300335069736919471324611 3450502604605379206986917)
        ·
          refine ⟨646969238363508601310047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3450502604605379206986917 646969238363508601310047)
          ·
            refine ⟨970453857545262901965071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646969238363508601310047 970453857545262901965071)
            ·
              refine ⟨1455680786317894352947607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 970453857545262901965071 1455680786317894352947607)
              ·
                refine ⟨2183521179476841529421411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1455680786317894352947607 2183521179476841529421411)
                ·
                  refine ⟨3275281769215262294132117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2183521179476841529421411 3275281769215262294132117)
                  ·
                    refine ⟨153528832931965420037443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3275281769215262294132117 153528832931965420037443)
                    ·
                      rfl

theorem cell23_896989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_896989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896989 prefixEnd_896989 := by exact prefixLift 896989
  have htrace : WordTrace (prefixWord ++ tailWord_896989) baseStart_896989 baseEnd_896989 := by
    simpa [prefixWord, tailWord_896989, baseEnd_896989] using wordTrace_append hprefix tailTrace_896989
  have hstable : (prefixWord ++ tailWord_896989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896989).length < 2 ^ (prefixWord ++ tailWord_896989).sum := by decide
  have hdescent : baseEnd_896989 < baseStart_896989 := by decide
  rcases family_descends (prefixWord ++ tailWord_896989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896999 : List Nat := [1, 1, 5, 2, 3, 1, 2, 2, 1, 2, 3]
def baseStart_896999 : Nat := 118140960795 + 896999 * 2 ^ 59
def prefixEnd_896999 : Nat := 4983230072969 + 3 ^ 40 * 896999 * 2
def baseEnd_896999 : Nat := 460591633602441220987283

theorem tailTrace_896999 : CollatzResearch.WordTrace tailWord_896999 prefixEnd_896999 460591633602441220987283 := by
  unfold tailWord_896999
  simp only [CollatzResearch.WordTrace]
  refine ⟨32716241277333293077814051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21810827518222195385209367 32716241277333293077814051)
  ·
    refine ⟨49074361915999939616721077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32716241277333293077814051 49074361915999939616721077)
    ·
      refine ⟨4600721429624994339067601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49074361915999939616721077 4600721429624994339067601)
      ·
        refine ⟨3450541072218745754300701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4600721429624994339067601 3450541072218745754300701)
        ·
          refine ⟨1293952902082029657862763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3450541072218745754300701 1293952902082029657862763)
          ·
            refine ⟨1940929353123044486794145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1293952902082029657862763 1940929353123044486794145)
            ·
              refine ⟨1455697014842283365095609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1940929353123044486794145 1455697014842283365095609)
              ·
                refine ⟨1091772761131712523821707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1455697014842283365095609 1091772761131712523821707)
                ·
                  refine ⟨1637659141697568785732561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1091772761131712523821707 1637659141697568785732561)
                  ·
                    refine ⟨1228244356273176589299421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1637659141697568785732561 1228244356273176589299421)
                    ·
                      refine ⟨460591633602441220987283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1228244356273176589299421 460591633602441220987283)
                      ·
                        rfl

theorem cell23_896999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_896999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_896999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_896999 prefixEnd_896999 := by exact prefixLift 896999
  have htrace : WordTrace (prefixWord ++ tailWord_896999) baseStart_896999 baseEnd_896999 := by
    simpa [prefixWord, tailWord_896999, baseEnd_896999] using wordTrace_append hprefix tailTrace_896999
  have hstable : (prefixWord ++ tailWord_896999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896999).length < 2 ^ (prefixWord ++ tailWord_896999).sum := by decide
  have hdescent : baseEnd_896999 < baseStart_896999 := by decide
  rcases family_descends (prefixWord ++ tailWord_896999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897008 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 5]
def baseStart_897008 : Nat := 118140960795 + 897008 * 2 ^ 59
def prefixEnd_897008 : Nat := 4983230072969 + 3 ^ 40 * 897008 * 2
def baseEnd_897008 : Nat := 460596254928331685774741

theorem tailTrace_897008 : CollatzResearch.WordTrace tailWord_897008 prefixEnd_897008 460596254928331685774741 := by
  unfold tailWord_897008
  simp only [CollatzResearch.WordTrace]
  refine ⟨16358284767150343807445839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21811046356200458409927785 16358284767150343807445839)
  ·
    refine ⟨24537427150725515711168759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16358284767150343807445839 24537427150725515711168759)
    ·
      refine ⟨36806140726088273566753139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24537427150725515711168759 36806140726088273566753139)
      ·
        refine ⟨55209211089132410350129709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36806140726088273566753139 55209211089132410350129709)
        ·
          refine ⟨20703454158424653881298641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55209211089132410350129709 20703454158424653881298641)
          ·
            refine ⟨15527590618818490410973981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20703454158424653881298641 15527590618818490410973981)
            ·
              refine ⟨5822846482056933904115243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15527590618818490410973981 5822846482056933904115243)
              ·
                refine ⟨8734269723085400856172865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5822846482056933904115243 8734269723085400856172865)
                ·
                  refine ⟨6550702292314050642129649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8734269723085400856172865 6550702292314050642129649)
                  ·
                    refine ⟨4913026719235537981597237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6550702292314050642129649 4913026719235537981597237)
                    ·
                      refine ⟨460596254928331685774741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4913026719235537981597237 460596254928331685774741)
                      ·
                        rfl

theorem cell23_897008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 5].length) (baseStart_897008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897008 prefixEnd_897008 := by exact prefixLift 897008
  have htrace : WordTrace (prefixWord ++ tailWord_897008) baseStart_897008 baseEnd_897008 := by
    simpa [prefixWord, tailWord_897008, baseEnd_897008] using wordTrace_append hprefix tailTrace_897008
  have hstable : (prefixWord ++ tailWord_897008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897008).length < 2 ^ (prefixWord ++ tailWord_897008).sum := by decide
  have hdescent : baseEnd_897008 < baseStart_897008 := by decide
  rcases family_descends (prefixWord ++ tailWord_897008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897018 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 3, 5, 4]
def baseStart_897018 : Nat := 118140960795 + 897018 * 2 ^ 59
def prefixEnd_897018 : Nat := 4983230072969 + 3 ^ 40 * 897018 * 2
def baseEnd_897018 : Nat := 460601389734876646649695

theorem tailTrace_897018 : CollatzResearch.WordTrace tailWord_897018 prefixEnd_897018 460601389734876646649695 := by
  unfold tailWord_897018
  simp only [CollatzResearch.WordTrace]
  refine ⟨8179233566066114830688927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21811289509509639548503805 8179233566066114830688927)
  ·
    refine ⟨12268850349099172246033391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8179233566066114830688927 12268850349099172246033391)
    ·
      refine ⟨18403275523648758369050087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12268850349099172246033391 18403275523648758369050087)
      ·
        refine ⟨27604913285473137553575131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18403275523648758369050087 27604913285473137553575131)
        ·
          refine ⟨41407369928209706330362697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27604913285473137553575131 41407369928209706330362697)
          ·
            refine ⟨31055527446157279747772023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41407369928209706330362697 31055527446157279747772023)
            ·
              refine ⟨46583291169235919621658035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31055527446157279747772023 46583291169235919621658035)
              ·
                refine ⟨69874936753853879432487053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46583291169235919621658035 69874936753853879432487053)
                ·
                  refine ⟨26203101282695204787182645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69874936753853879432487053 26203101282695204787182645)
                  ·
                    refine ⟨2456540745252675448798373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26203101282695204787182645 2456540745252675448798373)
                    ·
                      refine ⟨460601389734876646649695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2456540745252675448798373 460601389734876646649695)
                      ·
                        rfl

theorem cell23_897018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_897018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897018 prefixEnd_897018 := by exact prefixLift 897018
  have htrace : WordTrace (prefixWord ++ tailWord_897018) baseStart_897018 baseEnd_897018 := by
    simpa [prefixWord, tailWord_897018, baseEnd_897018] using wordTrace_append hprefix tailTrace_897018
  have hstable : (prefixWord ++ tailWord_897018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897018).length < 2 ^ (prefixWord ++ tailWord_897018).sum := by decide
  have hdescent : baseEnd_897018 < baseStart_897018 := by decide
  rcases family_descends (prefixWord ++ tailWord_897018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897068 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 7]
def baseStart_897068 : Nat := 118140960795 + 897068 * 2 ^ 59
def prefixEnd_897068 : Nat := 4983230072969 + 3 ^ 40 * 897068 * 2
def baseEnd_897068 : Nat := 460627063767601451024465

theorem tailTrace_897068 : CollatzResearch.WordTrace tailWord_897068 prefixEnd_897068 460627063767601451024465 := by
  unfold tailWord_897068
  simp only [CollatzResearch.WordTrace]
  refine ⟨16359378957041658931037929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21812505276055545241383905 16359378957041658931037929)
  ·
    refine ⟨12269534217781244198278447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16359378957041658931037929 12269534217781244198278447)
    ·
      refine ⟨18404301326671866297417671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12269534217781244198278447 18404301326671866297417671)
      ·
        refine ⟨27606451990007799446126507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18404301326671866297417671 27606451990007799446126507)
        ·
          refine ⟨41409677985011699169189761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27606451990007799446126507 41409677985011699169189761)
          ·
            refine ⟨31057258488758774376892321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41409677985011699169189761 31057258488758774376892321)
            ·
              refine ⟨23292943866569080782669241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31057258488758774376892321 23292943866569080782669241)
              ·
                refine ⟨17469707899926810587001931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23292943866569080782669241 17469707899926810587001931)
                ·
                  refine ⟨26204561849890215880502897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17469707899926810587001931 26204561849890215880502897)
                  ·
                    refine ⟨19653421387417661910377173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26204561849890215880502897 19653421387417661910377173)
                    ·
                      refine ⟨460627063767601451024465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19653421387417661910377173 460627063767601451024465)
                      ·
                        rfl

theorem cell23_897068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_897068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897068 prefixEnd_897068 := by exact prefixLift 897068
  have htrace : WordTrace (prefixWord ++ tailWord_897068) baseStart_897068 baseEnd_897068 := by
    simpa [prefixWord, tailWord_897068, baseEnd_897068] using wordTrace_append hprefix tailTrace_897068
  have hstable : (prefixWord ++ tailWord_897068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897068).length < 2 ^ (prefixWord ++ tailWord_897068).sum := by decide
  have hdescent : baseEnd_897068 < baseStart_897068 := by decide
  rcases family_descends (prefixWord ++ tailWord_897068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897102 : List Nat := [4, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3]
def baseStart_897102 : Nat := 118140960795 + 897102 * 2 ^ 59
def prefixEnd_897102 : Nat := 4983230072969 + 3 ^ 40 * 897102 * 2
def baseEnd_897102 : Nat := 460644522109854317999309

theorem tailTrace_897102 : CollatzResearch.WordTrace tailWord_897102 prefixEnd_897102 460644522109854317999309 := by
  unfold tailWord_897102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4089999749495017708601695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21813331997306761112542373 4089999749495017708601695)
  ·
    refine ⟨6134999624242526562902543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4089999749495017708601695 6134999624242526562902543)
    ·
      refine ⟨9202499436363789844353815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6134999624242526562902543 9202499436363789844353815)
      ·
        refine ⟨13803749154545684766530723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9202499436363789844353815 13803749154545684766530723)
        ·
          refine ⟨20705623731818527149796085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13803749154545684766530723 20705623731818527149796085)
          ·
            refine ⟨1941152224857986920293383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20705623731818527149796085 1941152224857986920293383)
            ·
              refine ⟨2911728337286980380440075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1941152224857986920293383 2911728337286980380440075)
              ·
                refine ⟨4367592505930470570660113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2911728337286980380440075 4367592505930470570660113)
                ·
                  refine ⟨3275694379447852927995085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4367592505930470570660113 3275694379447852927995085)
                  ·
                    refine ⟨1228385392292944847998157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3275694379447852927995085 1228385392292944847998157)
                    ·
                      refine ⟨460644522109854317999309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1228385392292944847998157 460644522109854317999309)
                      ·
                        rfl

theorem cell23_897102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_897102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897102 prefixEnd_897102 := by exact prefixLift 897102
  have htrace : WordTrace (prefixWord ++ tailWord_897102) baseStart_897102 baseEnd_897102 := by
    simpa [prefixWord, tailWord_897102, baseEnd_897102] using wordTrace_append hprefix tailTrace_897102
  have hstable : (prefixWord ++ tailWord_897102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897102).length < 2 ^ (prefixWord ++ tailWord_897102).sum := by decide
  have hdescent : baseEnd_897102 < baseStart_897102 := by decide
  rcases family_descends (prefixWord ++ tailWord_897102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897162 : List Nat := [3, 1, 2, 3, 1, 2, 1, 2, 1, 4, 3]
def baseStart_897162 : Nat := 118140960795 + 897162 * 2 ^ 59
def prefixEnd_897162 : Nat := 4983230072969 + 3 ^ 40 * 897162 * 2
def baseEnd_897162 : Nat := 460675330949124083249033

theorem tailTrace_897162 : CollatzResearch.WordTrace tailWord_897162 prefixEnd_897162 460675330949124083249033 := by
  unfold tailWord_897162
  simp only [CollatzResearch.WordTrace]
  refine ⟨8180546593935692978999435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21814790917161847943998493 8180546593935692978999435)
  ·
    refine ⟨12270819890903539468499153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8180546593935692978999435 12270819890903539468499153)
    ·
      refine ⟨9203114918177654601374365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12270819890903539468499153 9203114918177654601374365)
      ·
        refine ⟨3451168094316620475515387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9203114918177654601374365 3451168094316620475515387)
        ·
          refine ⟨5176752141474930713273081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3451168094316620475515387 5176752141474930713273081)
          ·
            refine ⟨3882564106106198034954811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5176752141474930713273081 3882564106106198034954811)
            ·
              refine ⟨5823846159159297052432217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3882564106106198034954811 5823846159159297052432217)
              ·
                refine ⟨4367884619369472789324163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5823846159159297052432217 4367884619369472789324163)
                ·
                  refine ⟨6551826929054209183986245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4367884619369472789324163 6551826929054209183986245)
                  ·
                    refine ⟨1228467549197664221997421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6551826929054209183986245 1228467549197664221997421)
                    ·
                      refine ⟨460675330949124083249033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1228467549197664221997421 460675330949124083249033)
                      ·
                        rfl

theorem cell23_897162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_897162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897162 prefixEnd_897162 := by exact prefixLift 897162
  have htrace : WordTrace (prefixWord ++ tailWord_897162) baseStart_897162 baseEnd_897162 := by
    simpa [prefixWord, tailWord_897162, baseEnd_897162] using wordTrace_append hprefix tailTrace_897162
  have hstable : (prefixWord ++ tailWord_897162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897162).length < 2 ^ (prefixWord ++ tailWord_897162).sum := by decide
  have hdescent : baseEnd_897162 < baseStart_897162 := by decide
  rcases family_descends (prefixWord ++ tailWord_897162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897215 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 4]
def baseStart_897215 : Nat := 118140960795 + 897215 * 2 ^ 59
def prefixEnd_897215 : Nat := 4983230072969 + 3 ^ 40 * 897215 * 2
def baseEnd_897215 : Nat := 460702545423812375886289

theorem tailTrace_897215 : CollatzResearch.WordTrace tailWord_897215 prefixEnd_897215 460702545423812375886289 := by
  unfold tailWord_897215
  simp only [CollatzResearch.WordTrace]
  refine ⟨32724119444550761967677099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21816079629700507978451399 32724119444550761967677099)
  ·
    refine ⟨49086179166826142951515649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32724119444550761967677099 49086179166826142951515649)
    ·
      refine ⟨36814634375119607213636737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49086179166826142951515649 36814634375119607213636737)
      ·
        refine ⟨27610975781339705410227553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36814634375119607213636737 27610975781339705410227553)
        ·
          refine ⟨20708231836004779057670665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27610975781339705410227553 20708231836004779057670665)
          ·
            refine ⟨15531173877003584293252999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20708231836004779057670665 15531173877003584293252999)
            ·
              refine ⟨23296760815505376439879499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15531173877003584293252999 23296760815505376439879499)
              ·
                refine ⟨34945141223258064659819249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23296760815505376439879499 34945141223258064659819249)
                ·
                  refine ⟨26208855917443548494864437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34945141223258064659819249 26208855917443548494864437)
                  ·
                    refine ⟨2457080242260332671393541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26208855917443548494864437 2457080242260332671393541)
                    ·
                      refine ⟨460702545423812375886289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2457080242260332671393541 460702545423812375886289)
                      ·
                        rfl

theorem cell23_897215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_897215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897215 prefixEnd_897215 := by exact prefixLift 897215
  have htrace : WordTrace (prefixWord ++ tailWord_897215) baseStart_897215 baseEnd_897215 := by
    simpa [prefixWord, tailWord_897215, baseEnd_897215] using wordTrace_append hprefix tailTrace_897215
  have hstable : (prefixWord ++ tailWord_897215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897215).length < 2 ^ (prefixWord ++ tailWord_897215).sum := by decide
  have hdescent : baseEnd_897215 < baseStart_897215 := by decide
  rcases family_descends (prefixWord ++ tailWord_897215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897242 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 6, 4]
def baseStart_897242 : Nat := 118140960795 + 897242 * 2 ^ 59
def prefixEnd_897242 : Nat := 4983230072969 + 3 ^ 40 * 897242 * 2
def baseEnd_897242 : Nat := 153572136467161256749555

theorem tailTrace_897242 : CollatzResearch.WordTrace tailWord_897242 prefixEnd_897242 153572136467161256749555 := by
  unfold tailWord_897242
  simp only [CollatzResearch.WordTrace]
  refine ⟨8181276053863236394727495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21816736143635297052606653 8181276053863236394727495)
  ·
    refine ⟨12271914080794854592091243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8181276053863236394727495 12271914080794854592091243)
    ·
      refine ⟨18407871121192281888136865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12271914080794854592091243 18407871121192281888136865)
      ·
        refine ⟨13805903340894211416102649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18407871121192281888136865 13805903340894211416102649)
        ·
          refine ⟨10354427505670658562076987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13805903340894211416102649 10354427505670658562076987)
          ·
            refine ⟨15531641258505987843115481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10354427505670658562076987 15531641258505987843115481)
            ·
              refine ⟨11648730943879490882336611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15531641258505987843115481 11648730943879490882336611)
              ·
                refine ⟨17473096415819236323504917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11648730943879490882336611 17473096415819236323504917)
                ·
                  refine ⟨819051394491526702664293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17473096415819236323504917 819051394491526702664293)
                  ·
                    refine ⟨153572136467161256749555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 819051394491526702664293 153572136467161256749555)
                    ·
                      rfl

theorem cell23_897242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 6, 4].length) (baseStart_897242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897242 prefixEnd_897242 := by exact prefixLift 897242
  have htrace : WordTrace (prefixWord ++ tailWord_897242) baseStart_897242 baseEnd_897242 := by
    simpa [prefixWord, tailWord_897242, baseEnd_897242] using wordTrace_append hprefix tailTrace_897242
  have hstable : (prefixWord ++ tailWord_897242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897242).length < 2 ^ (prefixWord ++ tailWord_897242).sum := by decide
  have hdescent : baseEnd_897242 < baseStart_897242 := by decide
  rcases family_descends (prefixWord ++ tailWord_897242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897259 : List Nat := [1, 1, 1, 1, 2, 5, 4, 2, 2, 4]
def baseStart_897259 : Nat := 118140960795 + 897259 * 2 ^ 59
def prefixEnd_897259 : Nat := 4983230072969 + 3 ^ 40 * 897259 * 2
def baseEnd_897259 : Nat := 153575046190870067912029

theorem tailTrace_897259 : CollatzResearch.WordTrace tailWord_897259 prefixEnd_897259 153575046190870067912029 := by
  unfold tailWord_897259
  simp only [CollatzResearch.WordTrace]
  refine ⟨32725724256391357482278831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21817149504260904988185887 32725724256391357482278831)
  ·
    refine ⟨49088586384587036223418247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32725724256391357482278831 49088586384587036223418247)
    ·
      refine ⟨73632879576880554335127371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49088586384587036223418247 73632879576880554335127371)
      ·
        refine ⟨110449319365320831502691057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73632879576880554335127371 110449319365320831502691057)
        ·
          refine ⟨82836989523990623627018293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110449319365320831502691057 82836989523990623627018293)
          ·
            refine ⟨7765967767874120965032965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82836989523990623627018293 7765967767874120965032965)
            ·
              refine ⟨1456118956476397680943681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7765967767874120965032965 1456118956476397680943681)
              ·
                refine ⟨1092089217357298260707761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1456118956476397680943681 1092089217357298260707761)
                ·
                  refine ⟨819066913017973695530821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1092089217357298260707761 819066913017973695530821)
                  ·
                    refine ⟨153575046190870067912029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 819066913017973695530821 153575046190870067912029)
                    ·
                      rfl

theorem cell23_897259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 2, 4].length) (baseStart_897259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897259 prefixEnd_897259 := by exact prefixLift 897259
  have htrace : WordTrace (prefixWord ++ tailWord_897259) baseStart_897259 baseEnd_897259 := by
    simpa [prefixWord, tailWord_897259, baseEnd_897259] using wordTrace_append hprefix tailTrace_897259
  have hstable : (prefixWord ++ tailWord_897259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897259).length < 2 ^ (prefixWord ++ tailWord_897259).sum := by decide
  have hdescent : baseEnd_897259 < baseStart_897259 := by decide
  rcases family_descends (prefixWord ++ tailWord_897259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897262 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 5, 2, 4]
def baseStart_897262 : Nat := 118140960795 + 897262 * 2 ^ 59
def prefixEnd_897262 : Nat := 4983230072969 + 3 ^ 40 * 897262 * 2
def baseEnd_897262 : Nat := 460726679014573691998573

theorem tailTrace_897262 : CollatzResearch.WordTrace tailWord_897262 prefixEnd_897262 460726679014573691998573 := by
  unfold tailWord_897262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4090729209422561124329755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21817222450253659329758693 4090729209422561124329755)
  ·
    refine ⟨6136093814133841686494633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4090729209422561124329755 6136093814133841686494633)
    ·
      refine ⟨4602070360600381264870975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6136093814133841686494633 4602070360600381264870975)
      ·
        refine ⟨6903105540900571897306463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4602070360600381264870975 6903105540900571897306463)
        ·
          refine ⟨10354658311350857845959695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6903105540900571897306463 10354658311350857845959695)
          ·
            refine ⟨15531987467026286768939543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10354658311350857845959695 15531987467026286768939543)
            ·
              refine ⟨23297981200539430153409315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15531987467026286768939543 23297981200539430153409315)
              ·
                refine ⟨34946971800809145230113973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23297981200539430153409315 34946971800809145230113973)
                ·
                  refine ⟨3276278606325857365323185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34946971800809145230113973 3276278606325857365323185)
                  ·
                    refine ⟨2457208954744393023992389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3276278606325857365323185 2457208954744393023992389)
                    ·
                      refine ⟨460726679014573691998573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2457208954744393023992389 460726679014573691998573)
                      ·
                        rfl

theorem cell23_897262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_897262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897262 prefixEnd_897262 := by exact prefixLift 897262
  have htrace : WordTrace (prefixWord ++ tailWord_897262) baseStart_897262 baseEnd_897262 := by
    simpa [prefixWord, tailWord_897262, baseEnd_897262] using wordTrace_append hprefix tailTrace_897262
  have hstable : (prefixWord ++ tailWord_897262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897262).length < 2 ^ (prefixWord ++ tailWord_897262).sum := by decide
  have hdescent : baseEnd_897262 < baseStart_897262 := by decide
  rcases family_descends (prefixWord ++ tailWord_897262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897303 : List Nat := [1, 1, 3, 4, 1, 4, 2, 1, 1, 2, 3]
def baseStart_897303 : Nat := 118140960795 + 897303 * 2 ^ 59
def prefixEnd_897303 : Nat := 4983230072969 + 3 ^ 40 * 897303 * 2
def baseEnd_897303 : Nat := 460747731721408031585885

theorem tailTrace_897303 : CollatzResearch.WordTrace tailWord_897303 prefixEnd_897303 460747731721408031585885 := by
  unfold tailWord_897303
  simp only [CollatzResearch.WordTrace]
  refine ⟨32727329068231952996880563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21818219378821301997920375 32727329068231952996880563)
  ·
    refine ⟨49090993602347929495320845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32727329068231952996880563 49090993602347929495320845)
    ·
      refine ⟨18409122600880473560745317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49090993602347929495320845 18409122600880473560745317)
      ·
        refine ⟨3451710487665088792639747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18409122600880473560745317 3451710487665088792639747)
        ·
          refine ⟨5177565731497633188959621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3451710487665088792639747 5177565731497633188959621)
          ·
            refine ⟨970793574655806222929929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5177565731497633188959621 970793574655806222929929)
            ·
              refine ⟨728095180991854667197447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 970793574655806222929929 728095180991854667197447)
              ·
                refine ⟨1092142771487782000796171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 728095180991854667197447 1092142771487782000796171)
                ·
                  refine ⟨1638214157231673001194257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1092142771487782000796171 1638214157231673001194257)
                  ·
                    refine ⟨1228660617923754750895693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1638214157231673001194257 1228660617923754750895693)
                    ·
                      refine ⟨460747731721408031585885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1228660617923754750895693 460747731721408031585885)
                      ·
                        rfl

theorem cell23_897303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_897303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897303 prefixEnd_897303 := by exact prefixLift 897303
  have htrace : WordTrace (prefixWord ++ tailWord_897303) baseStart_897303 baseEnd_897303 := by
    simpa [prefixWord, tailWord_897303, baseEnd_897303] using wordTrace_append hprefix tailTrace_897303
  have hstable : (prefixWord ++ tailWord_897303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897303).length < 2 ^ (prefixWord ++ tailWord_897303).sum := by decide
  have hdescent : baseEnd_897303 < baseStart_897303 := by decide
  rcases family_descends (prefixWord ++ tailWord_897303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897310 : List Nat := [4, 3, 2, 1, 1, 3, 1, 2, 2, 4]
def baseStart_897310 : Nat := 118140960795 + 897310 * 2 ^ 59
def prefixEnd_897310 : Nat := 4983230072969 + 3 ^ 40 * 897310 * 2
def baseEnd_897310 : Nat := 153583775361996501399451

theorem tailTrace_897310 : CollatzResearch.WordTrace tailWord_897310 prefixEnd_897310 153583775361996501399451 := by
  unfold tailWord_897310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4090948047400824149048173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21818389586137728794923589 4090948047400824149048173)
  ·
    refine ⟨1534105517775309055893065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4090948047400824149048173 1534105517775309055893065)
    ·
      refine ⟨1150579138331481791919799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1534105517775309055893065 1150579138331481791919799)
      ·
        refine ⟨1725868707497222687879699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1150579138331481791919799 1725868707497222687879699)
        ·
          refine ⟨2588803061245834031819549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1725868707497222687879699 2588803061245834031819549)
          ·
            refine ⟨970801147967187761932331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2588803061245834031819549 970801147967187761932331)
            ·
              refine ⟨1456201721950781642898497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 970801147967187761932331 1456201721950781642898497)
              ·
                refine ⟨1092151291463086232173873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1456201721950781642898497 1092151291463086232173873)
                ·
                  refine ⟨819113468597314674130405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1092151291463086232173873 819113468597314674130405)
                  ·
                    refine ⟨153583775361996501399451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 819113468597314674130405 153583775361996501399451)
                    ·
                      rfl

theorem cell23_897310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_897310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897310 prefixEnd_897310 := by exact prefixLift 897310
  have htrace : WordTrace (prefixWord ++ tailWord_897310) baseStart_897310 baseEnd_897310 := by
    simpa [prefixWord, tailWord_897310, baseEnd_897310] using wordTrace_append hprefix tailTrace_897310
  have hstable : (prefixWord ++ tailWord_897310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897310).length < 2 ^ (prefixWord ++ tailWord_897310).sum := by decide
  have hdescent : baseEnd_897310 < baseStart_897310 := by decide
  rcases family_descends (prefixWord ++ tailWord_897310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897316 : List Nat := [2, 3, 1, 3, 1, 3, 1, 1, 4, 1, 3]
def baseStart_897316 : Nat := 118140960795 + 897316 * 2 ^ 59
def prefixEnd_897316 : Nat := 4983230072969 + 3 ^ 40 * 897316 * 2
def baseEnd_897316 : Nat := 460754406969916480723325

theorem tailTrace_897316 : CollatzResearch.WordTrace tailWord_897316 prefixEnd_897316 460754406969916480723325 := by
  unfold tailWord_897316
  simp only [CollatzResearch.WordTrace]
  refine ⟨16363901608592428108551901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21818535478123237478069201 16363901608592428108551901)
  ·
    refine ⟨6136463103222160540706963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16363901608592428108551901 6136463103222160540706963)
    ·
      refine ⟨9204694654833240811060445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6136463103222160540706963 9204694654833240811060445)
      ·
        refine ⟨3451760495562465304147667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9204694654833240811060445 3451760495562465304147667)
        ·
          refine ⟨5177640743343697956221501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3451760495562465304147667 5177640743343697956221501)
          ·
            refine ⟨1941615278753886733583063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5177640743343697956221501 1941615278753886733583063)
            ·
              refine ⟨2912422918130830100374595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1941615278753886733583063 2912422918130830100374595)
              ·
                refine ⟨4368634377196245150561893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2912422918130830100374595 4368634377196245150561893)
                ·
                  refine ⟨819118945724295965730355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4368634377196245150561893 819118945724295965730355)
                  ·
                    refine ⟨1228678418586443948595533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 819118945724295965730355 1228678418586443948595533)
                    ·
                      refine ⟨460754406969916480723325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1228678418586443948595533 460754406969916480723325)
                      ·
                        rfl

theorem cell23_897316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_897316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897316 prefixEnd_897316 := by exact prefixLift 897316
  have htrace : WordTrace (prefixWord ++ tailWord_897316) baseStart_897316 baseEnd_897316 := by
    simpa [prefixWord, tailWord_897316, baseEnd_897316] using wordTrace_append hprefix tailTrace_897316
  have hstable : (prefixWord ++ tailWord_897316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897316).length < 2 ^ (prefixWord ++ tailWord_897316).sum := by decide
  have hdescent : baseEnd_897316 < baseStart_897316 := by decide
  rcases family_descends (prefixWord ++ tailWord_897316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897333 : List Nat := [1, 3, 3, 1, 2, 1, 5, 1, 2, 1, 3]
def baseStart_897333 : Nat := 118140960795 + 897333 * 2 ^ 59
def prefixEnd_897333 : Nat := 4983230072969 + 3 ^ 40 * 897333 * 2
def baseEnd_897333 : Nat := 460763136141042914210747

theorem tailTrace_897333 : CollatzResearch.WordTrace tailWord_897333 prefixEnd_897333 460763136141042914210747 := by
  unfold tailWord_897333
  simp only [CollatzResearch.WordTrace]
  refine ⟨32728423258123268120472653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21818948838748845413648435 32728423258123268120472653)
  ·
    refine ⟨12273158721796225545177245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32728423258123268120472653 12273158721796225545177245)
    ·
      refine ⟨4602434520673584579441467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12273158721796225545177245 4602434520673584579441467)
      ·
        refine ⟨6903651781010376869162201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4602434520673584579441467 6903651781010376869162201)
        ·
          refine ⟨5177738835757782651871651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6903651781010376869162201 5177738835757782651871651)
          ·
            refine ⟨7766608253636673977807477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5177738835757782651871651 7766608253636673977807477)
            ·
              refine ⟨728119523778438185419451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7766608253636673977807477 728119523778438185419451)
              ·
                refine ⟨1092179285667657278129177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 728119523778438185419451 1092179285667657278129177)
                ·
                  refine ⟨819134464250742958596883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1092179285667657278129177 819134464250742958596883)
                  ·
                    refine ⟨1228701696376114437895325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 819134464250742958596883 1228701696376114437895325)
                    ·
                      refine ⟨460763136141042914210747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1228701696376114437895325 460763136141042914210747)
                      ·
                        rfl

theorem cell23_897333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_897333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897333 prefixEnd_897333 := by exact prefixLift 897333
  have htrace : WordTrace (prefixWord ++ tailWord_897333) baseStart_897333 baseEnd_897333 := by
    simpa [prefixWord, tailWord_897333, baseEnd_897333] using wordTrace_append hprefix tailTrace_897333
  have hstable : (prefixWord ++ tailWord_897333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897333).length < 2 ^ (prefixWord ++ tailWord_897333).sum := by decide
  have hdescent : baseEnd_897333 < baseStart_897333 := by decide
  rcases family_descends (prefixWord ++ tailWord_897333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897352 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 1, 4, 4]
def baseStart_897352 : Nat := 118140960795 + 897352 * 2 ^ 59
def prefixEnd_897352 : Nat := 4983230072969 + 3 ^ 40 * 897352 * 2
def baseEnd_897352 : Nat := 460772892273478339873159

theorem tailTrace_897352 : CollatzResearch.WordTrace tailWord_897352 prefixEnd_897352 460772892273478339873159 := by
  unfold tailWord_897352
  simp only [CollatzResearch.WordTrace]
  refine ⟨16364558122527217182707155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21819410830036289576942873 16364558122527217182707155)
  ·
    refine ⟨24546837183790825774060733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16364558122527217182707155 24546837183790825774060733)
    ·
      refine ⟨9205063943921559665272775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24546837183790825774060733 9205063943921559665272775)
      ·
        refine ⟨13807595915882339497909163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9205063943921559665272775 13807595915882339497909163)
        ·
          refine ⟨20711393873823509246863745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13807595915882339497909163 20711393873823509246863745)
          ·
            refine ⟨15533545405367631935147809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20711393873823509246863745 15533545405367631935147809)
            ·
              refine ⟨11650159054025723951360857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15533545405367631935147809 11650159054025723951360857)
              ·
                refine ⟨8737619290519292963520643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11650159054025723951360857 8737619290519292963520643)
                ·
                  refine ⟨13106428935778939445280965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8737619290519292963520643 13106428935778939445280965)
                  ·
                    refine ⟨2457455425458551145990181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13106428935778939445280965 2457455425458551145990181)
                    ·
                      refine ⟨460772892273478339873159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2457455425458551145990181 460772892273478339873159)
                      ·
                        rfl

theorem cell23_897352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_897352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897352 prefixEnd_897352 := by exact prefixLift 897352
  have htrace : WordTrace (prefixWord ++ tailWord_897352) baseStart_897352 baseEnd_897352 := by
    simpa [prefixWord, tailWord_897352, baseEnd_897352] using wordTrace_append hprefix tailTrace_897352
  have hstable : (prefixWord ++ tailWord_897352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897352).length < 2 ^ (prefixWord ++ tailWord_897352).sum := by decide
  have hdescent : baseEnd_897352 < baseStart_897352 := by decide
  rcases family_descends (prefixWord ++ tailWord_897352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897356 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 6, 2, 2]
def baseStart_897356 : Nat := 118140960795 + 897356 * 2 ^ 59
def prefixEnd_897356 : Nat := 4983230072969 + 3 ^ 40 * 897356 * 2
def baseEnd_897356 : Nat := 460774946196096324223141

theorem tailTrace_897356 : CollatzResearch.WordTrace tailWord_897356 prefixEnd_897356 460774946196096324223141 := by
  unfold tailWord_897356
  simp only [CollatzResearch.WordTrace]
  refine ⟨16364631068519971524279961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21819508091359962032373281 16364631068519971524279961)
  ·
    refine ⟨12273473301389978643209971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16364631068519971524279961 12273473301389978643209971)
    ·
      refine ⟨18410209952084967964814957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12273473301389978643209971 18410209952084967964814957)
      ·
        refine ⟨6903828732031862986805609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18410209952084967964814957 6903828732031862986805609)
        ·
          refine ⟨5177871549023897240104207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6903828732031862986805609 5177871549023897240104207)
          ·
            refine ⟨7766807323535845860156311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5177871549023897240104207 7766807323535845860156311)
            ·
              refine ⟨11650210985303768790234467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7766807323535845860156311 11650210985303768790234467)
              ·
                refine ⟨17475316477955653185351701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11650210985303768790234467 17475316477955653185351701)
                ·
                  refine ⟨819155459904171243063361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17475316477955653185351701 819155459904171243063361)
                  ·
                    refine ⟨614366594928128432297521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 819155459904171243063361 614366594928128432297521)
                    ·
                      refine ⟨460774946196096324223141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 614366594928128432297521 460774946196096324223141)
                      ·
                        rfl

theorem cell23_897356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_897356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897356 prefixEnd_897356 := by exact prefixLift 897356
  have htrace : WordTrace (prefixWord ++ tailWord_897356) baseStart_897356 baseEnd_897356 := by
    simpa [prefixWord, tailWord_897356, baseEnd_897356] using wordTrace_append hprefix tailTrace_897356
  have hstable : (prefixWord ++ tailWord_897356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897356).length < 2 ^ (prefixWord ++ tailWord_897356).sum := by decide
  have hdescent : baseEnd_897356 < baseStart_897356 := by decide
  rcases family_descends (prefixWord ++ tailWord_897356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897362 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 9]
def baseStart_897362 : Nat := 118140960795 + 897362 * 2 ^ 59
def prefixEnd_897362 : Nat := 4983230072969 + 3 ^ 40 * 897362 * 2
def baseEnd_897362 : Nat := 51197558564447033416457

theorem tailTrace_897362 : CollatzResearch.WordTrace tailWord_897362 prefixEnd_897362 51197558564447033416457 := by
  unfold tailWord_897362
  simp only [CollatzResearch.WordTrace]
  refine ⟨8182370243754551518319585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21819653983345470715518893 8182370243754551518319585)
  ·
    refine ⟨6136777682815913638739689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8182370243754551518319585 6136777682815913638739689)
    ·
      refine ⟨4602583262111935229054767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6136777682815913638739689 4602583262111935229054767)
      ·
        refine ⟨6903874893167902843582151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4602583262111935229054767 6903874893167902843582151)
        ·
          refine ⟨10355812339751854265373227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6903874893167902843582151 10355812339751854265373227)
          ·
            refine ⟨15533718509627781398059841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10355812339751854265373227 15533718509627781398059841)
            ·
              refine ⟨11650288882220836048544881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15533718509627781398059841 11650288882220836048544881)
              ·
                refine ⟨8737716661665627036408661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11650288882220836048544881 8737716661665627036408661)
                ·
                  refine ⟨51197558564447033416457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8737716661665627036408661 51197558564447033416457)
                  ·
                    rfl

theorem cell23_897362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 9].length) (baseStart_897362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897362 prefixEnd_897362 := by exact prefixLift 897362
  have htrace : WordTrace (prefixWord ++ tailWord_897362) baseStart_897362 baseEnd_897362 := by
    simpa [prefixWord, tailWord_897362, baseEnd_897362] using wordTrace_append hprefix tailTrace_897362
  have hstable : (prefixWord ++ tailWord_897362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897362).length < 2 ^ (prefixWord ++ tailWord_897362).sum := by decide
  have hdescent : baseEnd_897362 < baseStart_897362 := by decide
  rcases family_descends (prefixWord ++ tailWord_897362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897389 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 1, 5, 3]
def baseStart_897389 : Nat := 118140960795 + 897389 * 2 ^ 59
def prefixEnd_897389 : Nat := 4983230072969 + 3 ^ 40 * 897389 * 2
def baseEnd_897389 : Nat := 460791891057694695110489

theorem tailTrace_897389 : CollatzResearch.WordTrace tailWord_897389 prefixEnd_897389 460791891057694695110489 := by
  unfold tailWord_897389
  simp only [CollatzResearch.WordTrace]
  refine ⟨32730465745920389684511221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21820310497280259789674147 32730465745920389684511221)
  ·
    refine ⟨3068481163680036532922927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32730465745920389684511221 3068481163680036532922927)
    ·
      refine ⟨4602721745520054799384391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3068481163680036532922927 4602721745520054799384391)
      ·
        refine ⟨6904082618280082199076587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4602721745520054799384391 6904082618280082199076587)
        ·
          refine ⟨10356123927420123298614881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6904082618280082199076587 10356123927420123298614881)
          ·
            refine ⟨7767092945565092473961161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10356123927420123298614881 7767092945565092473961161)
            ·
              refine ⟨5825319709173819355470871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7767092945565092473961161 5825319709173819355470871)
              ·
                refine ⟨8737979563760729033206307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5825319709173819355470871 8737979563760729033206307)
                ·
                  refine ⟨13106969345641093549809461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8737979563760729033206307 13106969345641093549809461)
                  ·
                    refine ⟨1228778376153852520294637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13106969345641093549809461 1228778376153852520294637)
                    ·
                      refine ⟨460791891057694695110489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1228778376153852520294637 460791891057694695110489)
                      ·
                        rfl

theorem cell23_897389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_897389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897389 prefixEnd_897389 := by exact prefixLift 897389
  have htrace : WordTrace (prefixWord ++ tailWord_897389) baseStart_897389 baseEnd_897389 := by
    simpa [prefixWord, tailWord_897389, baseEnd_897389] using wordTrace_append hprefix tailTrace_897389
  have hstable : (prefixWord ++ tailWord_897389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897389).length < 2 ^ (prefixWord ++ tailWord_897389).sum := by decide
  have hdescent : baseEnd_897389 < baseStart_897389 := by decide
  rcases family_descends (prefixWord ++ tailWord_897389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897399 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 4, 5, 2]
def baseStart_897399 : Nat := 118140960795 + 897399 * 2 ^ 59
def prefixEnd_897399 : Nat := 4983230072969 + 3 ^ 40 * 897399 * 2
def baseEnd_897399 : Nat := 460797025864239655985443

theorem tailTrace_897399 : CollatzResearch.WordTrace tailWord_897399 prefixEnd_897399 460797025864239655985443 := by
  unfold tailWord_897399
  simp only [CollatzResearch.WordTrace]
  refine ⟨32730830475884161392375251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21820553650589440928250167 32730830475884161392375251)
  ·
    refine ⟨49096245713826242088562877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32730830475884161392375251 49096245713826242088562877)
    ·
      refine ⟨18411092142684840783211079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49096245713826242088562877 18411092142684840783211079)
      ·
        refine ⟨27616638214027261174816619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18411092142684840783211079 27616638214027261174816619)
        ·
          refine ⟨41424957321040891762224929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27616638214027261174816619 41424957321040891762224929)
          ·
            refine ⟨31068717990780668821668697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41424957321040891762224929 31068717990780668821668697)
            ·
              refine ⟨23301538493085501616251523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31068717990780668821668697 23301538493085501616251523)
              ·
                refine ⟨34952307739628252424377285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23301538493085501616251523 34952307739628252424377285)
                ·
                  refine ⟨6553557701180297329570741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34952307739628252424377285 6553557701180297329570741)
                  ·
                    refine ⟨614396034485652874647257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6553557701180297329570741 614396034485652874647257)
                    ·
                      refine ⟨460797025864239655985443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 614396034485652874647257 460797025864239655985443)
                      ·
                        rfl

theorem cell23_897399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 5, 2].length) (baseStart_897399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897399 prefixEnd_897399 := by exact prefixLift 897399
  have htrace : WordTrace (prefixWord ++ tailWord_897399) baseStart_897399 baseEnd_897399 := by
    simpa [prefixWord, tailWord_897399, baseEnd_897399] using wordTrace_append hprefix tailTrace_897399
  have hstable : (prefixWord ++ tailWord_897399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897399).length < 2 ^ (prefixWord ++ tailWord_897399).sum := by decide
  have hdescent : baseEnd_897399 < baseStart_897399 := by decide
  rcases family_descends (prefixWord ++ tailWord_897399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897402 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 5, 2, 5]
def baseStart_897402 : Nat := 118140960795 + 897402 * 2 ^ 59
def prefixEnd_897402 : Nat := 4983230072969 + 3 ^ 40 * 897402 * 2
def baseEnd_897402 : Nat := 460798566306203144247929

theorem tailTrace_897402 : CollatzResearch.WordTrace tailWord_897402 prefixEnd_897402 460798566306203144247929 := by
  unfold tailWord_897402
  simp only [CollatzResearch.WordTrace]
  refine ⟨8182734973718323226183615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21820626596582195269822973 8182734973718323226183615)
  ·
    refine ⟨12274102460577484839275423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8182734973718323226183615 12274102460577484839275423)
    ·
      refine ⟨18411153690866227258913135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12274102460577484839275423 18411153690866227258913135)
      ·
        refine ⟨27616730536299340888369703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18411153690866227258913135 27616730536299340888369703)
        ·
          refine ⟨41425095804449011332554555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27616730536299340888369703 41425095804449011332554555)
          ·
            refine ⟨62137643706673516998831833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41425095804449011332554555 62137643706673516998831833)
            ·
              refine ⟨46603232780005137749123875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62137643706673516998831833 46603232780005137749123875)
              ·
                refine ⟨69904849170007706623685813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46603232780005137749123875 69904849170007706623685813)
                ·
                  refine ⟨6553579609688222495970545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69904849170007706623685813 6553579609688222495970545)
                  ·
                    refine ⟨4915184707266166871977909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6553579609688222495970545 4915184707266166871977909)
                    ·
                      refine ⟨460798566306203144247929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4915184707266166871977909 460798566306203144247929)
                      ·
                        rfl

theorem cell23_897402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_897402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897402 prefixEnd_897402 := by exact prefixLift 897402
  have htrace : WordTrace (prefixWord ++ tailWord_897402) baseStart_897402 baseEnd_897402 := by
    simpa [prefixWord, tailWord_897402, baseEnd_897402] using wordTrace_append hprefix tailTrace_897402
  have hstable : (prefixWord ++ tailWord_897402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897402).length < 2 ^ (prefixWord ++ tailWord_897402).sum := by decide
  have hdescent : baseEnd_897402 < baseStart_897402 := by decide
  rcases family_descends (prefixWord ++ tailWord_897402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897449 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 4, 2, 3]
def baseStart_897449 : Nat := 118140960795 + 897449 * 2 ^ 59
def prefixEnd_897449 : Nat := 4983230072969 + 3 ^ 40 * 897449 * 2
def baseEnd_897449 : Nat := 460822699896964460360213

theorem tailTrace_897449 : CollatzResearch.WordTrace tailWord_897449 prefixEnd_897449 460822699896964460360213 := by
  unfold tailWord_897449
  simp only [CollatzResearch.WordTrace]
  refine ⟨32732654125703019931695401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21821769417135346621130267 32732654125703019931695401)
  ·
    refine ⟨24549490594277264948771551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32732654125703019931695401 24549490594277264948771551)
    ·
      refine ⟨36824235891415897423157327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24549490594277264948771551 36824235891415897423157327)
      ·
        refine ⟨55236353837123846134735991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36824235891415897423157327 55236353837123846134735991)
        ·
          refine ⟨82854530755685769202103987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55236353837123846134735991 82854530755685769202103987)
          ·
            refine ⟨124281796133528653803155981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82854530755685769202103987 124281796133528653803155981)
            ·
              refine ⟨46605673550073245176183493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124281796133528653803155981 46605673550073245176183493)
              ·
                refine ⟨8738563790638733470534405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46605673550073245176183493 8738563790638733470534405)
                ·
                  refine ⟨1638480710744762525725201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8738563790638733470534405 1638480710744762525725201)
                  ·
                    refine ⟨1228860533058571894293901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1638480710744762525725201 1228860533058571894293901)
                    ·
                      refine ⟨460822699896964460360213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1228860533058571894293901 460822699896964460360213)
                      ·
                        rfl

theorem cell23_897449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 2, 3].length) (baseStart_897449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897449 prefixEnd_897449 := by exact prefixLift 897449
  have htrace : WordTrace (prefixWord ++ tailWord_897449) baseStart_897449 baseEnd_897449 := by
    simpa [prefixWord, tailWord_897449, baseEnd_897449] using wordTrace_append hprefix tailTrace_897449
  have hstable : (prefixWord ++ tailWord_897449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897449).length < 2 ^ (prefixWord ++ tailWord_897449).sum := by decide
  have hdescent : baseEnd_897449 < baseStart_897449 := by decide
  rcases family_descends (prefixWord ++ tailWord_897449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897452 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 10]
def baseStart_897452 : Nat := 118140960795 + 897452 * 2 ^ 59
def prefixEnd_897452 : Nat := 4983230072969 + 3 ^ 40 * 897452 * 2
def baseEnd_897452 : Nat := 51202693370991994291411

theorem tailTrace_897452 : CollatzResearch.WordTrace tailWord_897452 prefixEnd_897452 51202693370991994291411 := by
  unfold tailWord_897452
  simp only [CollatzResearch.WordTrace]
  refine ⟨16366381772346075722027305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21821842363128100962703073 16366381772346075722027305)
  ·
    refine ⟨12274786329259556791520479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16366381772346075722027305 12274786329259556791520479)
    ·
      refine ⟨18412179493889335187280719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12274786329259556791520479 18412179493889335187280719)
      ·
        refine ⟨27618269240834002780921079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18412179493889335187280719 27618269240834002780921079)
        ·
          refine ⟨41427403861251004171381619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27618269240834002780921079 41427403861251004171381619)
          ·
            refine ⟨62141105791876506257072429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41427403861251004171381619 62141105791876506257072429)
            ·
              refine ⟨23302914671953689846402161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62141105791876506257072429 23302914671953689846402161)
              ·
                refine ⟨17477186003965267384801621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23302914671953689846402161 17477186003965267384801621)
                ·
                  refine ⟨51202693370991994291411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 17477186003965267384801621 51202693370991994291411)
                  ·
                    rfl

theorem cell23_897452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 10].length) (baseStart_897452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897452 prefixEnd_897452 := by exact prefixLift 897452
  have htrace : WordTrace (prefixWord ++ tailWord_897452) baseStart_897452 baseEnd_897452 := by
    simpa [prefixWord, tailWord_897452, baseEnd_897452] using wordTrace_append hprefix tailTrace_897452
  have hstable : (prefixWord ++ tailWord_897452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897452).length < 2 ^ (prefixWord ++ tailWord_897452).sum := by decide
  have hdescent : baseEnd_897452 < baseStart_897452 := by decide
  rcases family_descends (prefixWord ++ tailWord_897452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897490 : List Nat := [3, 2, 2, 4, 1, 1, 2, 1, 3, 4]
def baseStart_897490 : Nat := 118140960795 + 897490 * 2 ^ 59
def prefixEnd_897490 : Nat := 4983230072969 + 3 ^ 40 * 897490 * 2
def baseEnd_897490 : Nat := 153614584201266266649175

theorem tailTrace_897490 : CollatzResearch.WordTrace tailWord_897490 prefixEnd_897490 153614584201266266649175 := by
  unfold tailWord_897490
  simp only [CollatzResearch.WordTrace]
  refine ⟨8183537379638620983484481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21822766345702989289291949 8183537379638620983484481)
  ·
    refine ⟨6137653034728965737613361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8183537379638620983484481 6137653034728965737613361)
    ·
      refine ⟨4603239776046724303210021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6137653034728965737613361 4603239776046724303210021)
      ·
        refine ⟨863107458008760806851879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4603239776046724303210021 863107458008760806851879)
        ·
          refine ⟨1294661187013141210277819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 863107458008760806851879 1294661187013141210277819)
          ·
            refine ⟨1941991780519711815416729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1294661187013141210277819 1941991780519711815416729)
            ·
              refine ⟨1456493835389783861562547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1941991780519711815416729 1456493835389783861562547)
              ·
                refine ⟨2184740753084675792343821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1456493835389783861562547 2184740753084675792343821)
                ·
                  refine ⟨819277782406753422128933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2184740753084675792343821 819277782406753422128933)
                  ·
                    refine ⟨153614584201266266649175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 819277782406753422128933 153614584201266266649175)
                    ·
                      rfl

theorem cell23_897490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_897490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897490 prefixEnd_897490 := by exact prefixLift 897490
  have htrace : WordTrace (prefixWord ++ tailWord_897490) baseStart_897490 baseEnd_897490 := by
    simpa [prefixWord, tailWord_897490, baseEnd_897490] using wordTrace_append hprefix tailTrace_897490
  have hstable : (prefixWord ++ tailWord_897490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897490).length < 2 ^ (prefixWord ++ tailWord_897490).sum := by decide
  have hdescent : baseEnd_897490 < baseStart_897490 := by decide
  rcases family_descends (prefixWord ++ tailWord_897490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897516 : List Nat := [2, 2, 1, 1, 2, 1, 6, 2, 1, 5]
def baseStart_897516 : Nat := 118140960795 + 897516 * 2 ^ 59
def prefixEnd_897516 : Nat := 4983230072969 + 3 ^ 40 * 897516 * 2
def baseEnd_897516 : Nat := 153619034366938566074135

theorem tailTrace_897516 : CollatzResearch.WordTrace tailWord_897516 prefixEnd_897516 153619034366938566074135 := by
  unfold tailWord_897516
  simp only [CollatzResearch.WordTrace]
  refine ⟨16367548908230145187192201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21823398544306860249589601 16367548908230145187192201)
  ·
    refine ⟨12275661681172608890394151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16367548908230145187192201 12275661681172608890394151)
    ·
      refine ⟨18413492521758913335591227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12275661681172608890394151 18413492521758913335591227)
      ·
        refine ⟨27620238782638370003386841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18413492521758913335591227 27620238782638370003386841)
        ·
          refine ⟨20715179086978777502540131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27620238782638370003386841 20715179086978777502540131)
          ·
            refine ⟨31072768630468166253810197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20715179086978777502540131 31072768630468166253810197)
            ·
              refine ⟨1456536029553195293147353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31072768630468166253810197 1456536029553195293147353)
              ·
                refine ⟨1092402022164896469860515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1456536029553195293147353 1092402022164896469860515)
                ·
                  refine ⟨1638603033247344704790773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1092402022164896469860515 1638603033247344704790773)
                  ·
                    refine ⟨153619034366938566074135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1638603033247344704790773 153619034366938566074135)
                    ·
                      rfl

theorem cell23_897516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 5].length) (baseStart_897516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897516 prefixEnd_897516 := by exact prefixLift 897516
  have htrace : WordTrace (prefixWord ++ tailWord_897516) baseStart_897516 baseEnd_897516 := by
    simpa [prefixWord, tailWord_897516, baseEnd_897516] using wordTrace_append hprefix tailTrace_897516
  have hstable : (prefixWord ++ tailWord_897516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897516).length < 2 ^ (prefixWord ++ tailWord_897516).sum := by decide
  have hdescent : baseEnd_897516 < baseStart_897516 := by decide
  rcases family_descends (prefixWord ++ tailWord_897516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897529 : List Nat := [1, 2, 1, 3, 1, 2, 2, 4, 1, 6]
def baseStart_897529 : Nat := 118140960795 + 897529 * 2 ^ 59
def prefixEnd_897529 : Nat := 4983230072969 + 3 ^ 40 * 897529 * 2
def baseEnd_897529 : Nat := 153621259449774715786615

theorem tailTrace_897529 : CollatzResearch.WordTrace tailWord_897529 prefixEnd_897529 153621259449774715786615 := by
  unfold tailWord_897529
  simp only [CollatzResearch.WordTrace]
  refine ⟨32735571965413193594607641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21823714643608795729738427 32735571965413193594607641)
  ·
    refine ⟨24551678974059895195955731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32735571965413193594607641 24551678974059895195955731)
    ·
      refine ⟨36827518461089842793933597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24551678974059895195955731 36827518461089842793933597)
      ·
        refine ⟨13810319422908691047725099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36827518461089842793933597 13810319422908691047725099)
        ·
          refine ⟨20715479134363036571587649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13810319422908691047725099 20715479134363036571587649)
          ·
            refine ⟨15536609350772277428690737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20715479134363036571587649 15536609350772277428690737)
            ·
              refine ⟨11652457013079208071518053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15536609350772277428690737 11652457013079208071518053)
              ·
                refine ⟨2184835689952351513409635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11652457013079208071518053 2184835689952351513409635)
                ·
                  refine ⟨3277253534928527270114453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2184835689952351513409635 3277253534928527270114453)
                  ·
                    refine ⟨153621259449774715786615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3277253534928527270114453 153621259449774715786615)
                    ·
                      rfl

theorem cell23_897529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 6].length) (baseStart_897529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897529 prefixEnd_897529 := by exact prefixLift 897529
  have htrace : WordTrace (prefixWord ++ tailWord_897529) baseStart_897529 baseEnd_897529 := by
    simpa [prefixWord, tailWord_897529, baseEnd_897529] using wordTrace_append hprefix tailTrace_897529
  have hstable : (prefixWord ++ tailWord_897529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897529).length < 2 ^ (prefixWord ++ tailWord_897529).sum := by decide
  have hdescent : baseEnd_897529 < baseStart_897529 := by decide
  rcases family_descends (prefixWord ++ tailWord_897529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897540 : List Nat := [2, 3, 2, 3, 1, 2, 1, 2, 2, 3, 2]
def baseStart_897540 : Nat := 118140960795 + 897540 * 2 ^ 59
def prefixEnd_897540 : Nat := 4983230072969 + 3 ^ 40 * 897540 * 2
def baseEnd_897540 : Nat := 460869426636523604322295

theorem tailTrace_897540 : CollatzResearch.WordTrace tailWord_897540 prefixEnd_897540 460869426636523604322295 := by
  unfold tailWord_897540
  simp only [CollatzResearch.WordTrace]
  refine ⟨16367986584186671236629037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21823982112248894982172049 16367986584186671236629037)
  ·
    refine ⟨6137994969070001713735889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16367986584186671236629037 6137994969070001713735889)
    ·
      refine ⟨4603496226802501285301917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6137994969070001713735889 4603496226802501285301917)
      ·
        refine ⟨1726311085050937981988219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4603496226802501285301917 1726311085050937981988219)
        ·
          refine ⟨2589466627576406972982329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1726311085050937981988219 2589466627576406972982329)
          ·
            refine ⟨1942099970682305229736747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2589466627576406972982329 1942099970682305229736747)
            ·
              refine ⟨2913149956023457844605121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1942099970682305229736747 2913149956023457844605121)
              ·
                refine ⟨2184862467017593383453841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2913149956023457844605121 2184862467017593383453841)
                ·
                  refine ⟨1638646850263195037590381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2184862467017593383453841 1638646850263195037590381)
                  ·
                    refine ⟨614492568848698139096393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1638646850263195037590381 614492568848698139096393)
                    ·
                      refine ⟨460869426636523604322295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 614492568848698139096393 460869426636523604322295)
                      ·
                        rfl

theorem cell23_897540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_897540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897540 prefixEnd_897540 := by exact prefixLift 897540
  have htrace : WordTrace (prefixWord ++ tailWord_897540) baseStart_897540 baseEnd_897540 := by
    simpa [prefixWord, tailWord_897540, baseEnd_897540] using wordTrace_append hprefix tailTrace_897540
  have hstable : (prefixWord ++ tailWord_897540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897540).length < 2 ^ (prefixWord ++ tailWord_897540).sum := by decide
  have hdescent : baseEnd_897540 < baseStart_897540 := by decide
  rcases family_descends (prefixWord ++ tailWord_897540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897546 : List Nat := [3, 1, 2, 2, 2, 1, 1, 3, 4, 4]
def baseStart_897546 : Nat := 118140960795 + 897546 * 2 ^ 59
def prefixEnd_897546 : Nat := 4983230072969 + 3 ^ 40 * 897546 * 2
def baseEnd_897546 : Nat := 153624169173483526949089

theorem tailTrace_897546 : CollatzResearch.WordTrace tailWord_897546 prefixEnd_897546 153624169173483526949089 := by
  unfold tailWord_897546
  simp only [CollatzResearch.WordTrace]
  refine ⟨8184048001587901374494123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21824128004234403665317661 8184048001587901374494123)
  ·
    refine ⟨12276072002381852061741185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8184048001587901374494123 12276072002381852061741185)
    ·
      refine ⟨9207054001786389046305889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12276072002381852061741185 9207054001786389046305889)
      ·
        refine ⟨6905290501339791784729417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9207054001786389046305889 6905290501339791784729417)
        ·
          refine ⟨5178967876004843838547063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6905290501339791784729417 5178967876004843838547063)
          ·
            refine ⟨7768451814007265757820595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5178967876004843838547063 7768451814007265757820595)
            ·
              refine ⟨11652677721010898636730893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7768451814007265757820595 11652677721010898636730893)
              ·
                refine ⟨4369754145379086988774085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11652677721010898636730893 4369754145379086988774085)
                ·
                  refine ⟨819328902258578810395141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4369754145379086988774085 819328902258578810395141)
                  ·
                    refine ⟨153624169173483526949089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 819328902258578810395141 153624169173483526949089)
                    ·
                      rfl

theorem cell23_897546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_897546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897546 prefixEnd_897546 := by exact prefixLift 897546
  have htrace : WordTrace (prefixWord ++ tailWord_897546) baseStart_897546 baseEnd_897546 := by
    simpa [prefixWord, tailWord_897546, baseEnd_897546] using wordTrace_append hprefix tailTrace_897546
  have hstable : (prefixWord ++ tailWord_897546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897546).length < 2 ^ (prefixWord ++ tailWord_897546).sum := by decide
  have hdescent : baseEnd_897546 < baseStart_897546 := by decide
  rcases family_descends (prefixWord ++ tailWord_897546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897547 : List Nat := [1, 1, 1, 1, 7, 2, 3, 2, 1, 1, 3]
def baseStart_897547 : Nat := 118140960795 + 897547 * 2 ^ 59
def prefixEnd_897547 : Nat := 4983230072969 + 3 ^ 40 * 897547 * 2
def baseEnd_897547 : Nat := 460873021001105076934763

theorem tailTrace_897547 : CollatzResearch.WordTrace tailWord_897547 prefixEnd_897547 460873021001105076934763 := by
  unfold tailWord_897547
  simp only [CollatzResearch.WordTrace]
  refine ⟨32736228479347982668762895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21824152319565321779175263 32736228479347982668762895)
  ·
    refine ⟨49104342719021974003144343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32736228479347982668762895 49104342719021974003144343)
    ·
      refine ⟨73656514078532961004716515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49104342719021974003144343 73656514078532961004716515)
      ·
        refine ⟨110484771117799441507074773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73656514078532961004716515 110484771117799441507074773)
        ·
          refine ⟨2589486823073424410322065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 110484771117799441507074773 2589486823073424410322065)
          ·
            refine ⟨1942115117305068307741549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2589486823073424410322065 1942115117305068307741549)
            ·
              refine ⟨728293168989400615403081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1942115117305068307741549 728293168989400615403081)
              ·
                refine ⟨546219876742050461552311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 728293168989400615403081 546219876742050461552311)
                ·
                  refine ⟨819329815113075692328467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 546219876742050461552311 819329815113075692328467)
                  ·
                    refine ⟨1228994722669613538492701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 819329815113075692328467 1228994722669613538492701)
                    ·
                      refine ⟨460873021001105076934763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1228994722669613538492701 460873021001105076934763)
                      ·
                        rfl

theorem cell23_897547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 2, 1, 1, 3].length) (baseStart_897547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897547 prefixEnd_897547 := by exact prefixLift 897547
  have htrace : WordTrace (prefixWord ++ tailWord_897547) baseStart_897547 baseEnd_897547 := by
    simpa [prefixWord, tailWord_897547, baseEnd_897547] using wordTrace_append hprefix tailTrace_897547
  have hstable : (prefixWord ++ tailWord_897547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897547).length < 2 ^ (prefixWord ++ tailWord_897547).sum := by decide
  have hdescent : baseEnd_897547 < baseStart_897547 := by decide
  rcases family_descends (prefixWord ++ tailWord_897547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897553 : List Nat := [1, 2, 2, 1, 1, 2, 2, 5, 3, 2, 2]
def baseStart_897553 : Nat := 118140960795 + 897553 * 2 ^ 59
def prefixEnd_897553 : Nat := 4983230072969 + 3 ^ 40 * 897553 * 2
def baseEnd_897553 : Nat := 460876101885032053459735

theorem tailTrace_897553 : CollatzResearch.WordTrace tailWord_897553 prefixEnd_897553 460876101885032053459735 := by
  unfold tailWord_897553
  simp only [CollatzResearch.WordTrace]
  refine ⟨32736447317326245693481313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21824298211550830462320875 32736447317326245693481313)
  ·
    refine ⟨24552335487994684270110985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32736447317326245693481313 24552335487994684270110985)
    ·
      refine ⟨18414251615996013202583239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24552335487994684270110985 18414251615996013202583239)
      ·
        refine ⟨27621377423994019803874859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18414251615996013202583239 27621377423994019803874859)
        ·
          refine ⟨41432066135991029705812289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27621377423994019803874859 41432066135991029705812289)
          ·
            refine ⟨31074049601993272279359217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41432066135991029705812289 31074049601993272279359217)
            ·
              refine ⟨23305537201494954209519413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31074049601993272279359217 23305537201494954209519413)
              ·
                refine ⟨2184894112640151957142445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23305537201494954209519413 2184894112640151957142445)
                ·
                  refine ⟨819335292240056983928417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2184894112640151957142445 819335292240056983928417)
                  ·
                    refine ⟨614501469180042737946313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 819335292240056983928417 614501469180042737946313)
                    ·
                      refine ⟨460876101885032053459735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 614501469180042737946313 460876101885032053459735)
                      ·
                        rfl

theorem cell23_897553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3, 2, 2].length) (baseStart_897553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897553 prefixEnd_897553 := by exact prefixLift 897553
  have htrace : WordTrace (prefixWord ++ tailWord_897553) baseStart_897553 baseEnd_897553 := by
    simpa [prefixWord, tailWord_897553, baseEnd_897553] using wordTrace_append hprefix tailTrace_897553
  have hstable : (prefixWord ++ tailWord_897553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897553).length < 2 ^ (prefixWord ++ tailWord_897553).sum := by decide
  have hdescent : baseEnd_897553 < baseStart_897553 := by decide
  rcases family_descends (prefixWord ++ tailWord_897553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897573 : List Nat := [1, 3, 1, 2, 2, 1, 5, 2, 1, 2, 3]
def baseStart_897573 : Nat := 118140960795 + 897573 * 2 ^ 59
def prefixEnd_897573 : Nat := 4983230072969 + 3 ^ 40 * 897573 * 2
def baseEnd_897573 : Nat := 460886371498121975209643

theorem tailTrace_897573 : CollatzResearch.WordTrace tailWord_897573 prefixEnd_897573 460886371498121975209643 := by
  unfold tailWord_897573
  simp only [CollatzResearch.WordTrace]
  refine ⟨32737176777253789109209373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21824784518169192739472915 32737176777253789109209373)
  ·
    refine ⟨12276441291470170915953515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32737176777253789109209373 12276441291470170915953515)
    ·
      refine ⟨18414661937205256373930273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12276441291470170915953515 18414661937205256373930273)
      ·
        refine ⟨13810996452903942280447705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18414661937205256373930273 13810996452903942280447705)
        ·
          refine ⟨10358247339677956710335779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13810996452903942280447705 10358247339677956710335779)
          ·
            refine ⟨15537371009516935065503669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10358247339677956710335779 15537371009516935065503669)
            ·
              refine ⟨1456628532142212662390969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15537371009516935065503669 1456628532142212662390969)
              ·
                refine ⟨1092471399106659496793227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1456628532142212662390969 1092471399106659496793227)
                ·
                  refine ⟨1638707098659989245189841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1092471399106659496793227 1638707098659989245189841)
                  ·
                    refine ⟨1229030323994991933892381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1638707098659989245189841 1229030323994991933892381)
                    ·
                      refine ⟨460886371498121975209643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1229030323994991933892381 460886371498121975209643)
                      ·
                        rfl

theorem cell23_897573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_897573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897573 prefixEnd_897573 := by exact prefixLift 897573
  have htrace : WordTrace (prefixWord ++ tailWord_897573) baseStart_897573 baseEnd_897573 := by
    simpa [prefixWord, tailWord_897573, baseEnd_897573] using wordTrace_append hprefix tailTrace_897573
  have hstable : (prefixWord ++ tailWord_897573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897573).length < 2 ^ (prefixWord ++ tailWord_897573).sum := by decide
  have hdescent : baseEnd_897573 < baseStart_897573 := by decide
  rcases family_descends (prefixWord ++ tailWord_897573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897576 : List Nat := [2, 1, 5, 2, 1, 1, 2, 9]
def baseStart_897576 : Nat := 118140960795 + 897576 * 2 ^ 59
def prefixEnd_897576 : Nat := 4983230072969 + 3 ^ 40 * 897576 * 2
def baseEnd_897576 : Nat := 17069922664447609758227

theorem tailTrace_897576 : CollatzResearch.WordTrace tailWord_897576 prefixEnd_897576 17069922664447609758227 := by
  unfold tailWord_897576
  simp only [CollatzResearch.WordTrace]
  refine ⟨16368643098121460310784291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21824857464161947081045721 16368643098121460310784291)
  ·
    refine ⟨24552964647182190466176437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16368643098121460310784291 24552964647182190466176437)
    ·
      refine ⟨2301840435673330356204041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24552964647182190466176437 2301840435673330356204041)
      ·
        refine ⟨1726380326754997767153031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2301840435673330356204041 1726380326754997767153031)
        ·
          refine ⟨2589570490132496650729547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1726380326754997767153031 2589570490132496650729547)
          ·
            refine ⟨3884355735198744976094321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2589570490132496650729547 3884355735198744976094321)
            ·
              refine ⟨2913266801399058732070741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3884355735198744976094321 2913266801399058732070741)
              ·
                refine ⟨17069922664447609758227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2913266801399058732070741 17069922664447609758227)
                ·
                  rfl

theorem cell23_897576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 9].length) (baseStart_897576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897576 prefixEnd_897576 := by exact prefixLift 897576
  have htrace : WordTrace (prefixWord ++ tailWord_897576) baseStart_897576 baseEnd_897576 := by
    simpa [prefixWord, tailWord_897576, baseEnd_897576] using wordTrace_append hprefix tailTrace_897576
  have hstable : (prefixWord ++ tailWord_897576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897576).length < 2 ^ (prefixWord ++ tailWord_897576).sum := by decide
  have hdescent : baseEnd_897576 < baseStart_897576 := by decide
  rcases family_descends (prefixWord ++ tailWord_897576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897586 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3]
def baseStart_897586 : Nat := 118140960795 + 897586 * 2 ^ 59
def prefixEnd_897586 : Nat := 4983230072969 + 3 ^ 40 * 897586 * 2
def baseEnd_897586 : Nat := 460893046746630424347083

theorem tailTrace_897586 : CollatzResearch.WordTrace tailWord_897586 prefixEnd_897586 460893046746630424347083 := by
  unfold tailWord_897586
  simp only [CollatzResearch.WordTrace]
  refine ⟨8184412731551673082358153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21825100617471128219621741 8184412731551673082358153)
  ·
    refine ⟨6138309548663754811768615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8184412731551673082358153 6138309548663754811768615)
    ·
      refine ⟨9207464322995632217652923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6138309548663754811768615 9207464322995632217652923)
      ·
        refine ⟨13811196484493448326479385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9207464322995632217652923 13811196484493448326479385)
        ·
          refine ⟨10358397363370086244859539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13811196484493448326479385 10358397363370086244859539)
          ·
            refine ⟨15537596045055129367289309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10358397363370086244859539 15537596045055129367289309)
            ·
              refine ⟨5826598516895673512733491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15537596045055129367289309 5826598516895673512733491)
              ·
                refine ⟨8739897775343510269100237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5826598516895673512733491 8739897775343510269100237)
                ·
                  refine ⟨3277461665753816350912589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8739897775343510269100237 3277461665753816350912589)
                  ·
                    refine ⟨1229048124657681131592221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3277461665753816350912589 1229048124657681131592221)
                    ·
                      refine ⟨460893046746630424347083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1229048124657681131592221 460893046746630424347083)
                      ·
                        rfl

theorem cell23_897586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_897586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897586 prefixEnd_897586 := by exact prefixLift 897586
  have htrace : WordTrace (prefixWord ++ tailWord_897586) baseStart_897586 baseEnd_897586 := by
    simpa [prefixWord, tailWord_897586, baseEnd_897586] using wordTrace_append hprefix tailTrace_897586
  have hstable : (prefixWord ++ tailWord_897586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897586).length < 2 ^ (prefixWord ++ tailWord_897586).sum := by decide
  have hdescent : baseEnd_897586 < baseStart_897586 := by decide
  rcases family_descends (prefixWord ++ tailWord_897586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897590 : List Nat := [5, 1, 2, 1, 2, 3, 1, 1, 1, 1, 5]
def baseStart_897590 : Nat := 118140960795 + 897590 * 2 ^ 59
def prefixEnd_897590 : Nat := 4983230072969 + 3 ^ 40 * 897590 * 2
def baseEnd_897590 : Nat := 460895100669248408697065

theorem tailTrace_897590 : CollatzResearch.WordTrace tailWord_897590 prefixEnd_897590 460895100669248408697065 := by
  unfold tailWord_897590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2046112301137012563286139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21825197878794800675052149 2046112301137012563286139)
  ·
    refine ⟨3069168451705518844929209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2046112301137012563286139 3069168451705518844929209)
    ·
      refine ⟨2301876338779139133696907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3069168451705518844929209 2301876338779139133696907)
      ·
        refine ⟨3452814508168708700545361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2301876338779139133696907 3452814508168708700545361)
        ·
          refine ⟨2589610881126531525409021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3452814508168708700545361 2589610881126531525409021)
          ·
            refine ⟨971104080422449322028383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2589610881126531525409021 971104080422449322028383)
            ·
              refine ⟨1456656120633673983042575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 971104080422449322028383 1456656120633673983042575)
              ·
                refine ⟨2184984180950510974563863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1456656120633673983042575 2184984180950510974563863)
                ·
                  refine ⟨3277476271425766461845795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2184984180950510974563863 3277476271425766461845795)
                  ·
                    refine ⟨4916214407138649692768693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3277476271425766461845795 4916214407138649692768693)
                    ·
                      refine ⟨460895100669248408697065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4916214407138649692768693 460895100669248408697065)
                      ·
                        rfl

theorem cell23_897590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_897590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897590 prefixEnd_897590 := by exact prefixLift 897590
  have htrace : WordTrace (prefixWord ++ tailWord_897590) baseStart_897590 baseEnd_897590 := by
    simpa [prefixWord, tailWord_897590, baseEnd_897590] using wordTrace_append hprefix tailTrace_897590
  have hstable : (prefixWord ++ tailWord_897590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897590).length < 2 ^ (prefixWord ++ tailWord_897590).sum := by decide
  have hdescent : baseEnd_897590 < baseStart_897590 := by decide
  rcases family_descends (prefixWord ++ tailWord_897590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
