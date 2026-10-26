import V185TrunkScan23Chunk0853

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5053796 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 1, 1, 7]
def baseStart_5053796 : Nat := 118140960795 + 5053796 * 2 ^ 59
def prefixEnd_5053796 : Nat := 4983230072969 + 3 ^ 40 * 5053796 * 2
def baseEnd_5053796 : Nat := 2595026477769814233608021

theorem tailTrace_5053796 : CollatzResearch.WordTrace tailWord_5053796 prefixEnd_5053796 2595026477769814233608021 := by
  unfold tailWord_5053796
  simp only [CollatzResearch.WordTrace]
  refine ⟨92163541599483843242722621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122884722132645124323630161 92163541599483843242722621)
  ·
    refine ⟨34561328099806441216020983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92163541599483843242722621 34561328099806441216020983)
    ·
      refine ⟨51841992149709661824031475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34561328099806441216020983 51841992149709661824031475)
      ·
        refine ⟨77762988224564492736047213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51841992149709661824031475 77762988224564492736047213)
        ·
          refine ⟨29161120584211684776017705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77762988224564492736047213 29161120584211684776017705)
          ·
            refine ⟨21870840438158763582013279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29161120584211684776017705 21870840438158763582013279)
            ·
              refine ⟨32806260657238145373019919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21870840438158763582013279 32806260657238145373019919)
              ·
                refine ⟨49209390985857218059529879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32806260657238145373019919 49209390985857218059529879)
                ·
                  refine ⟨73814086478785827089294819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49209390985857218059529879 73814086478785827089294819)
                  ·
                    refine ⟨110721129718178740633942229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73814086478785827089294819 110721129718178740633942229)
                    ·
                      refine ⟨2595026477769814233608021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 110721129718178740633942229 2595026477769814233608021)
                      ·
                        rfl

theorem cell23_5053796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_5053796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053796 prefixEnd_5053796 := by exact prefixLift 5053796
  have htrace : WordTrace (prefixWord ++ tailWord_5053796) baseStart_5053796 baseEnd_5053796 := by
    simpa [prefixWord, tailWord_5053796, baseEnd_5053796] using wordTrace_append hprefix tailTrace_5053796
  have hstable : (prefixWord ++ tailWord_5053796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053796).length < 2 ^ (prefixWord ++ tailWord_5053796).sum := by decide
  have hdescent : baseEnd_5053796 < baseStart_5053796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053836 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 2, 1, 6]
def baseStart_5053836 : Nat := 118140960795 + 5053836 * 2 ^ 59
def prefixEnd_5053836 : Nat := 4983230072969 + 3 ^ 40 * 5053836 * 2
def baseEnd_5053836 : Nat := 2595047016995994077107837

theorem tailTrace_5053836 : CollatzResearch.WordTrace tailWord_5053836 prefixEnd_5053836 2595047016995994077107837 := by
  unfold tailWord_5053836
  simp only [CollatzResearch.WordTrace]
  refine ⟨92164271059411386658450681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122885694745881848877934241 92164271059411386658450681)
  ·
    refine ⟨69123203294558539993838011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92164271059411386658450681 69123203294558539993838011)
    ·
      refine ⟨103684804941837809990757017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69123203294558539993838011 103684804941837809990757017)
      ·
        refine ⟨77763603706378357493067763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103684804941837809990757017 77763603706378357493067763)
        ·
          refine ⟨116645405559567536239601645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77763603706378357493067763 116645405559567536239601645)
          ·
            refine ⟨43742027084837826089850617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116645405559567536239601645 43742027084837826089850617)
            ·
              refine ⟨32806520313628369567387963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43742027084837826089850617 32806520313628369567387963)
              ·
                refine ⟨49209780470442554351081945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32806520313628369567387963 49209780470442554351081945)
                ·
                  refine ⟨36907335352831915763311459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49209780470442554351081945 36907335352831915763311459)
                  ·
                    refine ⟨55361003029247873644967189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36907335352831915763311459 55361003029247873644967189)
                    ·
                      refine ⟨2595047016995994077107837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55361003029247873644967189 2595047016995994077107837)
                      ·
                        rfl

theorem cell23_5053836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_5053836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053836 prefixEnd_5053836 := by exact prefixLift 5053836
  have htrace : WordTrace (prefixWord ++ tailWord_5053836) baseStart_5053836 baseEnd_5053836 := by
    simpa [prefixWord, tailWord_5053836, baseEnd_5053836] using wordTrace_append hprefix tailTrace_5053836
  have hstable : (prefixWord ++ tailWord_5053836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053836).length < 2 ^ (prefixWord ++ tailWord_5053836).sum := by decide
  have hdescent : baseEnd_5053836 < baseStart_5053836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053863 : List Nat := [1, 1, 6, 1, 1, 1, 1, 5, 6]
def baseStart_5053863 : Nat := 118140960795 + 5053863 * 2 ^ 59
def prefixEnd_5053863 : Nat := 4983230072969 + 3 ^ 40 * 5053863 * 2
def baseEnd_5053863 : Nat := 288340097885962830163357

theorem tailTrace_5053863 : CollatzResearch.WordTrace tailWord_5053863 prefixEnd_5053863 288340097885962830163357 := by
  unfold tailWord_5053863
  simp only [CollatzResearch.WordTrace]
  refine ⟨184329526889724956928134243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122886351259816637952089495 184329526889724956928134243)
  ·
    refine ⟨276494290334587435392201365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184329526889724956928134243 276494290334587435392201365)
    ·
      refine ⟨12960669859433786034009439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 276494290334587435392201365 12960669859433786034009439)
      ·
        refine ⟨19441004789150679051014159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12960669859433786034009439 19441004789150679051014159)
        ·
          refine ⟨29161507183726018576521239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19441004789150679051014159 29161507183726018576521239)
          ·
            refine ⟨43742260775589027864781859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29161507183726018576521239 43742260775589027864781859)
            ·
              refine ⟨65613391163383541797172789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43742260775589027864781859 65613391163383541797172789)
              ·
                refine ⟨6151255421567207043484949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65613391163383541797172789 6151255421567207043484949)
                ·
                  refine ⟨288340097885962830163357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6151255421567207043484949 288340097885962830163357)
                  ·
                    rfl

theorem cell23_5053863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 6].length) (baseStart_5053863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053863 prefixEnd_5053863 := by exact prefixLift 5053863
  have htrace : WordTrace (prefixWord ++ tailWord_5053863) baseStart_5053863 baseEnd_5053863 := by
    simpa [prefixWord, tailWord_5053863, baseEnd_5053863] using wordTrace_append hprefix tailTrace_5053863
  have hstable : (prefixWord ++ tailWord_5053863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053863).length < 2 ^ (prefixWord ++ tailWord_5053863).sum := by decide
  have hdescent : baseEnd_5053863 < baseStart_5053863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053877 : List Nat := [1, 3, 3, 2, 2, 3, 1, 1, 2, 2, 3]
def baseStart_5053877 : Nat := 118140960795 + 5053877 * 2 ^ 59
def prefixEnd_5053877 : Nat := 4983230072969 + 3 ^ 40 * 5053877 * 2
def baseEnd_5053877 : Nat := 2595068069702828416695149

theorem tailTrace_5053877 : CollatzResearch.WordTrace tailWord_5053877 prefixEnd_5053877 2595068069702828416695149 := by
  unfold tailWord_5053877
  simp only [CollatzResearch.WordTrace]
  refine ⟨184330037511674237319143885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122886691674449491546095923 184330037511674237319143885)
  ·
    refine ⟨69123764066877838994678957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184330037511674237319143885 69123764066877838994678957)
    ·
      refine ⟨25921411525079189623004609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69123764066877838994678957 25921411525079189623004609)
      ·
        refine ⟨19441058643809392217253457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25921411525079189623004609 19441058643809392217253457)
        ·
          refine ⟨14580793982857044162940093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19441058643809392217253457 14580793982857044162940093)
          ·
            refine ⟨5467797743571391561102535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14580793982857044162940093 5467797743571391561102535)
            ·
              refine ⟨8201696615357087341653803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5467797743571391561102535 8201696615357087341653803)
              ·
                refine ⟨12302544923035631012480705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8201696615357087341653803 12302544923035631012480705)
                ·
                  refine ⟨9226908692276723259360529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12302544923035631012480705 9226908692276723259360529)
                  ·
                    refine ⟨6920181519207542444520397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9226908692276723259360529 6920181519207542444520397)
                    ·
                      refine ⟨2595068069702828416695149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6920181519207542444520397 2595068069702828416695149)
                      ·
                        rfl

theorem cell23_5053877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_5053877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053877 prefixEnd_5053877 := by exact prefixLift 5053877
  have htrace : WordTrace (prefixWord ++ tailWord_5053877) baseStart_5053877 baseEnd_5053877 := by
    simpa [prefixWord, tailWord_5053877, baseEnd_5053877] using wordTrace_append hprefix tailTrace_5053877
  have hstable : (prefixWord ++ tailWord_5053877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053877).length < 2 ^ (prefixWord ++ tailWord_5053877).sum := by decide
  have hdescent : baseEnd_5053877 < baseStart_5053877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053884 : List Nat := [2, 2, 2, 4, 2, 1, 2, 3, 1, 4]
def baseStart_5053884 : Nat := 118140960795 + 5053884 * 2 ^ 59
def prefixEnd_5053884 : Nat := 4983230072969 + 3 ^ 40 * 5053884 * 2
def baseEnd_5053884 : Nat := 865023888022469963102539

theorem tailTrace_5053884 : CollatzResearch.WordTrace tailWord_5053884 prefixEnd_5053884 865023888022469963102539 := by
  unfold tailWord_5053884
  simp only [CollatzResearch.WordTrace]
  refine ⟨92165146411324438757324353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122886861881765918343099137 92165146411324438757324353)
  ·
    refine ⟨69123859808493329067993265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92165146411324438757324353 69123859808493329067993265)
    ·
      refine ⟨51842894856369996800994949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69123859808493329067993265 51842894856369996800994949)
      ·
        refine ⟨9720542785569374400186553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51842894856369996800994949 9720542785569374400186553)
        ·
          refine ⟨7290407089177030800139915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9720542785569374400186553 7290407089177030800139915)
          ·
            refine ⟨10935610633765546200209873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7290407089177030800139915 10935610633765546200209873)
            ·
              refine ⟨8201707975324159650157405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10935610633765546200209873 8201707975324159650157405)
              ·
                refine ⟨3075640490746559868809027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8201707975324159650157405 3075640490746559868809027)
                ·
                  refine ⟨4613460736119839803213541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3075640490746559868809027 4613460736119839803213541)
                  ·
                    refine ⟨865023888022469963102539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4613460736119839803213541 865023888022469963102539)
                    ·
                      rfl

theorem cell23_5053884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_5053884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053884 prefixEnd_5053884 := by exact prefixLift 5053884
  have htrace : WordTrace (prefixWord ++ tailWord_5053884) baseStart_5053884 baseEnd_5053884 := by
    simpa [prefixWord, tailWord_5053884, baseEnd_5053884] using wordTrace_append hprefix tailTrace_5053884
  have hstable : (prefixWord ++ tailWord_5053884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053884).length < 2 ^ (prefixWord ++ tailWord_5053884).sum := by decide
  have hdescent : baseEnd_5053884 < baseStart_5053884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053941 : List Nat := [1, 3, 5, 1, 1, 1, 3, 3, 1, 1, 3]
def baseStart_5053941 : Nat := 118140960795 + 5053941 * 2 ^ 59
def prefixEnd_5053941 : Nat := 4983230072969 + 3 ^ 40 * 5053941 * 2
def baseEnd_5053941 : Nat := 2595100932464716166294855

theorem tailTrace_5053941 : CollatzResearch.WordTrace tailWord_5053941 prefixEnd_5053941 2595100932464716166294855 := by
  unfold tailWord_5053941
  simp only [CollatzResearch.WordTrace]
  refine ⟨184332371783442376249473677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122888247855628250832982451 184332371783442376249473677)
  ·
    refine ⟨69124639418790891093552629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184332371783442376249473677 69124639418790891093552629)
    ·
      refine ⟨6480434945511646040020559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69124639418790891093552629 6480434945511646040020559)
      ·
        refine ⟨9720652418267469060030839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6480434945511646040020559 9720652418267469060030839)
        ·
          refine ⟨14580978627401203590046259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9720652418267469060030839 14580978627401203590046259)
          ·
            refine ⟨21871467941101805385069389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14580978627401203590046259 21871467941101805385069389)
            ·
              refine ⟨8201800477913177019401021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21871467941101805385069389 8201800477913177019401021)
              ·
                refine ⟨3075675179217441382275383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8201800477913177019401021 3075675179217441382275383)
                ·
                  refine ⟨4613512768826162073413075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3075675179217441382275383 4613512768826162073413075)
                  ·
                    refine ⟨6920269153239243110119613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4613512768826162073413075 6920269153239243110119613)
                    ·
                      refine ⟨2595100932464716166294855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6920269153239243110119613 2595100932464716166294855)
                      ·
                        rfl

theorem cell23_5053941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_5053941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053941 prefixEnd_5053941 := by exact prefixLift 5053941
  have htrace : WordTrace (prefixWord ++ tailWord_5053941) baseStart_5053941 baseEnd_5053941 := by
    simpa [prefixWord, tailWord_5053941, baseEnd_5053941] using wordTrace_append hprefix tailTrace_5053941
  have hstable : (prefixWord ++ tailWord_5053941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053941).length < 2 ^ (prefixWord ++ tailWord_5053941).sum := by decide
  have hdescent : baseEnd_5053941 < baseStart_5053941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053980 : List Nat := [2, 2, 3, 1, 2, 1, 2, 3, 1, 3, 3]
def baseStart_5053980 : Nat := 118140960795 + 5053980 * 2 ^ 59
def prefixEnd_5053980 : Nat := 4983230072969 + 3 ^ 40 * 5053980 * 2
def baseEnd_5053980 : Nat := 2595120958210241513707175

theorem tailTrace_5053980 : CollatzResearch.WordTrace tailWord_5053980 prefixEnd_5053980 2595120958210241513707175 := by
  unfold tailWord_5053980
  simp only [CollatzResearch.WordTrace]
  refine ⟨92166897115150542955071697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122889196153534057273428929 92166897115150542955071697)
  ·
    refine ⟨69125172836362907216303773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92166897115150542955071697 69125172836362907216303773)
    ·
      refine ⟨25921939813636090206113915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69125172836362907216303773 25921939813636090206113915)
      ·
        refine ⟨38882909720454135309170873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25921939813636090206113915 38882909720454135309170873)
        ·
          refine ⟨29162182290340601481878155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38882909720454135309170873 29162182290340601481878155)
          ·
            refine ⟨43743273435510902222817233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29162182290340601481878155 43743273435510902222817233)
            ·
              refine ⟨32807455076633176667112925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43743273435510902222817233 32807455076633176667112925)
              ·
                refine ⟨12302795653737441250167347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32807455076633176667112925 12302795653737441250167347)
                ·
                  refine ⟨18454193480606161875251021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12302795653737441250167347 18454193480606161875251021)
                  ·
                    refine ⟨6920322555227310703219133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18454193480606161875251021 6920322555227310703219133)
                    ·
                      refine ⟨2595120958210241513707175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6920322555227310703219133 2595120958210241513707175)
                      ·
                        rfl

theorem cell23_5053980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_5053980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053980 prefixEnd_5053980 := by exact prefixLift 5053980
  have htrace : WordTrace (prefixWord ++ tailWord_5053980) baseStart_5053980 baseEnd_5053980 := by
    simpa [prefixWord, tailWord_5053980, baseEnd_5053980] using wordTrace_append hprefix tailTrace_5053980
  have hstable : (prefixWord ++ tailWord_5053980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053980).length < 2 ^ (prefixWord ++ tailWord_5053980).sum := by decide
  have hdescent : baseEnd_5053980 < baseStart_5053980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5053984 : List Nat := [2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 3]
def baseStart_5053984 : Nat := 118140960795 + 5053984 * 2 ^ 59
def prefixEnd_5053984 : Nat := 4983230072969 + 3 ^ 40 * 5053984 * 2
def baseEnd_5053984 : Nat := 2595123012132859498057157

theorem tailTrace_5053984 : CollatzResearch.WordTrace tailWord_5053984 prefixEnd_5053984 2595123012132859498057157 := by
  unfold tailWord_5053984
  simp only [CollatzResearch.WordTrace]
  refine ⟨92166970061143297296644503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122889293414857729728859337 92166970061143297296644503)
  ·
    refine ⟨138250455091714945944966755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92166970061143297296644503 138250455091714945944966755)
    ·
      refine ⟨207375682637572418917450133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138250455091714945944966755 207375682637572418917450133)
      ·
        refine ⟨9720735123636207136755475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 207375682637572418917450133 9720735123636207136755475)
        ·
          refine ⟨14581102685454310705133213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9720735123636207136755475 14581102685454310705133213)
          ·
            refine ⟨5467913507045366514424955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14581102685454310705133213 5467913507045366514424955)
            ·
              refine ⟨8201870260568049771637433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5467913507045366514424955 8201870260568049771637433)
              ·
                refine ⟨6151402695426037328728075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8201870260568049771637433 6151402695426037328728075)
                ·
                  refine ⟨9227104043139055993092113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6151402695426037328728075 9227104043139055993092113)
                  ·
                    refine ⟨6920328032354291994819085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9227104043139055993092113 6920328032354291994819085)
                    ·
                      refine ⟨2595123012132859498057157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6920328032354291994819085 2595123012132859498057157)
                      ·
                        rfl

theorem cell23_5053984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_5053984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5053984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5053984 prefixEnd_5053984 := by exact prefixLift 5053984
  have htrace : WordTrace (prefixWord ++ tailWord_5053984) baseStart_5053984 baseEnd_5053984 := by
    simpa [prefixWord, tailWord_5053984, baseEnd_5053984] using wordTrace_append hprefix tailTrace_5053984
  have hstable : (prefixWord ++ tailWord_5053984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5053984).length < 2 ^ (prefixWord ++ tailWord_5053984).sum := by decide
  have hdescent : baseEnd_5053984 < baseStart_5053984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5053984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054037 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 6, 2, 2]
def baseStart_5054037 : Nat := 118140960795 + 5054037 * 2 ^ 59
def prefixEnd_5054037 : Nat := 4983230072969 + 3 ^ 40 * 5054037 * 2
def baseEnd_5054037 : Nat := 2595150226607547790694413

theorem tailTrace_5054037 : CollatzResearch.WordTrace tailWord_5054037 prefixEnd_5054037 2595150226607547790694413 := by
  unfold tailWord_5054037
  simp only [CollatzResearch.WordTrace]
  refine ⟨184335873191094584644968365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122890582127396389763312243 184335873191094584644968365)
  ·
    refine ⟨69125952446660469241863137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184335873191094584644968365 69125952446660469241863137)
    ·
      refine ⟨51844464334995351931397353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69125952446660469241863137 51844464334995351931397353)
      ·
        refine ⟨38883348251246513948548015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51844464334995351931397353 38883348251246513948548015)
        ·
          refine ⟨58325022376869770922822023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38883348251246513948548015 58325022376869770922822023)
          ·
            refine ⟨87487533565304656384233035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58325022376869770922822023 87487533565304656384233035)
            ·
              refine ⟨131231300347956984576349553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87487533565304656384233035 131231300347956984576349553)
              ·
                refine ⟨98423475260967738432262165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131231300347956984576349553 98423475260967738432262165)
                ·
                  refine ⟨4613600402857862739012289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98423475260967738432262165 4613600402857862739012289)
                  ·
                    refine ⟨3460200302143397054259217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4613600402857862739012289 3460200302143397054259217)
                    ·
                      refine ⟨2595150226607547790694413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3460200302143397054259217 2595150226607547790694413)
                      ·
                        rfl

theorem cell23_5054037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_5054037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054037 prefixEnd_5054037 := by exact prefixLift 5054037
  have htrace : WordTrace (prefixWord ++ tailWord_5054037) baseStart_5054037 baseEnd_5054037 := by
    simpa [prefixWord, tailWord_5054037, baseEnd_5054037] using wordTrace_append hprefix tailTrace_5054037
  have hstable : (prefixWord ++ tailWord_5054037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054037).length < 2 ^ (prefixWord ++ tailWord_5054037).sum := by decide
  have hdescent : baseEnd_5054037 < baseStart_5054037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054077 : List Nat := [1, 4, 1, 1, 4, 1, 2, 4, 5]
def baseStart_5054077 : Nat := 118140960795 + 5054077 * 2 ^ 59
def prefixEnd_5054077 : Nat := 4983230072969 + 3 ^ 40 * 5054077 * 2
def baseEnd_5054077 : Nat := 288352307314858626021581

theorem tailTrace_5054077 : CollatzResearch.WordTrace tailWord_5054077 prefixEnd_5054077 288352307314858626021581 := by
  unfold tailWord_5054077
  simp only [CollatzResearch.WordTrace]
  refine ⟨184337332110949671476424485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122891554740633114317616323 184337332110949671476424485)
  ·
    refine ⟨34563249770803063401829591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184337332110949671476424485 34563249770803063401829591)
    ·
      refine ⟨51844874656204595102744387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34563249770803063401829591 51844874656204595102744387)
      ·
        refine ⟨77767311984306892654116581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51844874656204595102744387 77767311984306892654116581)
        ·
          refine ⟨14581370997057542372646859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77767311984306892654116581 14581370997057542372646859)
          ·
            refine ⟨21872056495586313558970289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14581370997057542372646859 21872056495586313558970289)
            ·
              refine ⟨16404042371689735169227717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21872056495586313558970289 16404042371689735169227717)
              ·
                refine ⟨3075757944691825344230197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16404042371689735169227717 3075757944691825344230197)
                ·
                  refine ⟨288352307314858626021581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3075757944691825344230197 288352307314858626021581)
                  ·
                    rfl

theorem cell23_5054077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 4, 5].length) (baseStart_5054077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054077 prefixEnd_5054077 := by exact prefixLift 5054077
  have htrace : WordTrace (prefixWord ++ tailWord_5054077) baseStart_5054077 baseEnd_5054077 := by
    simpa [prefixWord, tailWord_5054077, baseEnd_5054077] using wordTrace_append hprefix tailTrace_5054077
  have hstable : (prefixWord ++ tailWord_5054077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054077).length < 2 ^ (prefixWord ++ tailWord_5054077).sum := by decide
  have hdescent : baseEnd_5054077 < baseStart_5054077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054083 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 7]
def baseStart_5054083 : Nat := 118140960795 + 5054083 * 2 ^ 59
def prefixEnd_5054083 : Nat := 4983230072969 + 3 ^ 40 * 5054083 * 2
def baseEnd_5054083 : Nat := 2595173846717654610719201

theorem tailTrace_5054083 : CollatzResearch.WordTrace tailWord_5054083 prefixEnd_5054083 2595173846717654610719201 := by
  unfold tailWord_5054083
  simp only [CollatzResearch.WordTrace]
  refine ⟨184337550948927934501142903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122891700632618623000761935 184337550948927934501142903)
  ·
    refine ⟨276506326423391901751714355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184337550948927934501142903 276506326423391901751714355)
    ·
      refine ⟨414759489635087852627571533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276506326423391901751714355 414759489635087852627571533)
      ·
        refine ⟨155534808613157944735339325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 414759489635087852627571533 155534808613157944735339325)
        ·
          refine ⟨58325553229934229275752247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155534808613157944735339325 58325553229934229275752247)
          ·
            refine ⟨87488329844901343913628371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58325553229934229275752247 87488329844901343913628371)
            ·
              refine ⟨131232494767352015870442557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87488329844901343913628371 131232494767352015870442557)
              ·
                refine ⟨49212185537757005951415959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131232494767352015870442557 49212185537757005951415959)
                ·
                  refine ⟨73818278306635508927123939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49212185537757005951415959 73818278306635508927123939)
                  ·
                    refine ⟨110727417459953263390685909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73818278306635508927123939 110727417459953263390685909)
                    ·
                      refine ⟨2595173846717654610719201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 110727417459953263390685909 2595173846717654610719201)
                      ·
                        rfl

theorem cell23_5054083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_5054083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054083 prefixEnd_5054083 := by exact prefixLift 5054083
  have htrace : WordTrace (prefixWord ++ tailWord_5054083) baseStart_5054083 baseEnd_5054083 := by
    simpa [prefixWord, tailWord_5054083, baseEnd_5054083] using wordTrace_append hprefix tailTrace_5054083
  have hstable : (prefixWord ++ tailWord_5054083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054083).length < 2 ^ (prefixWord ++ tailWord_5054083).sum := by decide
  have hdescent : baseEnd_5054083 < baseStart_5054083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054088 : List Nat := [2, 1, 3, 5, 2, 1, 1, 1, 1, 4, 2]
def baseStart_5054088 : Nat := 118140960795 + 5054088 * 2 ^ 59
def prefixEnd_5054088 : Nat := 4983230072969 + 3 ^ 40 * 5054088 * 2
def baseEnd_5054088 : Nat := 2595176414120927091156679

theorem tailTrace_5054088 : CollatzResearch.WordTrace tailWord_5054088 prefixEnd_5054088 2595176414120927091156679 := by
  unfold tailWord_5054088
  simp only [CollatzResearch.WordTrace]
  refine ⟨92168866656954910177537459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122891822209273213570049945 92168866656954910177537459)
  ·
    refine ⟨138253299985432365266306189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92168866656954910177537459 138253299985432365266306189)
    ·
      refine ⟨51844987494537136974864821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138253299985432365266306189 51844987494537136974864821)
      ·
        refine ⟨4860467577612856591393577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51844987494537136974864821 4860467577612856591393577)
        ·
          refine ⟨3645350683209642443545183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4860467577612856591393577 3645350683209642443545183)
          ·
            refine ⟨5468026024814463665317775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3645350683209642443545183 5468026024814463665317775)
            ·
              refine ⟨8202039037221695497976663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5468026024814463665317775 8202039037221695497976663)
              ·
                refine ⟨12303058555832543246964995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8202039037221695497976663 12303058555832543246964995)
                ·
                  refine ⟨18454587833748814870447493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12303058555832543246964995 18454587833748814870447493)
                  ·
                    refine ⟨3460235218827902788208905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18454587833748814870447493 3460235218827902788208905)
                    ·
                      refine ⟨2595176414120927091156679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3460235218827902788208905 2595176414120927091156679)
                      ·
                        rfl

theorem cell23_5054088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_5054088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054088 prefixEnd_5054088 := by exact prefixLift 5054088
  have htrace : WordTrace (prefixWord ++ tailWord_5054088) baseStart_5054088 baseEnd_5054088 := by
    simpa [prefixWord, tailWord_5054088, baseEnd_5054088] using wordTrace_append hprefix tailTrace_5054088
  have hstable : (prefixWord ++ tailWord_5054088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054088).length < 2 ^ (prefixWord ++ tailWord_5054088).sum := by decide
  have hdescent : baseEnd_5054088 < baseStart_5054088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054090 : List Nat := [3, 1, 2, 3, 2, 1, 1, 2, 1, 7]
def baseStart_5054090 : Nat := 118140960795 + 5054090 * 2 ^ 59
def prefixEnd_5054090 : Nat := 4983230072969 + 3 ^ 40 * 5054090 * 2
def baseEnd_5054090 : Nat := 865059147027412027777223

theorem tailTrace_5054090 : CollatzResearch.WordTrace tailWord_5054090 prefixEnd_5054090 865059147027412027777223 := by
  unfold tailWord_5054090
  simp only [CollatzResearch.WordTrace]
  refine ⟨46084451564975643674161931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122891870839935049797765149 46084451564975643674161931)
  ·
    refine ⟨69126677347463465511242897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46084451564975643674161931 69126677347463465511242897)
    ·
      refine ⟨51845008010597599133432173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69126677347463465511242897 51845008010597599133432173)
      ·
        refine ⟨19441878003974099675037065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51845008010597599133432173 19441878003974099675037065)
        ·
          refine ⟨14581408502980574756277799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19441878003974099675037065 14581408502980574756277799)
          ·
            refine ⟨21872112754470862134416699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14581408502980574756277799 21872112754470862134416699)
            ·
              refine ⟨32808169131706293201625049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21872112754470862134416699 32808169131706293201625049)
              ·
                refine ⟨24606126848779719901218787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32808169131706293201625049 24606126848779719901218787)
                ·
                  refine ⟨36909190273169579851828181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24606126848779719901218787 36909190273169579851828181)
                  ·
                    refine ⟨865059147027412027777223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36909190273169579851828181 865059147027412027777223)
                    ·
                      rfl

theorem cell23_5054090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_5054090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054090 prefixEnd_5054090 := by exact prefixLift 5054090
  have htrace : WordTrace (prefixWord ++ tailWord_5054090) baseStart_5054090 baseEnd_5054090 := by
    simpa [prefixWord, tailWord_5054090, baseEnd_5054090] using wordTrace_append hprefix tailTrace_5054090
  have hstable : (prefixWord ++ tailWord_5054090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054090).length < 2 ^ (prefixWord ++ tailWord_5054090).sum := by decide
  have hdescent : baseEnd_5054090 < baseStart_5054090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054111 : List Nat := [1, 1, 2, 7, 1, 2, 1, 3, 5]
def baseStart_5054111 : Nat := 118140960795 + 5054111 * 2 ^ 59
def prefixEnd_5054111 : Nat := 4983230072969 + 3 ^ 40 * 5054111 * 2
def baseEnd_5054111 : Nat := 288354247130664500129897

theorem tailTrace_5054111 : CollatzResearch.WordTrace tailWord_5054111 prefixEnd_5054111 288354247130664500129897 := by
  unfold tailWord_5054111
  simp only [CollatzResearch.WordTrace]
  refine ⟨184338572192826495283162187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122892381461884330188774791 184338572192826495283162187)
  ·
    refine ⟨276507858289239742924743281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184338572192826495283162187 276507858289239742924743281)
    ·
      refine ⟨207380893716929807193557461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276507858289239742924743281 207380893716929807193557461)
      ·
        refine ⟨4860489696490542356099003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 207380893716929807193557461 4860489696490542356099003)
        ·
          refine ⟨7290734544735813534148505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4860489696490542356099003 7290734544735813534148505)
          ·
            refine ⟨5468050908551860150611379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7290734544735813534148505 5468050908551860150611379)
            ·
              refine ⟨8202076362827790225917069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5468050908551860150611379 8202076362827790225917069)
              ·
                refine ⟨3075778636060421334718901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8202076362827790225917069 3075778636060421334718901)
                ·
                  refine ⟨288354247130664500129897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3075778636060421334718901 288354247130664500129897)
                  ·
                    rfl

theorem cell23_5054111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 3, 5].length) (baseStart_5054111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054111 prefixEnd_5054111 := by exact prefixLift 5054111
  have htrace : WordTrace (prefixWord ++ tailWord_5054111) baseStart_5054111 baseEnd_5054111 := by
    simpa [prefixWord, tailWord_5054111, baseEnd_5054111] using wordTrace_append hprefix tailTrace_5054111
  have hstable : (prefixWord ++ tailWord_5054111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054111).length < 2 ^ (prefixWord ++ tailWord_5054111).sum := by decide
  have hdescent : baseEnd_5054111 < baseStart_5054111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054134 : List Nat := [5, 1, 3, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_5054134 : Nat := 118140960795 + 5054134 * 2 ^ 59
def prefixEnd_5054134 : Nat := 4983230072969 + 3 ^ 40 * 5054134 * 2
def baseEnd_5054134 : Nat := 2595200034231033911181467

theorem tailTrace_5054134 : CollatzResearch.WordTrace tailWord_5054134 prefixEnd_5054134 2595200034231033911181467 := by
  unfold tailWord_5054134
  simp only [CollatzResearch.WordTrace]
  refine ⟨11521213191983948138203091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122892940714495446807499637 11521213191983948138203091)
  ·
    refine ⟨17281819787975922207304637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11521213191983948138203091 17281819787975922207304637)
    ·
      refine ⟨6480682420490970827739239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17281819787975922207304637 6480682420490970827739239)
      ·
        refine ⟨9721023630736456241608859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6480682420490970827739239 9721023630736456241608859)
        ·
          refine ⟨14581535446104684362413289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9721023630736456241608859 14581535446104684362413289)
          ·
            refine ⟨10936151584578513271809967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14581535446104684362413289 10936151584578513271809967)
            ·
              refine ⟨16404227376867769907714951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10936151584578513271809967 16404227376867769907714951)
              ·
                refine ⟨24606341065301654861572427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16404227376867769907714951 24606341065301654861572427)
                ·
                  refine ⟨36909511597952482292358641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24606341065301654861572427 36909511597952482292358641)
                  ·
                    refine ⟨27682133698464361719268981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36909511597952482292358641 27682133698464361719268981)
                    ·
                      refine ⟨2595200034231033911181467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27682133698464361719268981 2595200034231033911181467)
                      ·
                        rfl

theorem cell23_5054134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_5054134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054134 prefixEnd_5054134 := by exact prefixLift 5054134
  have htrace : WordTrace (prefixWord ++ tailWord_5054134) baseStart_5054134 baseEnd_5054134 := by
    simpa [prefixWord, tailWord_5054134, baseEnd_5054134] using wordTrace_append hprefix tailTrace_5054134
  have hstable : (prefixWord ++ tailWord_5054134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054134).length < 2 ^ (prefixWord ++ tailWord_5054134).sum := by decide
  have hdescent : baseEnd_5054134 < baseStart_5054134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054137 : List Nat := [1, 2, 1, 4, 1, 1, 5, 1, 3, 4]
def baseStart_5054137 : Nat := 118140960795 + 5054137 * 2 ^ 59
def prefixEnd_5054137 : Nat := 4983230072969 + 3 ^ 40 * 5054137 * 2
def baseEnd_5054137 : Nat := 865067191557665799814651

theorem tailTrace_5054137 : CollatzResearch.WordTrace tailWord_5054137 prefixEnd_5054137 865067191557665799814651 := by
  unfold tailWord_5054137
  simp only [CollatzResearch.WordTrace]
  refine ⟨184339520490732301723608665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122893013660488201149072443 184339520490732301723608665)
  ·
    refine ⟨138254640368049226292706499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184339520490732301723608665 138254640368049226292706499)
    ·
      refine ⟨207381960552073839439059749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138254640368049226292706499 207381960552073839439059749)
      ·
        refine ⟨38884117603513844894823703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207381960552073839439059749 38884117603513844894823703)
        ·
          refine ⟨58326176405270767342235555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38884117603513844894823703 58326176405270767342235555)
          ·
            refine ⟨87489264607906151013353333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58326176405270767342235555 87489264607906151013353333)
            ·
              refine ⟨8202118556991201657501875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87489264607906151013353333 8202118556991201657501875)
              ·
                refine ⟨12303177835486802486252813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8202118556991201657501875 12303177835486802486252813)
                ·
                  refine ⟨4613691688307550932344805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12303177835486802486252813 4613691688307550932344805)
                  ·
                    refine ⟨865067191557665799814651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4613691688307550932344805 865067191557665799814651)
                    ·
                      rfl

theorem cell23_5054137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 3, 4].length) (baseStart_5054137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054137 prefixEnd_5054137 := by exact prefixLift 5054137
  have htrace : WordTrace (prefixWord ++ tailWord_5054137) baseStart_5054137 baseEnd_5054137 := by
    simpa [prefixWord, tailWord_5054137, baseEnd_5054137] using wordTrace_append hprefix tailTrace_5054137
  have hstable : (prefixWord ++ tailWord_5054137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054137).length < 2 ^ (prefixWord ++ tailWord_5054137).sum := by decide
  have hdescent : baseEnd_5054137 < baseStart_5054137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054164 : List Nat := [2, 4, 1, 3, 1, 1, 1, 3, 2, 2, 3]
def baseStart_5054164 : Nat := 118140960795 + 5054164 * 2 ^ 59
def prefixEnd_5054164 : Nat := 4983230072969 + 3 ^ 40 * 5054164 * 2
def baseEnd_5054164 : Nat := 2595215438650668793806329

theorem tailTrace_5054164 : CollatzResearch.WordTrace tailWord_5054164 prefixEnd_5054164 2595215438650668793806329 := by
  unfold tailWord_5054164
  simp only [CollatzResearch.WordTrace]
  refine ⟨92170252630817242667420773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122893670174422990223227697 92170252630817242667420773)
  ·
    refine ⟨17281922368278233000141395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92170252630817242667420773 17281922368278233000141395)
    ·
      refine ⟨25922883552417349500212093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17281922368278233000141395 25922883552417349500212093)
      ·
        refine ⟨9721081332156506062579535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25922883552417349500212093 9721081332156506062579535)
        ·
          refine ⟨14581621998234759093869303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9721081332156506062579535 14581621998234759093869303)
          ·
            refine ⟨21872432997352138640803955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14581621998234759093869303 21872432997352138640803955)
            ·
              refine ⟨32808649496028207961205933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21872432997352138640803955 32808649496028207961205933)
              ·
                refine ⟨12303243561010577985452225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32808649496028207961205933 12303243561010577985452225)
                ·
                  refine ⟨9227432670757933489089169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12303243561010577985452225 9227432670757933489089169)
                  ·
                    refine ⟨6920574503068450116816877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9227432670757933489089169 6920574503068450116816877)
                    ·
                      refine ⟨2595215438650668793806329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6920574503068450116816877 2595215438650668793806329)
                      ·
                        rfl

theorem cell23_5054164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_5054164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054164 prefixEnd_5054164 := by exact prefixLift 5054164
  have htrace : WordTrace (prefixWord ++ tailWord_5054164) baseStart_5054164 baseEnd_5054164 := by
    simpa [prefixWord, tailWord_5054164, baseEnd_5054164] using wordTrace_append hprefix tailTrace_5054164
  have hstable : (prefixWord ++ tailWord_5054164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054164).length < 2 ^ (prefixWord ++ tailWord_5054164).sum := by decide
  have hdescent : baseEnd_5054164 < baseStart_5054164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054194 : List Nat := [3, 2, 1, 3, 1, 1, 2, 3, 3, 1, 3]
def baseStart_5054194 : Nat := 118140960795 + 5054194 * 2 ^ 59
def prefixEnd_5054194 : Nat := 4983230072969 + 3 ^ 40 * 5054194 * 2
def baseEnd_5054194 : Nat := 2595230843070303676431191

theorem tailTrace_5054194 : CollatzResearch.WordTrace tailWord_5054194 prefixEnd_5054194 2595230843070303676431191 := by
  unfold tailWord_5054194
  simp only [CollatzResearch.WordTrace]
  refine ⟨46085399862881450114608409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122894399634350533638955757 46085399862881450114608409)
  ·
    refine ⟨34564049897161087585956307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46085399862881450114608409 34564049897161087585956307)
    ·
      refine ⟨51846074845741631378934461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34564049897161087585956307 51846074845741631378934461)
      ·
        refine ⟨19442278067153111767100423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51846074845741631378934461 19442278067153111767100423)
        ·
          refine ⟨29163417100729667650650635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19442278067153111767100423 29163417100729667650650635)
          ·
            refine ⟨43745125651094501475975953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29163417100729667650650635 43745125651094501475975953)
            ·
              refine ⟨32808844238320876106981965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43745125651094501475975953 32808844238320876106981965)
              ·
                refine ⟨12303316589370328540118237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32808844238320876106981965 12303316589370328540118237)
                ·
                  refine ⟨4613743721013873202544339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12303316589370328540118237 4613743721013873202544339)
                  ·
                    refine ⟨6920615581520809803816509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4613743721013873202544339 6920615581520809803816509)
                    ·
                      refine ⟨2595230843070303676431191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6920615581520809803816509 2595230843070303676431191)
                      ·
                        rfl

theorem cell23_5054194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_5054194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054194 prefixEnd_5054194 := by exact prefixLift 5054194
  have htrace : WordTrace (prefixWord ++ tailWord_5054194) baseStart_5054194 baseEnd_5054194 := by
    simpa [prefixWord, tailWord_5054194, baseEnd_5054194] using wordTrace_append hprefix tailTrace_5054194
  have hstable : (prefixWord ++ tailWord_5054194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054194).length < 2 ^ (prefixWord ++ tailWord_5054194).sum := by decide
  have hdescent : baseEnd_5054194 < baseStart_5054194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054217 : List Nat := [1, 2, 1, 1, 3, 2, 1, 6, 1, 1, 4]
def baseStart_5054217 : Nat := 118140960795 + 5054217 * 2 ^ 59
def prefixEnd_5054217 : Nat := 4983230072969 + 3 ^ 40 * 5054217 * 2
def baseEnd_5054217 : Nat := 2595242653125357086443585

theorem tailTrace_5054217 : CollatzResearch.WordTrace tailWord_5054217 prefixEnd_5054217 2595242653125357086443585 := by
  unfold tailWord_5054217
  simp only [CollatzResearch.WordTrace]
  refine ⟨184342438330442475386520905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122894958886961650257680603 184342438330442475386520905)
  ·
    refine ⟨138256828747831856539890679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184342438330442475386520905 138256828747831856539890679)
    ·
      refine ⟨207385243121747784809836019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138256828747831856539890679 207385243121747784809836019)
      ·
        refine ⟨311077864682621677214754029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207385243121747784809836019 311077864682621677214754029)
        ·
          refine ⟨116654199255983128955532761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 311077864682621677214754029 116654199255983128955532761)
          ·
            refine ⟨87490649441987346716649571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116654199255983128955532761 87490649441987346716649571)
            ·
              refine ⟨131235974162981020074974357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87490649441987346716649571 131235974162981020074974357)
              ·
                refine ⟨6151686288889735316014423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 131235974162981020074974357 6151686288889735316014423)
                ·
                  refine ⟨9227529433334602974021635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6151686288889735316014423 9227529433334602974021635)
                  ·
                    refine ⟨13841294150001904461032453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9227529433334602974021635 13841294150001904461032453)
                    ·
                      refine ⟨2595242653125357086443585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13841294150001904461032453 2595242653125357086443585)
                      ·
                        rfl

theorem cell23_5054217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 1, 4].length) (baseStart_5054217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054217 prefixEnd_5054217 := by exact prefixLift 5054217
  have htrace : WordTrace (prefixWord ++ tailWord_5054217) baseStart_5054217 baseEnd_5054217 := by
    simpa [prefixWord, tailWord_5054217, baseEnd_5054217] using wordTrace_append hprefix tailTrace_5054217
  have hstable : (prefixWord ++ tailWord_5054217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054217).length < 2 ^ (prefixWord ++ tailWord_5054217).sum := by decide
  have hdescent : baseEnd_5054217 < baseStart_5054217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054231 : List Nat := [1, 1, 3, 4, 2, 3, 2, 1, 1, 5]
def baseStart_5054231 : Nat := 118140960795 + 5054231 * 2 ^ 59
def prefixEnd_5054231 : Nat := 4983230072969 + 3 ^ 40 * 5054231 * 2
def baseEnd_5054231 : Nat := 865083280618173343889507

theorem tailTrace_5054231 : CollatzResearch.WordTrace tailWord_5054231 prefixEnd_5054231 865083280618173343889507 := by
  unfold tailWord_5054231
  simp only [CollatzResearch.WordTrace]
  refine ⟨184342948952391755777530547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122895299301594503851687031 184342948952391755777530547)
  ·
    refine ⟨276514423428587633666295821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184342948952391755777530547 276514423428587633666295821)
    ·
      refine ⟨103692908785720362624860933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 276514423428587633666295821 103692908785720362624860933)
      ·
        refine ⟨19442420397322567992161425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103692908785720362624860933 19442420397322567992161425)
        ·
          refine ⟨14581815297991925994121069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19442420397322567992161425 14581815297991925994121069)
          ·
            refine ⟨5468180736746972247795401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14581815297991925994121069 5468180736746972247795401)
            ·
              refine ⟨4101135552560229185846551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5468180736746972247795401 4101135552560229185846551)
              ·
                refine ⟨6151703328840343778769827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4101135552560229185846551 6151703328840343778769827)
                ·
                  refine ⟨9227554993260515668154741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6151703328840343778769827 9227554993260515668154741)
                  ·
                    refine ⟨865083280618173343889507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9227554993260515668154741 865083280618173343889507)
                    ·
                      rfl

theorem cell23_5054231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 1, 5].length) (baseStart_5054231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054231 prefixEnd_5054231 := by exact prefixLift 5054231
  have htrace : WordTrace (prefixWord ++ tailWord_5054231) baseStart_5054231 baseEnd_5054231 := by
    simpa [prefixWord, tailWord_5054231, baseEnd_5054231] using wordTrace_append hprefix tailTrace_5054231
  have hstable : (prefixWord ++ tailWord_5054231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054231).length < 2 ^ (prefixWord ++ tailWord_5054231).sum := by decide
  have hdescent : baseEnd_5054231 < baseStart_5054231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054234 : List Nat := [3, 1, 1, 3, 2, 3, 1, 3, 1, 1, 4]
def baseStart_5054234 : Nat := 118140960795 + 5054234 * 2 ^ 59
def prefixEnd_5054234 : Nat := 4983230072969 + 3 ^ 40 * 5054234 * 2
def baseEnd_5054234 : Nat := 2595251382296483519931007

theorem tailTrace_5054234 : CollatzResearch.WordTrace tailWord_5054234 prefixEnd_5054234 2595251382296483519931007 := by
  unfold tailWord_5054234
  simp only [CollatzResearch.WordTrace]
  refine ⟨46085764592845221822472439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122895372247587258193259837 46085764592845221822472439)
  ·
    refine ⟨69128646889267832733708659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46085764592845221822472439 69128646889267832733708659)
    ·
      refine ⟨103692970333901749100562989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69128646889267832733708659 103692970333901749100562989)
      ·
        refine ⟨38884863875213155912711121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103692970333901749100562989 38884863875213155912711121)
        ·
          refine ⟨29163647906409866934533341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38884863875213155912711121 29163647906409866934533341)
          ·
            refine ⟨10936367964903700100450003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29163647906409866934533341 10936367964903700100450003)
            ·
              refine ⟨16404551947355550150675005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10936367964903700100450003 16404551947355550150675005)
              ·
                refine ⟨6151706980258331306503127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16404551947355550150675005 6151706980258331306503127)
                ·
                  refine ⟨9227560470387496959754691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6151706980258331306503127 9227560470387496959754691)
                  ·
                    refine ⟨13841340705581245439632037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9227560470387496959754691 13841340705581245439632037)
                    ·
                      refine ⟨2595251382296483519931007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13841340705581245439632037 2595251382296483519931007)
                      ·
                        rfl

theorem cell23_5054234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_5054234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054234 prefixEnd_5054234 := by exact prefixLift 5054234
  have htrace : WordTrace (prefixWord ++ tailWord_5054234) baseStart_5054234 baseEnd_5054234 := by
    simpa [prefixWord, tailWord_5054234, baseEnd_5054234] using wordTrace_append hprefix tailTrace_5054234
  have hstable : (prefixWord ++ tailWord_5054234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054234).length < 2 ^ (prefixWord ++ tailWord_5054234).sum := by decide
  have hdescent : baseEnd_5054234 < baseStart_5054234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054240 : List Nat := [2, 1, 1, 5, 1, 1, 12]
def baseStart_5054240 : Nat := 118140960795 + 5054240 * 2 ^ 59
def prefixEnd_5054240 : Nat := 4983230072969 + 3 ^ 40 * 5054240 * 2
def baseEnd_5054240 : Nat := 32040178557782845635259

theorem tailTrace_5054240 : CollatzResearch.WordTrace tailWord_5054240 prefixEnd_5054240 32040178557782845635259 := by
  unfold tailWord_5054240
  simp only [CollatzResearch.WordTrace]
  refine ⟨92171638604679575157304087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122895518139572766876405449 92171638604679575157304087)
  ·
    refine ⟨138257457907019362735956131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92171638604679575157304087 138257457907019362735956131)
    ·
      refine ⟨207386186860529044103934197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138257457907019362735956131 207386186860529044103934197)
      ·
        refine ⟨19442455018174597884743831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 207386186860529044103934197 19442455018174597884743831)
        ·
          refine ⟨29163682527261896827115747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19442455018174597884743831 29163682527261896827115747)
          ·
            refine ⟨43745523790892845240673621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29163682527261896827115747 43745523790892845240673621)
            ·
              refine ⟨32040178557782845635259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 43745523790892845240673621 32040178557782845635259)
              ·
                rfl

theorem cell23_5054240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 12].length) (baseStart_5054240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054240 prefixEnd_5054240 := by exact prefixLift 5054240
  have htrace : WordTrace (prefixWord ++ tailWord_5054240) baseStart_5054240 baseEnd_5054240 := by
    simpa [prefixWord, tailWord_5054240, baseEnd_5054240] using wordTrace_append hprefix tailTrace_5054240
  have hstable : (prefixWord ++ tailWord_5054240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054240).length < 2 ^ (prefixWord ++ tailWord_5054240).sum := by decide
  have hdescent : baseEnd_5054240 < baseStart_5054240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054244 : List Nat := [2, 3, 1, 3, 2, 2, 1, 1, 4, 4]
def baseStart_5054244 : Nat := 118140960795 + 5054244 * 2 ^ 59
def prefixEnd_5054244 : Nat := 4983230072969 + 3 ^ 40 * 5054244 * 2
def baseEnd_5054244 : Nat := 865085505701009493601987

theorem tailTrace_5054244 : CollatzResearch.WordTrace tailWord_5054244 prefixEnd_5054244 865085505701009493601987 := by
  unfold tailWord_5054244
  simp only [CollatzResearch.WordTrace]
  refine ⟨92171711550672329498876893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122895615400896439331835857 92171711550672329498876893)
  ·
    refine ⟨34564391831502123562078835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92171711550672329498876893 34564391831502123562078835)
    ·
      refine ⟨51846587747253185343118253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34564391831502123562078835 51846587747253185343118253)
      ·
        refine ⟨19442470405219944503669345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51846587747253185343118253 19442470405219944503669345)
        ·
          refine ⟨14581852803914958377752009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19442470405219944503669345 14581852803914958377752009)
          ·
            refine ⟨10936389602936218783314007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14581852803914958377752009 10936389602936218783314007)
            ·
              refine ⟨16404584404404328174971011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10936389602936218783314007 16404584404404328174971011)
              ·
                refine ⟨24606876606606492262456517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16404584404404328174971011 24606876606606492262456517)
                ·
                  refine ⟨4613789363738717299210597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24606876606606492262456517 4613789363738717299210597)
                  ·
                    refine ⟨865085505701009493601987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4613789363738717299210597 865085505701009493601987)
                    ·
                      rfl

theorem cell23_5054244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_5054244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054244 prefixEnd_5054244 := by exact prefixLift 5054244
  have htrace : WordTrace (prefixWord ++ tailWord_5054244) baseStart_5054244 baseEnd_5054244 := by
    simpa [prefixWord, tailWord_5054244, baseEnd_5054244] using wordTrace_append hprefix tailTrace_5054244
  have hstable : (prefixWord ++ tailWord_5054244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054244).length < 2 ^ (prefixWord ++ tailWord_5054244).sum := by decide
  have hdescent : baseEnd_5054244 < baseStart_5054244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054261 : List Nat := [1, 3, 3, 1, 5, 1, 1, 1, 1, 6]
def baseStart_5054261 : Nat := 118140960795 + 5054261 * 2 ^ 59
def prefixEnd_5054261 : Nat := 4983230072969 + 3 ^ 40 * 5054261 * 2
def baseEnd_5054261 : Nat := 865088415424718304764461

theorem tailTrace_5054261 : CollatzResearch.WordTrace tailWord_5054261 prefixEnd_5054261 865088415424718304764461 := by
  unfold tailWord_5054261
  simp only [CollatzResearch.WordTrace]
  refine ⟨184344043142283070901122637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122896028761522047267415091 184344043142283070901122637)
  ·
    refine ⟨69129016178356151587920989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184344043142283070901122637 69129016178356151587920989)
    ·
      refine ⟨25923381066883556845470371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69129016178356151587920989 25923381066883556845470371)
      ·
        refine ⟨38885071600325335268205557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25923381066883556845470371 38885071600325335268205557)
        ·
          refine ⟨3645475462530500181394271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38885071600325335268205557 3645475462530500181394271)
          ·
            refine ⟨5468213193795750272091407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3645475462530500181394271 5468213193795750272091407)
            ·
              refine ⟨8202319790693625408137111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5468213193795750272091407 8202319790693625408137111)
              ·
                refine ⟨12303479686040438112205667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8202319790693625408137111 12303479686040438112205667)
                ·
                  refine ⟨18455219529060657168308501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12303479686040438112205667 18455219529060657168308501)
                  ·
                    refine ⟨865088415424718304764461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18455219529060657168308501 865088415424718304764461)
                    ·
                      rfl

theorem cell23_5054261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_5054261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054261 prefixEnd_5054261 := by exact prefixLift 5054261
  have htrace : WordTrace (prefixWord ++ tailWord_5054261) baseStart_5054261 baseEnd_5054261 := by
    simpa [prefixWord, tailWord_5054261, baseEnd_5054261] using wordTrace_append hprefix tailTrace_5054261
  have hstable : (prefixWord ++ tailWord_5054261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054261).length < 2 ^ (prefixWord ++ tailWord_5054261).sum := by decide
  have hdescent : baseEnd_5054261 < baseStart_5054261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054264 : List Nat := [2, 1, 2, 1, 3, 5, 1, 1, 1, 2, 4]
def baseStart_5054264 : Nat := 118140960795 + 5054264 * 2 ^ 59
def prefixEnd_5054264 : Nat := 4983230072969 + 3 ^ 40 * 5054264 * 2
def baseEnd_5054264 : Nat := 2595266786716118402555869

theorem tailTrace_5054264 : CollatzResearch.WordTrace tailWord_5054264 prefixEnd_5054264 2595266786716118402555869 := by
  unfold tailWord_5054264
  simp only [CollatzResearch.WordTrace]
  refine ⟨92172076280636101206740923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122896101707514801608987897 92172076280636101206740923)
  ·
    refine ⟨138258114420954151810111385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92172076280636101206740923 138258114420954151810111385)
    ·
      refine ⟨103693585815715613857583539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138258114420954151810111385 103693585815715613857583539)
      ·
        refine ⟨155540378723573420786375309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103693585815715613857583539 155540378723573420786375309)
        ·
          refine ⟨58327642021340032794890741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155540378723573420786375309 58327642021340032794890741)
          ·
            refine ⟨5468216439500628074521007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58327642021340032794890741 5468216439500628074521007)
            ·
              refine ⟨8202324659250942111781511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5468216439500628074521007 8202324659250942111781511)
              ·
                refine ⟨12303486988876413167672267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8202324659250942111781511 12303486988876413167672267)
                ·
                  refine ⟨18455230483314619751508401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12303486988876413167672267 18455230483314619751508401)
                  ·
                    refine ⟨13841422862485964813631301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18455230483314619751508401 13841422862485964813631301)
                    ·
                      refine ⟨2595266786716118402555869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13841422862485964813631301 2595266786716118402555869)
                      ·
                        rfl

theorem cell23_5054264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 1, 2, 4].length) (baseStart_5054264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054264 prefixEnd_5054264 := by exact prefixLift 5054264
  have htrace : WordTrace (prefixWord ++ tailWord_5054264) baseStart_5054264 baseEnd_5054264 := by
    simpa [prefixWord, tailWord_5054264, baseEnd_5054264] using wordTrace_append hprefix tailTrace_5054264
  have hstable : (prefixWord ++ tailWord_5054264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054264).length < 2 ^ (prefixWord ++ tailWord_5054264).sum := by decide
  have hdescent : baseEnd_5054264 < baseStart_5054264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054271 : List Nat := [1, 1, 2, 2, 6, 1, 2, 2, 1, 2, 3]
def baseStart_5054271 : Nat := 118140960795 + 5054271 * 2 ^ 59
def prefixEnd_5054271 : Nat := 4983230072969 + 3 ^ 40 * 5054271 * 2
def baseEnd_5054271 : Nat := 2595270381080699875168337

theorem tailTrace_5054271 : CollatzResearch.WordTrace tailWord_5054271 prefixEnd_5054271 2595270381080699875168337 := by
  unfold tailWord_5054271
  simp only [CollatzResearch.WordTrace]
  refine ⟨184344407872246842608986667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122896271914831228405991111 184344407872246842608986667)
  ·
    refine ⟨276516611808370263913480001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184344407872246842608986667 276516611808370263913480001)
    ·
      refine ⟨207387458856277697935110001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276516611808370263913480001 207387458856277697935110001)
      ·
        refine ⟨155540594142208273451332501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207387458856277697935110001 155540594142208273451332501)
        ·
          refine ⟨7290965350416012818031211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 155540594142208273451332501 7290965350416012818031211)
          ·
            refine ⟨10936448025624019227046817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7290965350416012818031211 10936448025624019227046817)
            ·
              refine ⟨8202336019218014420285113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10936448025624019227046817 8202336019218014420285113)
              ·
                refine ⟨6151752014413510815213835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8202336019218014420285113 6151752014413510815213835)
                ·
                  refine ⟨9227628021620266222820753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6151752014413510815213835 9227628021620266222820753)
                  ·
                    refine ⟨6920721016215199667115565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9227628021620266222820753 6920721016215199667115565)
                    ·
                      refine ⟨2595270381080699875168337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6920721016215199667115565 2595270381080699875168337)
                      ·
                        rfl

theorem cell23_5054271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 2, 3].length) (baseStart_5054271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054271 prefixEnd_5054271 := by exact prefixLift 5054271
  have htrace : WordTrace (prefixWord ++ tailWord_5054271) baseStart_5054271 baseEnd_5054271 := by
    simpa [prefixWord, tailWord_5054271, baseEnd_5054271] using wordTrace_append hprefix tailTrace_5054271
  have hstable : (prefixWord ++ tailWord_5054271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054271).length < 2 ^ (prefixWord ++ tailWord_5054271).sum := by decide
  have hdescent : baseEnd_5054271 < baseStart_5054271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054317 : List Nat := [1, 5, 1, 1, 1, 1, 2, 3, 2, 6]
def baseStart_5054317 : Nat := 118140960795 + 5054317 * 2 ^ 59
def prefixEnd_5054317 : Nat := 4983230072969 + 3 ^ 40 * 5054317 * 2
def baseEnd_5054317 : Nat := 865098000396935565064375

theorem tailTrace_5054317 : CollatzResearch.WordTrace tailWord_5054317 prefixEnd_5054317 865098000396935565064375 := by
  unfold tailWord_5054317
  simp only [CollatzResearch.WordTrace]
  refine ⟨184346085630080192465161205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122897390420053461643440803 184346085630080192465161205)
  ·
    refine ⟨17282445527820018043608863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 184346085630080192465161205 17282445527820018043608863)
    ·
      refine ⟨25923668291730027065413295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17282445527820018043608863 25923668291730027065413295)
      ·
        refine ⟨38885502437595040598119943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25923668291730027065413295 38885502437595040598119943)
        ·
          refine ⟨58328253656392560897179915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38885502437595040598119943 58328253656392560897179915)
          ·
            refine ⟨87492380484588841345769873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58328253656392560897179915 87492380484588841345769873)
            ·
              refine ⟨65619285363441631009327405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87492380484588841345769873 65619285363441631009327405)
              ·
                refine ⟨24607232011290611628497777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65619285363441631009327405 24607232011290611628497777)
                ·
                  refine ⟨18455424008467958721373333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24607232011290611628497777 18455424008467958721373333)
                  ·
                    refine ⟨865098000396935565064375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18455424008467958721373333 865098000396935565064375)
                    ·
                      rfl

theorem cell23_5054317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_5054317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054317 prefixEnd_5054317 := by exact prefixLift 5054317
  have htrace : WordTrace (prefixWord ++ tailWord_5054317) baseStart_5054317 baseEnd_5054317 := by
    simpa [prefixWord, tailWord_5054317, baseEnd_5054317] using wordTrace_append hprefix tailTrace_5054317
  have hstable : (prefixWord ++ tailWord_5054317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054317).length < 2 ^ (prefixWord ++ tailWord_5054317).sum := by decide
  have hdescent : baseEnd_5054317 < baseStart_5054317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054318 : List Nat := [4, 1, 2, 3, 1, 2, 1, 3, 2, 1, 3]
def baseStart_5054318 : Nat := 118140960795 + 5054318 * 2 ^ 59
def prefixEnd_5054318 : Nat := 4983230072969 + 3 ^ 40 * 5054318 * 2
def baseEnd_5054318 : Nat := 2595294514671461191280621

theorem tailTrace_5054318 : CollatzResearch.WordTrace tailWord_5054318 prefixEnd_5054318 2595294514671461191280621 := by
  unfold tailWord_5054318
  simp only [CollatzResearch.WordTrace]
  refine ⟨23043265262884571204493451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122897414735384379757298405 23043265262884571204493451)
  ·
    refine ⟨34564897894326856806740177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23043265262884571204493451 34564897894326856806740177)
    ·
      refine ⟨25923673420745142605055133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34564897894326856806740177 25923673420745142605055133)
      ·
        refine ⟨9721377532779428476895675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25923673420745142605055133 9721377532779428476895675)
        ·
          refine ⟨14582066299169142715343513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9721377532779428476895675 14582066299169142715343513)
          ·
            refine ⟨10936549724376857036507635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14582066299169142715343513 10936549724376857036507635)
            ·
              refine ⟨16404824586565285554761453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10936549724376857036507635 16404824586565285554761453)
              ·
                refine ⟨6151809219961982083035545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16404824586565285554761453 6151809219961982083035545)
                ·
                  refine ⟨4613856914971486562276659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6151809219961982083035545 4613856914971486562276659)
                  ·
                    refine ⟨6920785372457229843414989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4613856914971486562276659 6920785372457229843414989)
                    ·
                      refine ⟨2595294514671461191280621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6920785372457229843414989 2595294514671461191280621)
                      ·
                        rfl

theorem cell23_5054318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_5054318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054318 prefixEnd_5054318 := by exact prefixLift 5054318
  have htrace : WordTrace (prefixWord ++ tailWord_5054318) baseStart_5054318 baseEnd_5054318 := by
    simpa [prefixWord, tailWord_5054318, baseEnd_5054318] using wordTrace_append hprefix tailTrace_5054318
  have hstable : (prefixWord ++ tailWord_5054318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054318).length < 2 ^ (prefixWord ++ tailWord_5054318).sum := by decide
  have hdescent : baseEnd_5054318 < baseStart_5054318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054414 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4]
def baseStart_5054414 : Nat := 118140960795 + 5054414 * 2 ^ 59
def prefixEnd_5054414 : Nat := 4983230072969 + 3 ^ 40 * 5054414 * 2
def baseEnd_5054414 : Nat := 2595343808814292815680179

theorem tailTrace_5054414 : CollatzResearch.WordTrace tailWord_5054414 prefixEnd_5054414 2595343808814292815680179 := by
  unfold tailWord_5054414
  simp only [CollatzResearch.WordTrace]
  refine ⟨23043702938841097253930287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122899749007152518687628197 23043702938841097253930287)
  ·
    refine ⟨34565554408261645880895431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23043702938841097253930287 34565554408261645880895431)
    ·
      refine ⟨51848331612392468821343147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34565554408261645880895431 51848331612392468821343147)
      ·
        refine ⟨77772497418588703232014721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51848331612392468821343147 77772497418588703232014721)
        ·
          refine ⟨58329373063941527424011041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77772497418588703232014721 58329373063941527424011041)
          ·
            refine ⟨43747029797956145568008281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58329373063941527424011041 43747029797956145568008281)
            ·
              refine ⟨32810272348467109176006211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43747029797956145568008281 32810272348467109176006211)
              ·
                refine ⟨49215408522700663764009317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32810272348467109176006211 49215408522700663764009317)
                ·
                  refine ⟨9227889098006374455751747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49215408522700663764009317 9227889098006374455751747)
                  ·
                    refine ⟨13841833647009561683627621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9227889098006374455751747 13841833647009561683627621)
                    ·
                      refine ⟨2595343808814292815680179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13841833647009561683627621 2595343808814292815680179)
                      ·
                        rfl

theorem cell23_5054414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_5054414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054414 prefixEnd_5054414 := by exact prefixLift 5054414
  have htrace : WordTrace (prefixWord ++ tailWord_5054414) baseStart_5054414 baseEnd_5054414 := by
    simpa [prefixWord, tailWord_5054414, baseEnd_5054414] using wordTrace_append hprefix tailTrace_5054414
  have hstable : (prefixWord ++ tailWord_5054414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054414).length < 2 ^ (prefixWord ++ tailWord_5054414).sum := by decide
  have hdescent : baseEnd_5054414 < baseStart_5054414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054431 : List Nat := [1, 1, 2, 3, 4, 1, 2, 1, 2, 4, 2]
def baseStart_5054431 : Nat := 118140960795 + 5054431 * 2 ^ 59
def prefixEnd_5054431 : Nat := 4983230072969 + 3 ^ 40 * 5054431 * 2
def baseEnd_5054431 : Nat := 2595352537985419249167601

theorem tailTrace_5054431 : CollatzResearch.WordTrace tailWord_5054431 prefixEnd_5054431 2595352537985419249167601 := by
  unfold tailWord_5054431
  simp only [CollatzResearch.WordTrace]
  refine ⟨184350243551667189934811147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122900162367778126623207431 184350243551667189934811147)
  ·
    refine ⟨276525365327500784902216721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184350243551667189934811147 276525365327500784902216721)
    ·
      refine ⟨207394023995625588676662541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276525365327500784902216721 207394023995625588676662541)
      ·
        refine ⟨77772758998359595753748453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207394023995625588676662541 77772758998359595753748453)
        ·
          refine ⟨14582392312192424203827835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77772758998359595753748453 14582392312192424203827835)
          ·
            refine ⟨21873588468288636305741753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14582392312192424203827835 21873588468288636305741753)
            ·
              refine ⟨16405191351216477229306315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21873588468288636305741753 16405191351216477229306315)
              ·
                refine ⟨24607787026824715843959473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16405191351216477229306315 24607787026824715843959473)
                ·
                  refine ⟨18455840270118536882969605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24607787026824715843959473 18455840270118536882969605)
                  ·
                    refine ⟨3460470050647225665556801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18455840270118536882969605 3460470050647225665556801)
                    ·
                      refine ⟨2595352537985419249167601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3460470050647225665556801 2595352537985419249167601)
                      ·
                        rfl

theorem cell23_5054431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 4, 2].length) (baseStart_5054431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054431 prefixEnd_5054431 := by exact prefixLift 5054431
  have htrace : WordTrace (prefixWord ++ tailWord_5054431) baseStart_5054431 baseEnd_5054431 := by
    simpa [prefixWord, tailWord_5054431, baseEnd_5054431] using wordTrace_append hprefix tailTrace_5054431
  have hstable : (prefixWord ++ tailWord_5054431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054431).length < 2 ^ (prefixWord ++ tailWord_5054431).sum := by decide
  have hdescent : baseEnd_5054431 < baseStart_5054431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054501 : List Nat := [1, 3, 1, 2, 2, 3, 3, 2, 1, 5]
def baseStart_5054501 : Nat := 118140960795 + 5054501 * 2 ^ 59
def prefixEnd_5054501 : Nat := 4983230072969 + 3 ^ 40 * 5054501 * 2
def baseEnd_5054501 : Nat := 865129493877077991764093

theorem tailTrace_5054501 : CollatzResearch.WordTrace tailWord_5054501 prefixEnd_5054501 865129493877077991764093 := by
  unfold tailWord_5054501
  simp only [CollatzResearch.WordTrace]
  refine ⟨184352796661413591889859357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122901864440942394593239571 184352796661413591889859357)
  ·
    refine ⟨69132298748030096958697259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184352796661413591889859357 69132298748030096958697259)
    ·
      refine ⟨103698448122045145438045889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69132298748030096958697259 103698448122045145438045889)
      ·
        refine ⟨77773836091533859078534417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103698448122045145438045889 77773836091533859078534417)
        ·
          refine ⟨58330377068650394308900813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77773836091533859078534417 58330377068650394308900813)
          ·
            refine ⟨21873891400743897865837805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58330377068650394308900813 21873891400743897865837805)
            ·
              refine ⟨8202709275278961699689177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21873891400743897865837805 8202709275278961699689177)
              ·
                refine ⟨6152031956459221274766883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8202709275278961699689177 6152031956459221274766883)
                ·
                  refine ⟨9228047934688831912150325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6152031956459221274766883 9228047934688831912150325)
                  ·
                    refine ⟨865129493877077991764093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9228047934688831912150325 865129493877077991764093)
                    ·
                      rfl

theorem cell23_5054501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 5].length) (baseStart_5054501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054501 prefixEnd_5054501 := by exact prefixLift 5054501
  have htrace : WordTrace (prefixWord ++ tailWord_5054501) baseStart_5054501 baseEnd_5054501 := by
    simpa [prefixWord, tailWord_5054501, baseEnd_5054501] using wordTrace_append hprefix tailTrace_5054501
  have hstable : (prefixWord ++ tailWord_5054501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054501).length < 2 ^ (prefixWord ++ tailWord_5054501).sum := by decide
  have hdescent : baseEnd_5054501 < baseStart_5054501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054514 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 3, 6]
def baseStart_5054514 : Nat := 118140960795 + 5054514 * 2 ^ 59
def prefixEnd_5054514 : Nat := 4983230072969 + 3 ^ 40 * 5054514 * 2
def baseEnd_5054514 : Nat := 865131718959914141476573

theorem tailTrace_5054514 : CollatzResearch.WordTrace tailWord_5054514 prefixEnd_5054514 865131718959914141476573 := by
  unfold tailWord_5054514
  simp only [CollatzResearch.WordTrace]
  refine ⟨46088317702591623777520649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122902180540244330073388397 46088317702591623777520649)
  ·
    refine ⟨34566238276943717833140487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46088317702591623777520649 34566238276943717833140487)
    ·
      refine ⟨51849357415415576749710731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34566238276943717833140487 51849357415415576749710731)
      ·
        refine ⟨77774036123123365124566097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51849357415415576749710731 77774036123123365124566097)
        ·
          refine ⟨58330527092342523843424573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77774036123123365124566097 58330527092342523843424573)
          ·
            refine ⟨21873947659628446441284215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58330527092342523843424573 21873947659628446441284215)
            ·
              refine ⟨32810921489442669661926323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21873947659628446441284215 32810921489442669661926323)
              ·
                refine ⟨49216382234164004492889485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32810921489442669661926323 49216382234164004492889485)
                ·
                  refine ⟨18456143337811501684833557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49216382234164004492889485 18456143337811501684833557)
                  ·
                    refine ⟨865131718959914141476573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18456143337811501684833557 865131718959914141476573)
                    ·
                      rfl

theorem cell23_5054514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_5054514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054514 prefixEnd_5054514 := by exact prefixLift 5054514
  have htrace : WordTrace (prefixWord ++ tailWord_5054514) baseStart_5054514 baseEnd_5054514 := by
    simpa [prefixWord, tailWord_5054514, baseEnd_5054514] using wordTrace_append hprefix tailTrace_5054514
  have hstable : (prefixWord ++ tailWord_5054514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054514).length < 2 ^ (prefixWord ++ tailWord_5054514).sum := by decide
  have hdescent : baseEnd_5054514 < baseStart_5054514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054538 : List Nat := [3, 1, 2, 1, 1, 2, 1, 5, 3, 2, 2]
def baseStart_5054538 : Nat := 118140960795 + 5054538 * 2 ^ 59
def prefixEnd_5054538 : Nat := 4983230072969 + 3 ^ 40 * 5054538 * 2
def baseEnd_5054538 : Nat := 2595407480415450330529609

theorem tailTrace_5054538 : CollatzResearch.WordTrace tailWord_5054538 prefixEnd_5054538 2595407480415450330529609 := by
  unfold tailWord_5054538
  simp only [CollatzResearch.WordTrace]
  refine ⟨46088536540569886802239067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122902764108186364805970845 46088536540569886802239067)
  ·
    refine ⟨69132804810854830203358601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46088536540569886802239067 69132804810854830203358601)
    ·
      refine ⟨51849603608141122652518951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69132804810854830203358601 51849603608141122652518951)
      ·
        refine ⟨77774405412211683978778427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51849603608141122652518951 77774405412211683978778427)
        ·
          refine ⟨116661608118317525968167641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77774405412211683978778427 116661608118317525968167641)
          ·
            refine ⟨87496206088738144476125731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116661608118317525968167641 87496206088738144476125731)
            ·
              refine ⟨131244309133107216714188597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87496206088738144476125731 131244309133107216714188597)
              ·
                refine ⟨12304153981228801566955181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 131244309133107216714188597 12304153981228801566955181)
                ·
                  refine ⟨4614057742960800587608193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12304153981228801566955181 4614057742960800587608193)
                  ·
                    refine ⟨3460543307220600440706145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4614057742960800587608193 3460543307220600440706145)
                    ·
                      refine ⟨2595407480415450330529609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3460543307220600440706145 2595407480415450330529609)
                      ·
                        rfl

theorem cell23_5054538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 3, 2, 2].length) (baseStart_5054538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054538 prefixEnd_5054538 := by exact prefixLift 5054538
  have htrace : WordTrace (prefixWord ++ tailWord_5054538) baseStart_5054538 baseEnd_5054538 := by
    simpa [prefixWord, tailWord_5054538, baseEnd_5054538] using wordTrace_append hprefix tailTrace_5054538
  have hstable : (prefixWord ++ tailWord_5054538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054538).length < 2 ^ (prefixWord ++ tailWord_5054538).sum := by decide
  have hdescent : baseEnd_5054538 < baseStart_5054538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054541 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_5054541 : Nat := 118140960795 + 5054541 * 2 ^ 59
def prefixEnd_5054541 : Nat := 4983230072969 + 3 ^ 40 * 5054541 * 2
def baseEnd_5054541 : Nat := 2595409020857413818792095

theorem tailTrace_5054541 : CollatzResearch.WordTrace tailWord_5054541 prefixEnd_5054541 2595409020857413818792095 := by
  unfold tailWord_5054541
  simp only [CollatzResearch.WordTrace]
  refine ⟨184354255581268678721315477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122902837054179119147543651 184354255581268678721315477)
  ·
    refine ⟨8641605730371969315061663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 184354255581268678721315477 8641605730371969315061663)
    ·
      refine ⟨12962408595557953972592495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8641605730371969315061663 12962408595557953972592495)
      ·
        refine ⟨19443612893336930958888743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12962408595557953972592495 19443612893336930958888743)
        ·
          refine ⟨29165419340005396438333115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19443612893336930958888743 29165419340005396438333115)
          ·
            refine ⟨43748129010008094657499673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29165419340005396438333115 43748129010008094657499673)
            ·
              refine ⟨32811096757506070993124755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43748129010008094657499673 32811096757506070993124755)
              ·
                refine ⟨49216645136259106489687133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32811096757506070993124755 49216645136259106489687133)
                ·
                  refine ⟨18456241926097164933632675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49216645136259106489687133 18456241926097164933632675)
                  ·
                    refine ⟨27684362889145747400449013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18456241926097164933632675 27684362889145747400449013)
                    ·
                      refine ⟨2595409020857413818792095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27684362889145747400449013 2595409020857413818792095)
                      ·
                        rfl

theorem cell23_5054541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_5054541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054541 prefixEnd_5054541 := by exact prefixLift 5054541
  have htrace : WordTrace (prefixWord ++ tailWord_5054541) baseStart_5054541 baseEnd_5054541 := by
    simpa [prefixWord, tailWord_5054541, baseEnd_5054541] using wordTrace_append hprefix tailTrace_5054541
  have hstable : (prefixWord ++ tailWord_5054541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054541).length < 2 ^ (prefixWord ++ tailWord_5054541).sum := by decide
  have hdescent : baseEnd_5054541 < baseStart_5054541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054572 : List Nat := [2, 2, 1, 1, 3, 4, 2, 3, 1, 2, 2]
def baseStart_5054572 : Nat := 118140960795 + 5054572 * 2 ^ 59
def prefixEnd_5054572 : Nat := 4983230072969 + 3 ^ 40 * 5054572 * 2
def baseEnd_5054572 : Nat := 2595424938757703197504453

theorem tailTrace_5054572 : CollatzResearch.WordTrace tailWord_5054572 prefixEnd_5054572 2595424938757703197504453 := by
  unfold tailWord_5054572
  simp only [CollatzResearch.WordTrace]
  refine ⟨92177693122078185507846985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122903590829437580677129313 92177693122078185507846985)
  ·
    refine ⟨69133269841558639130885239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92177693122078185507846985 69133269841558639130885239)
    ·
      refine ⟨103699904762337958696327859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69133269841558639130885239 103699904762337958696327859)
      ·
        refine ⟨155549857143506938044491789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103699904762337958696327859 155549857143506938044491789)
        ·
          refine ⟨58331196428815101766684421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155549857143506938044491789 58331196428815101766684421)
          ·
            refine ⟨10937099330402831581253329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58331196428815101766684421 10937099330402831581253329)
            ·
              refine ⟨8202824497802123685939997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10937099330402831581253329 8202824497802123685939997)
              ·
                refine ⟨3076059186675796382227499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8202824497802123685939997 3076059186675796382227499)
                ·
                  refine ⟨4614088780013694573341249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3076059186675796382227499 4614088780013694573341249)
                  ·
                    refine ⟨3460566585010270930005937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4614088780013694573341249 3460566585010270930005937)
                    ·
                      refine ⟨2595424938757703197504453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3460566585010270930005937 2595424938757703197504453)
                      ·
                        rfl

theorem cell23_5054572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3, 1, 2, 2].length) (baseStart_5054572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054572 prefixEnd_5054572 := by exact prefixLift 5054572
  have htrace : WordTrace (prefixWord ++ tailWord_5054572) baseStart_5054572 baseEnd_5054572 := by
    simpa [prefixWord, tailWord_5054572, baseEnd_5054572] using wordTrace_append hprefix tailTrace_5054572
  have hstable : (prefixWord ++ tailWord_5054572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054572).length < 2 ^ (prefixWord ++ tailWord_5054572).sum := by decide
  have hdescent : baseEnd_5054572 < baseStart_5054572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054575 : List Nat := [1, 1, 2, 1, 3, 6, 2, 1, 1, 2, 3]
def baseStart_5054575 : Nat := 118140960795 + 5054575 * 2 ^ 59
def prefixEnd_5054575 : Nat := 4983230072969 + 3 ^ 40 * 5054575 * 2
def baseEnd_5054575 : Nat := 2595426479199666685766939

theorem tailTrace_5054575 : CollatzResearch.WordTrace tailWord_5054575 prefixEnd_5054575 2595426479199666685766939 := by
  unfold tailWord_5054575
  simp only [CollatzResearch.WordTrace]
  refine ⟨184355495663145502528053179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122903663775430335018702119 184355495663145502528053179)
  ·
    refine ⟨276533243494718253792079769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184355495663145502528053179 276533243494718253792079769)
    ·
      refine ⟨207399932621038690344059827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276533243494718253792079769 207399932621038690344059827)
      ·
        refine ⟨311099898931558035516089741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207399932621038690344059827 311099898931558035516089741)
        ·
          refine ⟨116662462099334263318533653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 311099898931558035516089741 116662462099334263318533653)
          ·
            refine ⟨5468552910906293593056265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 116662462099334263318533653 5468552910906293593056265)
            ·
              refine ⟨4101414683179720194792199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5468552910906293593056265 4101414683179720194792199)
              ·
                refine ⟨6152122024769580292188299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4101414683179720194792199 6152122024769580292188299)
                ·
                  refine ⟨9228183037154370438282449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6152122024769580292188299 9228183037154370438282449)
                  ·
                    refine ⟨6921137277865777828711837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9228183037154370438282449 6921137277865777828711837)
                    ·
                      refine ⟨2595426479199666685766939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6921137277865777828711837 2595426479199666685766939)
                      ·
                        rfl

theorem cell23_5054575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 1, 2, 3].length) (baseStart_5054575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054575 prefixEnd_5054575 := by exact prefixLift 5054575
  have htrace : WordTrace (prefixWord ++ tailWord_5054575) baseStart_5054575 baseEnd_5054575 := by
    simpa [prefixWord, tailWord_5054575, baseEnd_5054575] using wordTrace_append hprefix tailTrace_5054575
  have hstable : (prefixWord ++ tailWord_5054575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054575).length < 2 ^ (prefixWord ++ tailWord_5054575).sum := by decide
  have hdescent : baseEnd_5054575 < baseStart_5054575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054588 : List Nat := [2, 2, 2, 1, 1, 5, 1, 1, 4, 1, 3]
def baseStart_5054588 : Nat := 118140960795 + 5054588 * 2 ^ 59
def prefixEnd_5054588 : Nat := 4983230072969 + 3 ^ 40 * 5054588 * 2
def baseEnd_5054588 : Nat := 2595433154448175134904379

theorem tailTrace_5054588 : CollatzResearch.WordTrace tailWord_5054588 prefixEnd_5054588 2595433154448175134904379 := by
  unfold tailWord_5054588
  simp only [CollatzResearch.WordTrace]
  refine ⟨92177984906049202874138209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122903979874732270498850945 92177984906049202874138209)
  ·
    refine ⟨69133488679536902155603657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92177984906049202874138209 69133488679536902155603657)
    ·
      refine ⟨51850116509652676616702743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69133488679536902155603657 51850116509652676616702743)
      ·
        refine ⟨77775174764479014925054115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51850116509652676616702743 77775174764479014925054115)
        ·
          refine ⟨116662762146718522387581173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77775174764479014925054115 116662762146718522387581173)
          ·
            refine ⟨10937133951254861473835735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 116662762146718522387581173 10937133951254861473835735)
            ·
              refine ⟨16405700926882292210753603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10937133951254861473835735 16405700926882292210753603)
              ·
                refine ⟨24608551390323438316130405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16405700926882292210753603 24608551390323438316130405)
                ·
                  refine ⟨4614103385685644684274451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24608551390323438316130405 4614103385685644684274451)
                  ·
                    refine ⟨6921155078528467026411677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4614103385685644684274451 6921155078528467026411677)
                    ·
                      refine ⟨2595433154448175134904379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6921155078528467026411677 2595433154448175134904379)
                      ·
                        rfl

theorem cell23_5054588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_5054588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054588 prefixEnd_5054588 := by exact prefixLift 5054588
  have htrace : WordTrace (prefixWord ++ tailWord_5054588) baseStart_5054588 baseEnd_5054588 := by
    simpa [prefixWord, tailWord_5054588, baseEnd_5054588] using wordTrace_append hprefix tailTrace_5054588
  have hstable : (prefixWord ++ tailWord_5054588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054588).length < 2 ^ (prefixWord ++ tailWord_5054588).sum := by decide
  have hdescent : baseEnd_5054588 < baseStart_5054588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054612 : List Nat := [2, 4, 2, 3, 2, 1, 2, 7]
def baseStart_5054612 : Nat := 118140960795 + 5054612 * 2 ^ 59
def prefixEnd_5054612 : Nat := 4983230072969 + 3 ^ 40 * 5054612 * 2
def baseEnd_5054612 : Nat := 96127610295699371889047

theorem tailTrace_5054612 : CollatzResearch.WordTrace tailWord_5054612 prefixEnd_5054612 96127610295699371889047 := by
  unfold tailWord_5054612
  simp only [CollatzResearch.WordTrace]
  refine ⟨92178422582005728923575045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122904563442674305231433393 92178422582005728923575045)
  ·
    refine ⟨17283454234126074173170321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92178422582005728923575045 17283454234126074173170321)
    ·
      refine ⟨12962590675594555629877741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17283454234126074173170321 12962590675594555629877741)
      ·
        refine ⟨4860971503347958361204153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12962590675594555629877741 4860971503347958361204153)
        ·
          refine ⟨3645728627510968770903115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4860971503347958361204153 3645728627510968770903115)
          ·
            refine ⟨5468592941266453156354673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3645728627510968770903115 5468592941266453156354673)
            ·
              refine ⟨4101444705949839867266005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5468592941266453156354673 4101444705949839867266005)
              ·
                refine ⟨96127610295699371889047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4101444705949839867266005 96127610295699371889047)
                ·
                  rfl

theorem cell23_5054612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 7].length) (baseStart_5054612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054612 prefixEnd_5054612 := by exact prefixLift 5054612
  have htrace : WordTrace (prefixWord ++ tailWord_5054612) baseStart_5054612 baseEnd_5054612 := by
    simpa [prefixWord, tailWord_5054612, baseEnd_5054612] using wordTrace_append hprefix tailTrace_5054612
  have hstable : (prefixWord ++ tailWord_5054612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054612).length < 2 ^ (prefixWord ++ tailWord_5054612).sum := by decide
  have hdescent : baseEnd_5054612 < baseStart_5054612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054661 : List Nat := [1, 3, 1, 1, 1, 1, 4, 3, 2, 3, 3]
def baseStart_5054661 : Nat := 118140960795 + 5054661 * 2 ^ 59
def prefixEnd_5054661 : Nat := 4983230072969 + 3 ^ 40 * 5054661 * 2
def baseEnd_5054661 : Nat := 2595470638535953349291543

theorem tailTrace_5054661 : CollatzResearch.WordTrace tailWord_5054661 prefixEnd_5054661 2595470638535953349291543 := by
  unfold tailWord_5054661
  simp only [CollatzResearch.WordTrace]
  refine ⟨184358632340833939215683837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122905754893889292810455891 184358632340833939215683837)
  ·
    refine ⟨69134487127812727205881439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184358632340833939215683837 69134487127812727205881439)
    ·
      refine ⟨103701730691719090808822159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69134487127812727205881439 103701730691719090808822159)
      ·
        refine ⟨155552596037578636213233239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103701730691719090808822159 155552596037578636213233239)
        ·
          refine ⟨233328894056367954319849859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155552596037578636213233239 233328894056367954319849859)
          ·
            refine ⟨349993341084551931479774789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233328894056367954319849859 349993341084551931479774789)
            ·
              refine ⟨65623751453353487152457773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 349993341084551931479774789 65623751453353487152457773)
              ·
                refine ⟨24608906795007557682171665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65623751453353487152457773 24608906795007557682171665)
                ·
                  refine ⟨18456680096255668261628749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24608906795007557682171665 18456680096255668261628749)
                  ·
                    refine ⟨6921255036095875598110781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18456680096255668261628749 6921255036095875598110781)
                    ·
                      refine ⟨2595470638535953349291543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6921255036095875598110781 2595470638535953349291543)
                      ·
                        rfl

theorem cell23_5054661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 3, 3].length) (baseStart_5054661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054661 prefixEnd_5054661 := by exact prefixLift 5054661
  have htrace : WordTrace (prefixWord ++ tailWord_5054661) baseStart_5054661 baseEnd_5054661 := by
    simpa [prefixWord, tailWord_5054661, baseEnd_5054661] using wordTrace_append hprefix tailTrace_5054661
  have hstable : (prefixWord ++ tailWord_5054661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054661).length < 2 ^ (prefixWord ++ tailWord_5054661).sum := by decide
  have hdescent : baseEnd_5054661 < baseStart_5054661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054681 : List Nat := [1, 2, 1, 2, 3, 1, 3, 3, 2, 5]
def baseStart_5054681 : Nat := 118140960795 + 5054681 * 2 ^ 59
def prefixEnd_5054681 : Nat := 4983230072969 + 3 ^ 40 * 5054681 * 2
def baseEnd_5054681 : Nat := 865160302716347757013817

theorem tailTrace_5054681 : CollatzResearch.WordTrace tailWord_5054681 prefixEnd_5054681 865160302716347757013817 := by
  unfold tailWord_5054681
  simp only [CollatzResearch.WordTrace]
  refine ⟨184359361800761482631411897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122906241200507655087607931 184359361800761482631411897)
  ·
    refine ⟨138269521350571111973558923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184359361800761482631411897 138269521350571111973558923)
    ·
      refine ⟨207404282025856667960338385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138269521350571111973558923 207404282025856667960338385)
      ·
        refine ⟨155553211519392500970253789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207404282025856667960338385 155553211519392500970253789)
        ·
          refine ⟨58332454319772187863845171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155553211519392500970253789 58332454319772187863845171)
          ·
            refine ⟨87498681479658281795767757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58332454319772187863845171 87498681479658281795767757)
            ·
              refine ⟨32812005554871855673412909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87498681479658281795767757 32812005554871855673412909)
              ·
                refine ⟨12304502083076945877529841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32812005554871855673412909 12304502083076945877529841)
                ·
                  refine ⟨9228376562307709408147381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12304502083076945877529841 9228376562307709408147381)
                  ·
                    refine ⟨865160302716347757013817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9228376562307709408147381 865160302716347757013817)
                    ·
                      rfl

theorem cell23_5054681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 5].length) (baseStart_5054681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054681 prefixEnd_5054681 := by exact prefixLift 5054681
  have htrace : WordTrace (prefixWord ++ tailWord_5054681) baseStart_5054681 baseEnd_5054681 := by
    simpa [prefixWord, tailWord_5054681, baseEnd_5054681] using wordTrace_append hprefix tailTrace_5054681
  have hstable : (prefixWord ++ tailWord_5054681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054681).length < 2 ^ (prefixWord ++ tailWord_5054681).sum := by decide
  have hdescent : baseEnd_5054681 < baseStart_5054681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054718 : List Nat := [4, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_5054718 : Nat := 118140960795 + 5054718 * 2 ^ 59
def prefixEnd_5054718 : Nat := 4983230072969 + 3 ^ 40 * 5054718 * 2
def baseEnd_5054718 : Nat := 2595499906933259626278781

theorem tailTrace_5054718 : CollatzResearch.WordTrace tailWord_5054718 prefixEnd_5054718 2595499906933259626278781 := by
  unfold tailWord_5054718
  simp only [CollatzResearch.WordTrace]
  refine ⟨23045088912703429743813601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122907140867751625300339205 23045088912703429743813601)
  ·
    refine ⟨17283816684527572307860201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23045088912703429743813601 17283816684527572307860201)
    ·
      refine ⟨12962862513395679230895151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17283816684527572307860201 12962862513395679230895151)
      ·
        refine ⟨19444293770093518846342727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12962862513395679230895151 19444293770093518846342727)
        ·
          refine ⟨29166440655140278269514091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19444293770093518846342727 29166440655140278269514091)
          ·
            refine ⟨43749660982710417404271137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29166440655140278269514091 43749660982710417404271137)
            ·
              refine ⟨32812245737032813053203353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43749660982710417404271137 32812245737032813053203353)
              ·
                refine ⟨24609184302774609789902515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32812245737032813053203353 24609184302774609789902515)
                ·
                  refine ⟨36913776454161914684853773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24609184302774609789902515 36913776454161914684853773)
                  ·
                    refine ⟨13842666170310718006820165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36913776454161914684853773 13842666170310718006820165)
                    ·
                      refine ⟨2595499906933259626278781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13842666170310718006820165 2595499906933259626278781)
                      ·
                        rfl

theorem cell23_5054718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_5054718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054718 prefixEnd_5054718 := by exact prefixLift 5054718
  have htrace : WordTrace (prefixWord ++ tailWord_5054718) baseStart_5054718 baseEnd_5054718 := by
    simpa [prefixWord, tailWord_5054718, baseEnd_5054718] using wordTrace_append hprefix tailTrace_5054718
  have hstable : (prefixWord ++ tailWord_5054718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054718).length < 2 ^ (prefixWord ++ tailWord_5054718).sum := by decide
  have hdescent : baseEnd_5054718 < baseStart_5054718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054728 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 5, 4]
def baseStart_5054728 : Nat := 118140960795 + 5054728 * 2 ^ 59
def prefixEnd_5054728 : Nat := 4983230072969 + 3 ^ 40 * 5054728 * 2
def baseEnd_5054728 : Nat := 865168347246601529051245

theorem tailTrace_5054728 : CollatzResearch.WordTrace tailWord_5054728 prefixEnd_5054728 865168347246601529051245 := by
  unfold tailWord_5054728
  simp only [CollatzResearch.WordTrace]
  refine ⟨92180538015795604829186419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122907384021060806438915225 92180538015795604829186419)
  ·
    refine ⟨138270807023693407243779629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92180538015795604829186419 138270807023693407243779629)
    ·
      refine ⟨51851552633885027716417361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138270807023693407243779629 51851552633885027716417361)
      ·
        refine ⟨38888664475413770787313021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51851552633885027716417361 38888664475413770787313021)
        ·
          refine ⟨14583249178280164045242383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38888664475413770787313021 14583249178280164045242383)
          ·
            refine ⟨21874873767420246067863575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14583249178280164045242383 21874873767420246067863575)
            ·
              refine ⟨32812310651130369101795363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21874873767420246067863575 32812310651130369101795363)
              ·
                refine ⟨49218465976695553652693045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32812310651130369101795363 49218465976695553652693045)
                ·
                  refine ⟨4614231185315208154939973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49218465976695553652693045 4614231185315208154939973)
                  ·
                    refine ⟨865168347246601529051245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4614231185315208154939973 865168347246601529051245)
                    ·
                      rfl

theorem cell23_5054728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_5054728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054728 prefixEnd_5054728 := by exact prefixLift 5054728
  have htrace : WordTrace (prefixWord ++ tailWord_5054728) baseStart_5054728 baseEnd_5054728 := by
    simpa [prefixWord, tailWord_5054728, baseEnd_5054728] using wordTrace_append hprefix tailTrace_5054728
  have hstable : (prefixWord ++ tailWord_5054728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054728).length < 2 ^ (prefixWord ++ tailWord_5054728).sum := by decide
  have hdescent : baseEnd_5054728 < baseStart_5054728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054762 : List Nat := [3, 1, 4, 2, 2, 1, 2, 1, 3, 4]
def baseStart_5054762 : Nat := 118140960795 + 5054762 * 2 ^ 59
def prefixEnd_5054762 : Nat := 4983230072969 + 3 ^ 40 * 5054762 * 2
def baseEnd_5054762 : Nat := 865174166694019151376193

theorem tailTrace_5054762 : CollatzResearch.WordTrace tailWord_5054762 prefixEnd_5054762 865174166694019151376193 := by
  unfold tailWord_5054762
  simp only [CollatzResearch.WordTrace]
  refine ⟨46090579028367008366277635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122908210742312022310073693 46090579028367008366277635)
  ·
    refine ⟨69135868542550512549416453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46090579028367008366277635 69135868542550512549416453)
    ·
      refine ⟨12962975351728221103015585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69135868542550512549416453 12962975351728221103015585)
      ·
        refine ⟨9722231513796165827261689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12962975351728221103015585 9722231513796165827261689)
        ·
          refine ⟨7291673635347124370446267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9722231513796165827261689 7291673635347124370446267)
          ·
            refine ⟨10937510453020686555669401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7291673635347124370446267 10937510453020686555669401)
            ·
              refine ⟨8203132839765514916752051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10937510453020686555669401 8203132839765514916752051)
              ·
                refine ⟨12304699259648272375128077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8203132839765514916752051 12304699259648272375128077)
                ·
                  refine ⟨4614262222368102140673029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12304699259648272375128077 4614262222368102140673029)
                  ·
                    refine ⟨865174166694019151376193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4614262222368102140673029 865174166694019151376193)
                    ·
                      rfl

theorem cell23_5054762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_5054762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054762 prefixEnd_5054762 := by exact prefixLift 5054762
  have htrace : WordTrace (prefixWord ++ tailWord_5054762) baseStart_5054762 baseEnd_5054762 := by
    simpa [prefixWord, tailWord_5054762, baseEnd_5054762] using wordTrace_append hprefix tailTrace_5054762
  have hstable : (prefixWord ++ tailWord_5054762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054762).length < 2 ^ (prefixWord ++ tailWord_5054762).sum := by decide
  have hdescent : baseEnd_5054762 < baseStart_5054762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054819 : List Nat := [1, 1, 1, 5, 2, 1, 5, 2, 1, 1, 3]
def baseStart_5054819 : Nat := 118140960795 + 5054819 * 2 ^ 59
def prefixEnd_5054819 : Nat := 4983230072969 + 3 ^ 40 * 5054819 * 2
def baseEnd_5054819 : Nat := 2595551768479363731115817

theorem tailTrace_5054819 : CollatzResearch.WordTrace tailWord_5054819 prefixEnd_5054819 2595551768479363731115817 := by
  unfold tailWord_5054819
  simp only [CollatzResearch.WordTrace]
  refine ⟨184364395074261532199935511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122909596716174354799957007 184364395074261532199935511)
  ·
    refine ⟨276546592611392298299903267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184364395074261532199935511 276546592611392298299903267)
    ·
      refine ⟨414819888917088447449854901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276546592611392298299903267 414819888917088447449854901)
      ·
        refine ⟨38889364585977041948423897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 414819888917088447449854901 38889364585977041948423897)
        ·
          refine ⟨29167023439482781461317923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38889364585977041948423897 29167023439482781461317923)
          ·
            refine ⟨43750535159224172191976885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29167023439482781461317923 43750535159224172191976885)
            ·
              refine ⟨4101612671177266142997833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43750535159224172191976885 4101612671177266142997833)
              ·
                refine ⟨3076209503382949607248375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4101612671177266142997833 3076209503382949607248375)
                ·
                  refine ⟨4614314255074424410872563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3076209503382949607248375 4614314255074424410872563)
                  ·
                    refine ⟨6921471382611636616308845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4614314255074424410872563 6921471382611636616308845)
                    ·
                      refine ⟨2595551768479363731115817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6921471382611636616308845 2595551768479363731115817)
                      ·
                        rfl

theorem cell23_5054819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_5054819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054819 prefixEnd_5054819 := by exact prefixLift 5054819
  have htrace : WordTrace (prefixWord ++ tailWord_5054819) baseStart_5054819 baseEnd_5054819 := by
    simpa [prefixWord, tailWord_5054819, baseEnd_5054819] using wordTrace_append hprefix tailTrace_5054819
  have hstable : (prefixWord ++ tailWord_5054819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054819).length < 2 ^ (prefixWord ++ tailWord_5054819).sum := by decide
  have hdescent : baseEnd_5054819 < baseStart_5054819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054845 : List Nat := [1, 4, 1, 1, 2, 4, 1, 1, 3, 2, 3]
def baseStart_5054845 : Nat := 118140960795 + 5054845 * 2 ^ 59
def prefixEnd_5054845 : Nat := 4983230072969 + 3 ^ 40 * 5054845 * 2
def baseEnd_5054845 : Nat := 2595565118976380629390697

theorem tailTrace_5054845 : CollatzResearch.WordTrace tailWord_5054845 prefixEnd_5054845 2595565118976380629390697 := by
  unfold tailWord_5054845
  simp only [CollatzResearch.WordTrace]
  refine ⟨184365343372167338640381989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122910228914778225760254659 184365343372167338640381989)
  ·
    refine ⟨34568501882281375995071623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184365343372167338640381989 34568501882281375995071623)
    ·
      refine ⟨51852752823422063992607435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34568501882281375995071623 51852752823422063992607435)
      ·
        refine ⟨77779129235133095988911153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51852752823422063992607435 77779129235133095988911153)
        ·
          refine ⟨58334346926349821991683365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77779129235133095988911153 58334346926349821991683365)
          ·
            refine ⟨10937690048690591623440631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58334346926349821991683365 10937690048690591623440631)
            ·
              refine ⟨16406535073035887435160947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10937690048690591623440631 16406535073035887435160947)
              ·
                refine ⟨24609802609553831152741421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16406535073035887435160947 24609802609553831152741421)
                ·
                  refine ⟨9228675978582686682278033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24609802609553831152741421 9228675978582686682278033)
                  ·
                    refine ⟨6921506983937015011708525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9228675978582686682278033 6921506983937015011708525)
                    ·
                      refine ⟨2595565118976380629390697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6921506983937015011708525 2595565118976380629390697)
                      ·
                        rfl

theorem cell23_5054845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_5054845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054845 prefixEnd_5054845 := by exact prefixLift 5054845
  have htrace : WordTrace (prefixWord ++ tailWord_5054845) baseStart_5054845 baseEnd_5054845 := by
    simpa [prefixWord, tailWord_5054845, baseEnd_5054845] using wordTrace_append hprefix tailTrace_5054845
  have hstable : (prefixWord ++ tailWord_5054845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054845).length < 2 ^ (prefixWord ++ tailWord_5054845).sum := by decide
  have hdescent : baseEnd_5054845 < baseStart_5054845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054862 : List Nat := [4, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5]
def baseStart_5054862 : Nat := 118140960795 + 5054862 * 2 ^ 59
def prefixEnd_5054862 : Nat := 4983230072969 + 3 ^ 40 * 5054862 * 2
def baseEnd_5054862 : Nat := 2595573848147507062878119

theorem tailTrace_5054862 : CollatzResearch.WordTrace tailWord_5054862 prefixEnd_5054862 2595573848147507062878119 := by
  unfold tailWord_5054862
  simp only [CollatzResearch.WordTrace]
  refine ⟨23045745426638218817968855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122910642275403833695833893 23045745426638218817968855)
  ·
    refine ⟨34568618139957328226953283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23045745426638218817968855 34568618139957328226953283)
    ·
      refine ⟨51852927209935992340429925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34568618139957328226953283 51852927209935992340429925)
      ·
        refine ⟨9722423851862998563830611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51852927209935992340429925 9722423851862998563830611)
        ·
          refine ⟨14583635777794497845745917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9722423851862998563830611 14583635777794497845745917)
          ·
            refine ⟨5468863416672936692154719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14583635777794497845745917 5468863416672936692154719)
            ·
              refine ⟨8203295125009405038232079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5468863416672936692154719 8203295125009405038232079)
              ·
                refine ⟨12304942687514107557348119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8203295125009405038232079 12304942687514107557348119)
                ·
                  refine ⟨18457414031271161336022179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12304942687514107557348119 18457414031271161336022179)
                  ·
                    refine ⟨27686121046906742004033269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18457414031271161336022179 27686121046906742004033269)
                    ·
                      refine ⟨2595573848147507062878119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27686121046906742004033269 2595573848147507062878119)
                      ·
                        rfl

theorem cell23_5054862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_5054862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054862 prefixEnd_5054862 := by exact prefixLift 5054862
  have htrace : WordTrace (prefixWord ++ tailWord_5054862) baseStart_5054862 baseEnd_5054862 := by
    simpa [prefixWord, tailWord_5054862, baseEnd_5054862] using wordTrace_append hprefix tailTrace_5054862
  have hstable : (prefixWord ++ tailWord_5054862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054862).length < 2 ^ (prefixWord ++ tailWord_5054862).sum := by decide
  have hdescent : baseEnd_5054862 < baseStart_5054862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054870 : List Nat := [5, 3, 1, 2, 1, 1, 1, 4, 1, 1, 3]
def baseStart_5054870 : Nat := 118140960795 + 5054870 * 2 ^ 59
def prefixEnd_5054870 : Nat := 4983230072969 + 3 ^ 40 * 5054870 * 2
def baseEnd_5054870 : Nat := 2595577955992743031578083

theorem tailTrace_5054870 : CollatzResearch.WordTrace tailWord_5054870 prefixEnd_5054870 2595577955992743031578083 := by
  unfold tailWord_5054870
  simp only [CollatzResearch.WordTrace]
  refine ⟨11522890949817297994377629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122910836798051178606694709 11522890949817297994377629)
  ·
    refine ⟨4321084106181486747891611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11522890949817297994377629 4321084106181486747891611)
    ·
      refine ⟨6481626159272230121837417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4321084106181486747891611 6481626159272230121837417)
      ·
        refine ⟨4861219619454172591378063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6481626159272230121837417 4861219619454172591378063)
        ·
          refine ⟨7291829429181258887067095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4861219619454172591378063 7291829429181258887067095)
          ·
            refine ⟨10937744143771888330600643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7291829429181258887067095 10937744143771888330600643)
            ·
              refine ⟨16406616215657832495900965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10937744143771888330600643 16406616215657832495900965)
              ·
                refine ⟨3076240540435843592981431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16406616215657832495900965 3076240540435843592981431)
                ·
                  refine ⟨4614360810653765389472147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3076240540435843592981431 4614360810653765389472147)
                  ·
                    refine ⟨6921541215980648084208221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4614360810653765389472147 6921541215980648084208221)
                    ·
                      refine ⟨2595577955992743031578083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6921541215980648084208221 2595577955992743031578083)
                      ·
                        rfl

theorem cell23_5054870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_5054870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054870 prefixEnd_5054870 := by exact prefixLift 5054870
  have htrace : WordTrace (prefixWord ++ tailWord_5054870) baseStart_5054870 baseEnd_5054870 := by
    simpa [prefixWord, tailWord_5054870, baseEnd_5054870] using wordTrace_append hprefix tailTrace_5054870
  have hstable : (prefixWord ++ tailWord_5054870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054870).length < 2 ^ (prefixWord ++ tailWord_5054870).sum := by decide
  have hdescent : baseEnd_5054870 < baseStart_5054870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054885 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 5, 3, 2]
def baseStart_5054885 : Nat := 118140960795 + 5054885 * 2 ^ 59
def prefixEnd_5054885 : Nat := 4983230072969 + 3 ^ 40 * 5054885 * 2
def baseEnd_5054885 : Nat := 2595585658202560472890513

theorem tailTrace_5054885 : CollatzResearch.WordTrace tailWord_5054885 prefixEnd_5054885 2595585658202560472890513 := by
  unfold tailWord_5054885
  simp only [CollatzResearch.WordTrace]
  refine ⟨184366802292022425471838109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122911201528014950314558739 184366802292022425471838109)
  ·
    refine ⟨69137550859508409551939291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184366802292022425471838109 69137550859508409551939291)
    ·
      refine ⟨103706326289262614327908937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69137550859508409551939291 103706326289262614327908937)
      ·
        refine ⟨77779744716946960745931703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103706326289262614327908937 77779744716946960745931703)
        ·
          refine ⟨116669617075420441118897555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77779744716946960745931703 116669617075420441118897555)
          ·
            refine ⟨175004425613130661678346333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116669617075420441118897555 175004425613130661678346333)
            ·
              refine ⟨65626659604923998129379875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175004425613130661678346333 65626659604923998129379875)
              ·
                refine ⟨98439989407385997194069813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65626659604923998129379875 98439989407385997194069813)
                ·
                  refine ⟨9228749006942437236944045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98439989407385997194069813 9228749006942437236944045)
                  ·
                    refine ⟨3460780877603413963854017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9228749006942437236944045 3460780877603413963854017)
                    ·
                      refine ⟨2595585658202560472890513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3460780877603413963854017 2595585658202560472890513)
                      ·
                        rfl

theorem cell23_5054885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 3, 2].length) (baseStart_5054885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054885 prefixEnd_5054885 := by exact prefixLift 5054885
  have htrace : WordTrace (prefixWord ++ tailWord_5054885) baseStart_5054885 baseEnd_5054885 := by
    simpa [prefixWord, tailWord_5054885, baseEnd_5054885] using wordTrace_append hprefix tailTrace_5054885
  have hstable : (prefixWord ++ tailWord_5054885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054885).length < 2 ^ (prefixWord ++ tailWord_5054885).sum := by decide
  have hdescent : baseEnd_5054885 < baseStart_5054885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054898 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4]
def baseStart_5054898 : Nat := 118140960795 + 5054898 * 2 ^ 59
def prefixEnd_5054898 : Nat := 4983230072969 + 3 ^ 40 * 5054898 * 2
def baseEnd_5054898 : Nat := 2595592333451068922027953

theorem tailTrace_5054898 : CollatzResearch.WordTrace tailWord_5054898 prefixEnd_5054898 2595592333451068922027953 := by
  unfold tailWord_5054898
  simp only [CollatzResearch.WordTrace]
  refine ⟨46091819110243832173015337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122911517627316885794707565 46091819110243832173015337)
  ·
    refine ⟨34568864332682874129761503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46091819110243832173015337 34568864332682874129761503)
    ·
      refine ⟨51853296499024311194642255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34568864332682874129761503 51853296499024311194642255)
      ·
        refine ⟨77779944748536466791963383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51853296499024311194642255 77779944748536466791963383)
        ·
          refine ⟨116669917122804700187945075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77779944748536466791963383 116669917122804700187945075)
          ·
            refine ⟨175004875684207050281917613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116669917122804700187945075 175004875684207050281917613)
            ·
              refine ⟨65626828381577643855719105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175004875684207050281917613 65626828381577643855719105)
              ·
                refine ⟨49220121286183232891789329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65626828381577643855719105 49220121286183232891789329)
                ·
                  refine ⟨36915090964637424668841997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49220121286183232891789329 36915090964637424668841997)
                  ·
                    refine ⟨13843159111739034250815749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36915090964637424668841997 13843159111739034250815749)
                    ·
                      refine ⟨2595592333451068922027953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13843159111739034250815749 2595592333451068922027953)
                      ·
                        rfl

theorem cell23_5054898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_5054898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054898 prefixEnd_5054898 := by exact prefixLift 5054898
  have htrace : WordTrace (prefixWord ++ tailWord_5054898) baseStart_5054898 baseEnd_5054898 := by
    simpa [prefixWord, tailWord_5054898, baseEnd_5054898] using wordTrace_append hprefix tailTrace_5054898
  have hstable : (prefixWord ++ tailWord_5054898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054898).length < 2 ^ (prefixWord ++ tailWord_5054898).sum := by decide
  have hdescent : baseEnd_5054898 < baseStart_5054898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054919 : List Nat := [1, 1, 4, 1, 1, 4, 4, 1, 1, 3, 2]
def baseStart_5054919 : Nat := 118140960795 + 5054919 * 2 ^ 59
def prefixEnd_5054919 : Nat := 4983230072969 + 3 ^ 40 * 5054919 * 2
def baseEnd_5054919 : Nat := 2595603116544813339865357

theorem tailTrace_5054919 : CollatzResearch.WordTrace tailWord_5054919 prefixEnd_5054919 2595603116544813339865357 := by
  unfold tailWord_5054919
  simp only [CollatzResearch.WordTrace]
  refine ⟨184368042373899249278575811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122912028249266166185717207 184368042373899249278575811)
  ·
    refine ⟨276552063560848873917863717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184368042373899249278575811 276552063560848873917863717)
    ·
      refine ⟨51853511917659163859599447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 276552063560848873917863717 51853511917659163859599447)
      ·
        refine ⟨77780267876488745789399171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51853511917659163859599447 77780267876488745789399171)
        ·
          refine ⟨116670401814733118684098757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77780267876488745789399171 116670401814733118684098757)
          ·
            refine ⟨21875700340262459753268517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116670401814733118684098757 21875700340262459753268517)
            ·
              refine ⟨4101693813799211203737847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21875700340262459753268517 4101693813799211203737847)
              ·
                refine ⟨6152540720698816805606771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4101693813799211203737847 6152540720698816805606771)
                ·
                  refine ⟨9228811081048225208410157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6152540720698816805606771 9228811081048225208410157)
                  ·
                    refine ⟨3460804155393084453153809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9228811081048225208410157 3460804155393084453153809)
                    ·
                      refine ⟨2595603116544813339865357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3460804155393084453153809 2595603116544813339865357)
                      ·
                        rfl

theorem cell23_5054919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 1, 3, 2].length) (baseStart_5054919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054919 prefixEnd_5054919 := by exact prefixLift 5054919
  have htrace : WordTrace (prefixWord ++ tailWord_5054919) baseStart_5054919 baseEnd_5054919 := by
    simpa [prefixWord, tailWord_5054919, baseEnd_5054919] using wordTrace_append hprefix tailTrace_5054919
  have hstable : (prefixWord ++ tailWord_5054919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054919).length < 2 ^ (prefixWord ++ tailWord_5054919).sum := by decide
  have hdescent : baseEnd_5054919 < baseStart_5054919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054968 : List Nat := [2, 1, 2, 1, 1, 4, 1, 3, 1, 7]
def baseStart_5054968 : Nat := 118140960795 + 5054968 * 2 ^ 59
def prefixEnd_5054968 : Nat := 4983230072969 + 3 ^ 40 * 5054968 * 2
def baseEnd_5054968 : Nat := 865209425698961216050877

theorem tailTrace_5054968 : CollatzResearch.WordTrace tailWord_5054968 prefixEnd_5054968 865209425698961216050877 := by
  unfold tailWord_5054968
  simp only [CollatzResearch.WordTrace]
  refine ⟨92184914775360865323554779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122913219700481153764739705 92184914775360865323554779)
  ·
    refine ⟨138277372163041297985332169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92184914775360865323554779 138277372163041297985332169)
    ·
      refine ⟨103708029122280973488999127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138277372163041297985332169 103708029122280973488999127)
      ·
        refine ⟨155562043683421460233498691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103708029122280973488999127 155562043683421460233498691)
        ·
          refine ⟨233343065525132190350248037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155562043683421460233498691 233343065525132190350248037)
          ·
            refine ⟨43751824785962285690671507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 233343065525132190350248037 43751824785962285690671507)
            ·
              refine ⟨65627737178943428536007261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43751824785962285690671507 65627737178943428536007261)
              ·
                refine ⟨24610401442103785701002723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65627737178943428536007261 24610401442103785701002723)
                ·
                  refine ⟨36915602163155678551504085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24610401442103785701002723 36915602163155678551504085)
                  ·
                    refine ⟨865209425698961216050877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36915602163155678551504085 865209425698961216050877)
                    ·
                      rfl

theorem cell23_5054968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 1, 7].length) (baseStart_5054968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054968 prefixEnd_5054968 := by exact prefixLift 5054968
  have htrace : WordTrace (prefixWord ++ tailWord_5054968) baseStart_5054968 baseEnd_5054968 := by
    simpa [prefixWord, tailWord_5054968, baseEnd_5054968] using wordTrace_append hprefix tailTrace_5054968
  have hstable : (prefixWord ++ tailWord_5054968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054968).length < 2 ^ (prefixWord ++ tailWord_5054968).sum := by decide
  have hdescent : baseEnd_5054968 < baseStart_5054968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5054989 : List Nat := [1, 7, 1, 1, 1, 1, 3, 1, 7]
def baseStart_5054989 : Nat := 118140960795 + 5054989 * 2 ^ 59
def prefixEnd_5054989 : Nat := 4983230072969 + 3 ^ 40 * 5054989 * 2
def baseEnd_5054989 : Nat := 288404340021180896221115

theorem tailTrace_5054989 : CollatzResearch.WordTrace tailWord_5054989 prefixEnd_5054989 288404340021180896221115 := by
  unfold tailWord_5054989
  simp only [CollatzResearch.WordTrace]
  refine ⟨184370595483645651233624021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122913730322430434155749347 184370595483645651233624021)
  ·
    refine ⟨4321185831647944950788063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 184370595483645651233624021 4321185831647944950788063)
    ·
      refine ⟨6481778747471917426182095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4321185831647944950788063 6481778747471917426182095)
      ·
        refine ⟨9722668121207876139273143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6481778747471917426182095 9722668121207876139273143)
        ·
          refine ⟨14584002181811814208909715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9722668121207876139273143 14584002181811814208909715)
          ·
            refine ⟨21876003272717721313364573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14584002181811814208909715 21876003272717721313364573)
            ·
              refine ⟨8203501227269145492511715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21876003272717721313364573 8203501227269145492511715)
              ·
                refine ⟨12305251840903718238767573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8203501227269145492511715 12305251840903718238767573)
                ·
                  refine ⟨288404340021180896221115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12305251840903718238767573 288404340021180896221115)
                  ·
                    rfl

theorem cell23_5054989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_5054989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5054989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5054989 prefixEnd_5054989 := by exact prefixLift 5054989
  have htrace : WordTrace (prefixWord ++ tailWord_5054989) baseStart_5054989 baseEnd_5054989 := by
    simpa [prefixWord, tailWord_5054989, baseEnd_5054989] using wordTrace_append hprefix tailTrace_5054989
  have hstable : (prefixWord ++ tailWord_5054989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5054989).length < 2 ^ (prefixWord ++ tailWord_5054989).sum := by decide
  have hdescent : baseEnd_5054989 < baseStart_5054989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5054989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055025 : List Nat := [1, 2, 2, 3, 1, 1, 2, 3, 1, 4, 3]
def baseStart_5055025 : Nat := 118140960795 + 5055025 * 2 ^ 59
def prefixEnd_5055025 : Nat := 4983230072969 + 3 ^ 40 * 5055025 * 2
def baseEnd_5055025 : Nat := 2595657545494189925139869

theorem tailTrace_5055025 : CollatzResearch.WordTrace tailWord_5055025 prefixEnd_5055025 2595657545494189925139869 := by
  unfold tailWord_5055025
  simp only [CollatzResearch.WordTrace]
  refine ⟨184371908511515229381934529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122914605674343486254623019 184371908511515229381934529)
  ·
    refine ⟨138278931383636422036450897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184371908511515229381934529 138278931383636422036450897)
    ·
      refine ⟨103709198537727316527338173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138278931383636422036450897 103709198537727316527338173)
      ·
        refine ⟨38890949451647743697751815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103709198537727316527338173 38890949451647743697751815)
        ·
          refine ⟨58336424177471615546627723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38890949451647743697751815 58336424177471615546627723)
          ·
            refine ⟨87504636266207423319941585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58336424177471615546627723 87504636266207423319941585)
            ·
              refine ⟨65628477199655567489956189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87504636266207423319941585 65628477199655567489956189)
              ·
                refine ⟨24610678949870837808733571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65628477199655567489956189 24610678949870837808733571)
                ·
                  refine ⟨36916018424806256713100357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24610678949870837808733571 36916018424806256713100357)
                  ·
                    refine ⟨6921753454651173133706317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36916018424806256713100357 6921753454651173133706317)
                    ·
                      refine ⟨2595657545494189925139869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6921753454651173133706317 2595657545494189925139869)
                      ·
                        rfl

theorem cell23_5055025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_5055025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055025 prefixEnd_5055025 := by exact prefixLift 5055025
  have htrace : WordTrace (prefixWord ++ tailWord_5055025) baseStart_5055025 baseEnd_5055025 := by
    simpa [prefixWord, tailWord_5055025, baseEnd_5055025] using wordTrace_append hprefix tailTrace_5055025
  have hstable : (prefixWord ++ tailWord_5055025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055025).length < 2 ^ (prefixWord ++ tailWord_5055025).sum := by decide
  have hdescent : baseEnd_5055025 < baseStart_5055025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055045 : List Nat := [1, 3, 1, 1, 1, 5, 1, 4, 6]
def baseStart_5055045 : Nat := 118140960795 + 5055045 * 2 ^ 59
def prefixEnd_5055045 : Nat := 4983230072969 + 3 ^ 40 * 5055045 * 2
def baseEnd_5055045 : Nat := 288407535011919982987753

theorem tailTrace_5055045 : CollatzResearch.WordTrace tailWord_5055045 prefixEnd_5055045 288407535011919982987753 := by
  unfold tailWord_5055045
  simp only [CollatzResearch.WordTrace]
  refine ⟨184372637971442772797662589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122915091980961848531775059 184372637971442772797662589)
  ·
    refine ⟨69139739239291039799123471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184372637971442772797662589 69139739239291039799123471)
    ·
      refine ⟨103709608858936559698685207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69139739239291039799123471 103709608858936559698685207)
      ·
        refine ⟨155564413288404839548027811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103709608858936559698685207 155564413288404839548027811)
        ·
          refine ⟨233346619932607259322041717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155564413288404839548027811 233346619932607259322041717)
          ·
            refine ⟨21876245618681930561441411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 233346619932607259322041717 21876245618681930561441411)
            ·
              refine ⟨32814368428022895842162117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21876245618681930561441411 32814368428022895842162117)
              ·
                refine ⟨6152694080254292970405397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32814368428022895842162117 6152694080254292970405397)
                ·
                  refine ⟨288407535011919982987753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6152694080254292970405397 288407535011919982987753)
                  ·
                    rfl

theorem cell23_5055045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 6].length) (baseStart_5055045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055045 prefixEnd_5055045 := by exact prefixLift 5055045
  have htrace : WordTrace (prefixWord ++ tailWord_5055045) baseStart_5055045 baseEnd_5055045 := by
    simpa [prefixWord, tailWord_5055045, baseEnd_5055045] using wordTrace_append hprefix tailTrace_5055045
  have hstable : (prefixWord ++ tailWord_5055045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055045).length < 2 ^ (prefixWord ++ tailWord_5055045).sum := by decide
  have hdescent : baseEnd_5055045 < baseStart_5055045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055070 : List Nat := [4, 4, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_5055070 : Nat := 118140960795 + 5055070 * 2 ^ 59
def prefixEnd_5055070 : Nat := 4983230072969 + 3 ^ 40 * 5055070 * 2
def baseEnd_5055070 : Nat := 865226884041214083025721

theorem tailTrace_5055070 : CollatzResearch.WordTrace tailWord_5055070 prefixEnd_5055070 865226884041214083025721 := by
  unfold tailWord_5055070
  simp only [CollatzResearch.WordTrace]
  refine ⟨23046693724544025258415333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122915699864234801378215109 23046693724544025258415333)
  ·
    refine ⟨4321255073352004735952875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23046693724544025258415333 4321255073352004735952875)
    ·
      refine ⟨6481882610028007103929313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4321255073352004735952875 6481882610028007103929313)
      ·
        refine ⟨4861411957521005327946985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6481882610028007103929313 4861411957521005327946985)
        ·
          refine ⟨3646058968140753995960239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4861411957521005327946985 3646058968140753995960239)
          ·
            refine ⟨5469088452211130993940359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3646058968140753995960239 5469088452211130993940359)
            ·
              refine ⟨8203632678316696490910539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5469088452211130993940359 8203632678316696490910539)
              ·
                refine ⟨12305449017475044736365809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8203632678316696490910539 12305449017475044736365809)
                ·
                  refine ⟨9229086763106283552274357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12305449017475044736365809 9229086763106283552274357)
                  ·
                    refine ⟨865226884041214083025721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9229086763106283552274357 865226884041214083025721)
                    ·
                      rfl

theorem cell23_5055070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_5055070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055070 prefixEnd_5055070 := by exact prefixLift 5055070
  have htrace : WordTrace (prefixWord ++ tailWord_5055070) baseStart_5055070 baseEnd_5055070 := by
    simpa [prefixWord, tailWord_5055070, baseEnd_5055070] using wordTrace_append hprefix tailTrace_5055070
  have hstable : (prefixWord ++ tailWord_5055070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055070).length < 2 ^ (prefixWord ++ tailWord_5055070).sum := by decide
  have hdescent : baseEnd_5055070 < baseStart_5055070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055072 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 5, 1, 3]
def baseStart_5055072 : Nat := 118140960795 + 5055072 * 2 ^ 59
def prefixEnd_5055072 : Nat := 4983230072969 + 3 ^ 40 * 5055072 * 2
def baseEnd_5055072 : Nat := 2595681679084951241252153

theorem tailTrace_5055072 : CollatzResearch.WordTrace tailWord_5055072 prefixEnd_5055072 2595681679084951241252153 := by
  unfold tailWord_5055072
  simp only [CollatzResearch.WordTrace]
  refine ⟨92186811371172478204447735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122915748494896637605930313 92186811371172478204447735)
  ·
    refine ⟨138280217056758717306671603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92186811371172478204447735 138280217056758717306671603)
    ·
      refine ⟨207420325585138075960007405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138280217056758717306671603 207420325585138075960007405)
      ·
        refine ⟨77782622094426778485002777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207420325585138075960007405 77782622094426778485002777)
        ·
          refine ⟨58336966570820083863752083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77782622094426778485002777 58336966570820083863752083)
          ·
            refine ⟨87505449856230125795628125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58336966570820083863752083 87505449856230125795628125)
            ·
              refine ⟨32814543696086297173360547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87505449856230125795628125 32814543696086297173360547)
              ·
                refine ⟨49221815544129445760040821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32814543696086297173360547 49221815544129445760040821)
                ·
                  refine ⟨4614545207262135540003827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49221815544129445760040821 4614545207262135540003827)
                  ·
                    refine ⟨6921817810893203310005741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4614545207262135540003827 6921817810893203310005741)
                    ·
                      refine ⟨2595681679084951241252153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6921817810893203310005741 2595681679084951241252153)
                      ·
                        rfl

theorem cell23_5055072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_5055072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055072 prefixEnd_5055072 := by exact prefixLift 5055072
  have htrace : WordTrace (prefixWord ++ tailWord_5055072) baseStart_5055072 baseEnd_5055072 := by
    simpa [prefixWord, tailWord_5055072, baseEnd_5055072] using wordTrace_append hprefix tailTrace_5055072
  have hstable : (prefixWord ++ tailWord_5055072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055072).length < 2 ^ (prefixWord ++ tailWord_5055072).sum := by decide
  have hdescent : baseEnd_5055072 < baseStart_5055072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055075 : List Nat := [1, 1, 1, 5, 1, 2, 1, 3, 3, 5]
def baseStart_5055075 : Nat := 118140960795 + 5055075 * 2 ^ 59
def prefixEnd_5055075 : Nat := 4983230072969 + 3 ^ 40 * 5055075 * 2
def baseEnd_5055075 : Nat := 865227739842304909838213

theorem tailTrace_5055075 : CollatzResearch.WordTrace tailWord_5055075 prefixEnd_5055075 865227739842304909838213 := by
  unfold tailWord_5055075
  simp only [CollatzResearch.WordTrace]
  refine ⟨184373732161334087921254679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122915821440889391947503119 184373732161334087921254679)
  ·
    refine ⟨276560598242001131881882019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184373732161334087921254679 276560598242001131881882019)
    ·
      refine ⟨414840897363001697822823029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276560598242001131881882019 414840897363001697822823029)
      ·
        refine ⟨38891334127781409170889659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 414840897363001697822823029 38891334127781409170889659)
        ·
          refine ⟨58337001191672113756334489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38891334127781409170889659 58337001191672113756334489)
          ·
            refine ⟨43752750893754085317250867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58337001191672113756334489 43752750893754085317250867)
            ·
              refine ⟨65629126340631127975876301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43752750893754085317250867 65629126340631127975876301)
              ·
                refine ⟨24610922377736672990953613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65629126340631127975876301 24610922377736672990953613)
                ·
                  refine ⟨9229095891651252371607605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24610922377736672990953613 9229095891651252371607605)
                  ·
                    refine ⟨865227739842304909838213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9229095891651252371607605 865227739842304909838213)
                    ·
                      rfl

theorem cell23_5055075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 5].length) (baseStart_5055075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055075 prefixEnd_5055075 := by exact prefixLift 5055075
  have htrace : WordTrace (prefixWord ++ tailWord_5055075) baseStart_5055075 baseEnd_5055075 := by
    simpa [prefixWord, tailWord_5055075, baseEnd_5055075] using wordTrace_append hprefix tailTrace_5055075
  have hstable : (prefixWord ++ tailWord_5055075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055075).length < 2 ^ (prefixWord ++ tailWord_5055075).sum := by decide
  have hdescent : baseEnd_5055075 < baseStart_5055075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055115 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 2, 6, 3]
def baseStart_5055115 : Nat := 118140960795 + 5055115 * 2 ^ 59
def prefixEnd_5055115 : Nat := 4983230072969 + 3 ^ 40 * 5055115 * 2
def baseEnd_5055115 : Nat := 2595703758753094573014455

theorem tailTrace_5055115 : CollatzResearch.WordTrace tailWord_5055115 prefixEnd_5055115 2595703758753094573014455 := by
  unfold tailWord_5055115
  simp only [CollatzResearch.WordTrace]
  refine ⟨184375191081189174752710799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122916794054126116501807199 184375191081189174752710799)
  ·
    refine ⟨276562786621783762129066199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184375191081189174752710799 276562786621783762129066199)
    ·
      refine ⟨414844179932675643193599299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276562786621783762129066199 414844179932675643193599299)
      ·
        refine ⟨622266269899013464790398949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414844179932675643193599299 622266269899013464790398949)
        ·
          refine ⟨116674925606065024648199803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 622266269899013464790398949 116674925606065024648199803)
          ·
            refine ⟨175012388409097536972299705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116674925606065024648199803 175012388409097536972299705)
            ·
              refine ⟨131259291306823152729224779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175012388409097536972299705 131259291306823152729224779)
              ·
                refine ⟨196888936960234729093837169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131259291306823152729224779 196888936960234729093837169)
                ·
                  refine ⟨147666702720176046820377877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 196888936960234729093837169 147666702720176046820377877)
                  ·
                    refine ⟨6921876690008252194705213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 147666702720176046820377877 6921876690008252194705213)
                    ·
                      refine ⟨2595703758753094573014455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6921876690008252194705213 2595703758753094573014455)
                      ·
                        rfl

theorem cell23_5055115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 6, 3].length) (baseStart_5055115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055115 prefixEnd_5055115 := by exact prefixLift 5055115
  have htrace : WordTrace (prefixWord ++ tailWord_5055115) baseStart_5055115 baseEnd_5055115 := by
    simpa [prefixWord, tailWord_5055115, baseEnd_5055115] using wordTrace_append hprefix tailTrace_5055115
  have hstable : (prefixWord ++ tailWord_5055115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055115).length < 2 ^ (prefixWord ++ tailWord_5055115).sum := by decide
  have hdescent : baseEnd_5055115 < baseStart_5055115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055129 : List Nat := [1, 2, 1, 2, 1, 2, 3, 4, 3, 2, 2]
def baseStart_5055129 : Nat := 118140960795 + 5055129 * 2 ^ 59
def prefixEnd_5055129 : Nat := 4983230072969 + 3 ^ 40 * 5055129 * 2
def baseEnd_5055129 : Nat := 2595710947482257518239391

theorem tailTrace_5055129 : CollatzResearch.WordTrace tailWord_5055129 prefixEnd_5055129 2595710947482257518239391 := by
  unfold tailWord_5055129
  simp only [CollatzResearch.WordTrace]
  refine ⟨184375701703138455143720441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122917134468758970095813627 184375701703138455143720441)
  ·
    refine ⟨138281776277353841357790331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184375701703138455143720441 138281776277353841357790331)
    ·
      refine ⟨207422664416030762036685497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138281776277353841357790331 207422664416030762036685497)
      ·
        refine ⟨155566998312023071527514123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207422664416030762036685497 155566998312023071527514123)
        ·
          refine ⟨233350497468034607291271185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155566998312023071527514123 233350497468034607291271185)
          ·
            refine ⟨175012873101025955468453389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233350497468034607291271185 175012873101025955468453389)
            ·
              refine ⟨65629827412884733300670021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175012873101025955468453389 65629827412884733300670021)
              ·
                refine ⟨12305592639915887493875629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65629827412884733300670021 12305592639915887493875629)
                ·
                  refine ⟨4614597239968457810203361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12305592639915887493875629 4614597239968457810203361)
                  ·
                    refine ⟨3460947929976343357652521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4614597239968457810203361 3460947929976343357652521)
                    ·
                      refine ⟨2595710947482257518239391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3460947929976343357652521 2595710947482257518239391)
                      ·
                        rfl

theorem cell23_5055129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 3, 2, 2].length) (baseStart_5055129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055129 prefixEnd_5055129 := by exact prefixLift 5055129
  have htrace : WordTrace (prefixWord ++ tailWord_5055129) baseStart_5055129 baseEnd_5055129 := by
    simpa [prefixWord, tailWord_5055129, baseEnd_5055129] using wordTrace_append hprefix tailTrace_5055129
  have hstable : (prefixWord ++ tailWord_5055129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055129).length < 2 ^ (prefixWord ++ tailWord_5055129).sum := by decide
  have hdescent : baseEnd_5055129 < baseStart_5055129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055149 : List Nat := [1, 5, 2, 1, 1, 3, 2, 1, 1, 1, 5]
def baseStart_5055149 : Nat := 118140960795 + 5055149 * 2 ^ 59
def prefixEnd_5055149 : Nat := 4983230072969 + 3 ^ 40 * 5055149 * 2
def baseEnd_5055149 : Nat := 2595721217095347439989299

theorem tailTrace_5055149 : CollatzResearch.WordTrace tailWord_5055149 prefixEnd_5055149 2595721217095347439989299 := by
  unfold tailWord_5055149
  simp only [CollatzResearch.WordTrace]
  refine ⟨184376431163065998559448501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122917620775377332372965667 184376431163065998559448501)
  ·
    refine ⟨17285290421537437364948297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 184376431163065998559448501 17285290421537437364948297)
    ·
      refine ⟨12963967816153078023711223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17285290421537437364948297 12963967816153078023711223)
      ·
        refine ⟨19445951724229617035566835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12963967816153078023711223 19445951724229617035566835)
        ·
          refine ⟨29168927586344425553350253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19445951724229617035566835 29168927586344425553350253)
          ·
            refine ⟨10938347844879159582506345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29168927586344425553350253 10938347844879159582506345)
            ·
              refine ⟨8203760883659369686879759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10938347844879159582506345 8203760883659369686879759)
              ·
                refine ⟨12305641325489054530319639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8203760883659369686879759 12305641325489054530319639)
                ·
                  refine ⟨18458461988233581795479459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12305641325489054530319639 18458461988233581795479459)
                  ·
                    refine ⟨27687692982350372693219189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18458461988233581795479459 27687692982350372693219189)
                    ·
                      refine ⟨2595721217095347439989299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27687692982350372693219189 2595721217095347439989299)
                      ·
                        rfl

theorem cell23_5055149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_5055149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055149 prefixEnd_5055149 := by exact prefixLift 5055149
  have htrace : WordTrace (prefixWord ++ tailWord_5055149) baseStart_5055149 baseEnd_5055149 := by
    simpa [prefixWord, tailWord_5055149, baseEnd_5055149] using wordTrace_append hprefix tailTrace_5055149
  have hstable : (prefixWord ++ tailWord_5055149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055149).length < 2 ^ (prefixWord ++ tailWord_5055149).sum := by decide
  have hdescent : baseEnd_5055149 < baseStart_5055149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055175 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 5]
def baseStart_5055175 : Nat := 118140960795 + 5055175 * 2 ^ 59
def prefixEnd_5055175 : Nat := 4983230072969 + 3 ^ 40 * 5055175 * 2
def baseEnd_5055175 : Nat := 2595734567592364338264179

theorem tailTrace_5055175 : CollatzResearch.WordTrace tailWord_5055175 prefixEnd_5055175 2595734567592364338264179 := by
  unfold tailWord_5055175
  simp only [CollatzResearch.WordTrace]
  refine ⟨184377379460971804999894979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122918252973981203333263319 184377379460971804999894979)
  ·
    refine ⟨276566069191457707499842469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184377379460971804999894979 276566069191457707499842469)
    ·
      refine ⟨51856137973398320156220463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 276566069191457707499842469 51856137973398320156220463)
      ·
        refine ⟨77784206960097480234330695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51856137973398320156220463 77784206960097480234330695)
        ·
          refine ⟨116676310440146220351496043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77784206960097480234330695 116676310440146220351496043)
          ·
            refine ⟨175014465660219330527244065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116676310440146220351496043 175014465660219330527244065)
            ·
              refine ⟨131260849245164497895433049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175014465660219330527244065 131260849245164497895433049)
              ·
                refine ⟨98445636933873373421574787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131260849245164497895433049 98445636933873373421574787)
                ·
                  refine ⟨147668455400810060132362181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98445636933873373421574787 147668455400810060132362181)
                  ·
                    refine ⟨27687835387651886274817909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 147668455400810060132362181 27687835387651886274817909)
                    ·
                      refine ⟨2595734567592364338264179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27687835387651886274817909 2595734567592364338264179)
                      ·
                        rfl

theorem cell23_5055175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_5055175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055175 prefixEnd_5055175 := by exact prefixLift 5055175
  have htrace : WordTrace (prefixWord ++ tailWord_5055175) baseStart_5055175 baseEnd_5055175 := by
    simpa [prefixWord, tailWord_5055175, baseEnd_5055175] using wordTrace_append hprefix tailTrace_5055175
  have hstable : (prefixWord ++ tailWord_5055175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055175).length < 2 ^ (prefixWord ++ tailWord_5055175).sum := by decide
  have hdescent : baseEnd_5055175 < baseStart_5055175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055196 : List Nat := [2, 2, 5, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_5055196 : Nat := 118140960795 + 5055196 * 2 ^ 59
def prefixEnd_5055196 : Nat := 4983230072969 + 3 ^ 40 * 5055196 * 2
def baseEnd_5055196 : Nat := 2595745350686108756101583

theorem tailTrace_5055196 : CollatzResearch.WordTrace tailWord_5055196 prefixEnd_5055196 2595745350686108756101583 := by
  unfold tailWord_5055196
  simp only [CollatzResearch.WordTrace]
  refine ⟨92189072696947862793204721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122918763595930483724272961 92189072696947862793204721)
  ·
    refine ⟨69141804522710897094903541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92189072696947862793204721 69141804522710897094903541)
    ·
      refine ⟨6482044174004146602647207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69141804522710897094903541 6482044174004146602647207)
      ·
        refine ⟨9723066261006219903970811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6482044174004146602647207 9723066261006219903970811)
        ·
          refine ⟨14584599391509329855956217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9723066261006219903970811 14584599391509329855956217)
          ·
            refine ⟨10938449543631997391967163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14584599391509329855956217 10938449543631997391967163)
            ·
              refine ⟨16407674315447996087950745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10938449543631997391967163 16407674315447996087950745)
              ·
                refine ⟨12305755736585997065963059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16407674315447996087950745 12305755736585997065963059)
                ·
                  refine ⟨18458633604878995598944589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12305755736585997065963059 18458633604878995598944589)
                  ·
                    refine ⟨6921987601829623349604221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18458633604878995598944589 6921987601829623349604221)
                    ·
                      refine ⟨2595745350686108756101583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6921987601829623349604221 2595745350686108756101583)
                      ·
                        rfl

theorem cell23_5055196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_5055196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055196 prefixEnd_5055196 := by exact prefixLift 5055196
  have htrace : WordTrace (prefixWord ++ tailWord_5055196) baseStart_5055196 baseEnd_5055196 := by
    simpa [prefixWord, tailWord_5055196, baseEnd_5055196] using wordTrace_append hprefix tailTrace_5055196
  have hstable : (prefixWord ++ tailWord_5055196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055196).length < 2 ^ (prefixWord ++ tailWord_5055196).sum := by decide
  have hdescent : baseEnd_5055196 < baseStart_5055196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055225 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 11]
def baseStart_5055225 : Nat := 118140960795 + 5055225 * 2 ^ 59
def prefixEnd_5055225 : Nat := 4983230072969 + 3 ^ 40 * 5055225 * 2
def baseEnd_5055225 : Nat := 288417804625009904737661

theorem tailTrace_5055225 : CollatzResearch.WordTrace tailWord_5055225 prefixEnd_5055225 288417804625009904737661 := by
  unfold tailWord_5055225
  simp only [CollatzResearch.WordTrace]
  refine ⟨184379203110790663539215129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122919468740527109026143419 184379203110790663539215129)
  ·
    refine ⟨138284402333092997654411347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184379203110790663539215129 138284402333092997654411347)
    ·
      refine ⟨207426603499639496481617021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138284402333092997654411347 207426603499639496481617021)
      ·
        refine ⟨77784976312364811180606383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207426603499639496481617021 77784976312364811180606383)
        ·
          refine ⟨116677464468547216770909575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77784976312364811180606383 116677464468547216770909575)
          ·
            refine ⟨175016196702820825156364363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116677464468547216770909575 175016196702820825156364363)
            ·
              refine ⟨262524295054231237734546545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175016196702820825156364363 262524295054231237734546545)
              ·
                refine ⟨196893221290673428300909909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262524295054231237734546545 196893221290673428300909909)
                ·
                  refine ⟨288417804625009904737661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 196893221290673428300909909 288417804625009904737661)
                  ·
                    rfl

theorem cell23_5055225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 11].length) (baseStart_5055225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055225 prefixEnd_5055225 := by exact prefixLift 5055225
  have htrace : WordTrace (prefixWord ++ tailWord_5055225) baseStart_5055225 baseEnd_5055225 := by
    simpa [prefixWord, tailWord_5055225, baseEnd_5055225] using wordTrace_append hprefix tailTrace_5055225
  have hstable : (prefixWord ++ tailWord_5055225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055225).length < 2 ^ (prefixWord ++ tailWord_5055225).sum := by decide
  have hdescent : baseEnd_5055225 < baseStart_5055225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055236 : List Nat := [2, 3, 2, 2, 1, 1, 4, 1, 1, 4, 2]
def baseStart_5055236 : Nat := 118140960795 + 5055236 * 2 ^ 59
def prefixEnd_5055236 : Nat := 4983230072969 + 3 ^ 40 * 5055236 * 2
def baseEnd_5055236 : Nat := 2595765889912288599601399

theorem tailTrace_5055236 : CollatzResearch.WordTrace tailWord_5055236 prefixEnd_5055236 2595765889912288599601399 := by
  unfold tailWord_5055236
  simp only [CollatzResearch.WordTrace]
  refine ⟨92189802156875406208932781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122919736209167208278577041 92189802156875406208932781)
  ·
    refine ⟨34571175808828277328349793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92189802156875406208932781 34571175808828277328349793)
    ·
      refine ⟨25928381856621207996262345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34571175808828277328349793 25928381856621207996262345)
      ·
        refine ⟨19446286392465905997196759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25928381856621207996262345 19446286392465905997196759)
        ·
          refine ⟨29169429588698858995795139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19446286392465905997196759 29169429588698858995795139)
          ·
            refine ⟨43754144383048288493692709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29169429588698858995795139 43754144383048288493692709)
            ·
              refine ⟨8203902071821554092567383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43754144383048288493692709 8203902071821554092567383)
              ·
                refine ⟨12305853107732331138851075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8203902071821554092567383 12305853107732331138851075)
                ·
                  refine ⟨18458779661598496708276613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12305853107732331138851075 18458779661598496708276613)
                  ·
                    refine ⟨3461021186549718132801865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18458779661598496708276613 3461021186549718132801865)
                    ·
                      refine ⟨2595765889912288599601399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3461021186549718132801865 2595765889912288599601399)
                      ·
                        rfl

theorem cell23_5055236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_5055236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055236 prefixEnd_5055236 := by exact prefixLift 5055236
  have htrace : WordTrace (prefixWord ++ tailWord_5055236) baseStart_5055236 baseEnd_5055236 := by
    simpa [prefixWord, tailWord_5055236, baseEnd_5055236] using wordTrace_append hprefix tailTrace_5055236
  have hstable : (prefixWord ++ tailWord_5055236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055236).length < 2 ^ (prefixWord ++ tailWord_5055236).sum := by decide
  have hdescent : baseEnd_5055236 < baseStart_5055236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055242 : List Nat := [3, 1, 2, 2, 1, 2, 3, 2, 7]
def baseStart_5055242 : Nat := 118140960795 + 5055242 * 2 ^ 59
def prefixEnd_5055242 : Nat := 4983230072969 + 3 ^ 40 * 5055242 * 2
def baseEnd_5055242 : Nat := 288418774532912841791819

theorem tailTrace_5055242 : CollatzResearch.WordTrace tailWord_5055242 prefixEnd_5055242 288418774532912841791819 := by
  unfold tailWord_5055242
  simp only [CollatzResearch.WordTrace]
  refine ⟨46094955787932268860645995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122919882101152716961722653 46094955787932268860645995)
  ·
    refine ⟨69142433681898403290968993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46094955787932268860645995 69142433681898403290968993)
    ·
      refine ⟨51856825261423802468226745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69142433681898403290968993 51856825261423802468226745)
      ·
        refine ⟨38892618946067851851170059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51856825261423802468226745 38892618946067851851170059)
        ·
          refine ⟨58338928419101777776755089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38892618946067851851170059 58338928419101777776755089)
          ·
            refine ⟨43754196314326333332566317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58338928419101777776755089 43754196314326333332566317)
            ·
              refine ⟨16407823617872374999712369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43754196314326333332566317 16407823617872374999712369)
              ·
                refine ⟨12305867713404281249784277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16407823617872374999712369 12305867713404281249784277)
                ·
                  refine ⟨288418774532912841791819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12305867713404281249784277 288418774532912841791819)
                  ·
                    rfl

theorem cell23_5055242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 7].length) (baseStart_5055242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055242 prefixEnd_5055242 := by exact prefixLift 5055242
  have htrace : WordTrace (prefixWord ++ tailWord_5055242) baseStart_5055242 baseEnd_5055242 := by
    simpa [prefixWord, tailWord_5055242, baseEnd_5055242] using wordTrace_append hprefix tailTrace_5055242
  have hstable : (prefixWord ++ tailWord_5055242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055242).length < 2 ^ (prefixWord ++ tailWord_5055242).sum := by decide
  have hdescent : baseEnd_5055242 < baseStart_5055242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055282 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7]
def baseStart_5055282 : Nat := 118140960795 + 5055282 * 2 ^ 59
def prefixEnd_5055282 : Nat := 4983230072969 + 3 ^ 40 * 5055282 * 2
def baseEnd_5055282 : Nat := 2595789510022395419626187

theorem tailTrace_5055282 : CollatzResearch.WordTrace tailWord_5055282 prefixEnd_5055282 2595789510022395419626187 := by
  unfold tailWord_5055282
  simp only [CollatzResearch.WordTrace]
  refine ⟨46095320517896040568510025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122920854714389441516026733 46095320517896040568510025)
  ·
    refine ⟨34571490388422030426382519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46095320517896040568510025 34571490388422030426382519)
    ·
      refine ⟨51857235582633045639573779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34571490388422030426382519 51857235582633045639573779)
      ·
        refine ⟨77785853373949568459360669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51857235582633045639573779 77785853373949568459360669)
        ·
          refine ⟨29169695015231088172260251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77785853373949568459360669 29169695015231088172260251)
          ·
            refine ⟨43754542522846632258390377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29169695015231088172260251 43754542522846632258390377)
            ·
              refine ⟨32815906892134974193792783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43754542522846632258390377 32815906892134974193792783)
              ·
                refine ⟨49223860338202461290689175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32815906892134974193792783 49223860338202461290689175)
                ·
                  refine ⟨73835790507303691936033763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49223860338202461290689175 73835790507303691936033763)
                  ·
                    refine ⟨110753685760955537904050645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73835790507303691936033763 110753685760955537904050645)
                    ·
                      refine ⟨2595789510022395419626187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 110753685760955537904050645 2595789510022395419626187)
                      ·
                        rfl

theorem cell23_5055282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_5055282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055282 prefixEnd_5055282 := by exact prefixLift 5055282
  have htrace : WordTrace (prefixWord ++ tailWord_5055282) baseStart_5055282 baseEnd_5055282 := by
    simpa [prefixWord, tailWord_5055282, baseEnd_5055282] using wordTrace_append hprefix tailTrace_5055282
  have hstable : (prefixWord ++ tailWord_5055282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055282).length < 2 ^ (prefixWord ++ tailWord_5055282).sum := by decide
  have hdescent : baseEnd_5055282 < baseStart_5055282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055336 : List Nat := [2, 1, 4, 2, 1, 2, 3, 1, 3, 4]
def baseStart_5055336 : Nat := 118140960795 + 5055336 * 2 ^ 59
def prefixEnd_5055336 : Nat := 4983230072969 + 3 ^ 40 * 5055336 * 2
def baseEnd_5055336 : Nat := 865272412659246069450313

theorem tailTrace_5055336 : CollatzResearch.WordTrace tailWord_5055336 prefixEnd_5055336 865272412659246069450313 := by
  unfold tailWord_5055336
  simp only [CollatzResearch.WordTrace]
  refine ⟨92191625806694264748252931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122922167742259019664337241 92191625806694264748252931)
  ·
    refine ⟨138287438710041397122379397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92191625806694264748252931 138287438710041397122379397)
    ·
      refine ⟨25928894758132761960446137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138287438710041397122379397 25928894758132761960446137)
      ·
        refine ⟨19446671068599571470334603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25928894758132761960446137 19446671068599571470334603)
        ·
          refine ⟨29170006602899357205501905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19446671068599571470334603 29170006602899357205501905)
          ·
            refine ⟨21877504952174517904126429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29170006602899357205501905 21877504952174517904126429)
            ·
              refine ⟨8204064357065444214047411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21877504952174517904126429 8204064357065444214047411)
              ·
                refine ⟨12306096535598166321071117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8204064357065444214047411 12306096535598166321071117)
                ·
                  refine ⟨4614786200849312370401669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12306096535598166321071117 4614786200849312370401669)
                  ·
                    refine ⟨865272412659246069450313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4614786200849312370401669 865272412659246069450313)
                    ·
                      rfl

theorem cell23_5055336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_5055336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055336 prefixEnd_5055336 := by exact prefixLift 5055336
  have htrace : WordTrace (prefixWord ++ tailWord_5055336) baseStart_5055336 baseEnd_5055336 := by
    simpa [prefixWord, tailWord_5055336, baseEnd_5055336] using wordTrace_append hprefix tailTrace_5055336
  have hstable : (prefixWord ++ tailWord_5055336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055336).length < 2 ^ (prefixWord ++ tailWord_5055336).sum := by decide
  have hdescent : baseEnd_5055336 < baseStart_5055336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055414 : List Nat := [5, 1, 4, 1, 1, 2, 1, 1, 2, 2, 3]
def baseStart_5055414 : Nat := 118140960795 + 5055414 * 2 ^ 59
def prefixEnd_5055414 : Nat := 4983230072969 + 3 ^ 40 * 5055414 * 2
def baseEnd_5055414 : Nat := 2595857289468788903175581

theorem tailTrace_5055414 : CollatzResearch.WordTrace tailWord_5055414 prefixEnd_5055414 2595857289468788903175581 := by
  unfold tailWord_5055414
  simp only [CollatzResearch.WordTrace]
  refine ⟨11524131031694121801115331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122924064338070632545230197 11524131031694121801115331)
  ·
    refine ⟨17286196547541182701672997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11524131031694121801115331 17286196547541182701672997)
    ·
      refine ⟨3241161852663971756563687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17286196547541182701672997 3241161852663971756563687)
      ·
        refine ⟨4861742778995957634845531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3241161852663971756563687 4861742778995957634845531)
        ·
          refine ⟨7292614168493936452268297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4861742778995957634845531 7292614168493936452268297)
          ·
            refine ⟨5469460626370452339201223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7292614168493936452268297 5469460626370452339201223)
            ·
              refine ⟨8204190939555678508801835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5469460626370452339201223 8204190939555678508801835)
              ·
                refine ⟨12306286409333517763202753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8204190939555678508801835 12306286409333517763202753)
                ·
                  refine ⟨9229714807000138322402065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12306286409333517763202753 9229714807000138322402065)
                  ·
                    refine ⟨6922286105250103741801549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9229714807000138322402065 6922286105250103741801549)
                    ·
                      refine ⟨2595857289468788903175581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6922286105250103741801549 2595857289468788903175581)
                      ·
                        rfl

theorem cell23_5055414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_5055414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055414 prefixEnd_5055414 := by exact prefixLift 5055414
  have htrace : WordTrace (prefixWord ++ tailWord_5055414) baseStart_5055414 baseEnd_5055414 := by
    simpa [prefixWord, tailWord_5055414, baseEnd_5055414] using wordTrace_append hprefix tailTrace_5055414
  have hstable : (prefixWord ++ tailWord_5055414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055414).length < 2 ^ (prefixWord ++ tailWord_5055414).sum := by decide
  have hdescent : baseEnd_5055414 < baseStart_5055414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055419 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 7, 2, 3]
def baseStart_5055419 : Nat := 118140960795 + 5055419 * 2 ^ 59
def prefixEnd_5055419 : Nat := 4983230072969 + 3 ^ 40 * 5055419 * 2
def baseEnd_5055419 : Nat := 2595859856872061383613057

theorem tailTrace_5055419 : CollatzResearch.WordTrace tailWord_5055419 prefixEnd_5055419 2595859856872061383613057 := by
  unfold tailWord_5055419
  simp only [CollatzResearch.WordTrace]
  refine ⟨184386278872087834671777311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122924185914725223114518207 184386278872087834671777311)
  ·
    refine ⟨276579418308131752007665967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184386278872087834671777311 276579418308131752007665967)
    ·
      refine ⟨414869127462197628011498951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276579418308131752007665967 414869127462197628011498951)
      ·
        refine ⟨622303691193296442017248427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414869127462197628011498951 622303691193296442017248427)
        ·
          refine ⟨933455536789944663025872641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 622303691193296442017248427 933455536789944663025872641)
          ·
            refine ⟨700091652592458497269404481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 933455536789944663025872641 700091652592458497269404481)
            ·
              refine ⟨525068739444343872952053361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 700091652592458497269404481 525068739444343872952053361)
              ·
                refine ⟨393801554583257904714040021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 525068739444343872952053361 393801554583257904714040021)
                ·
                  refine ⟨9229723935545107141735313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 393801554583257904714040021 9229723935545107141735313)
                  ·
                    refine ⟨6922292951658830356301485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9229723935545107141735313 6922292951658830356301485)
                    ·
                      refine ⟨2595859856872061383613057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6922292951658830356301485 2595859856872061383613057)
                      ·
                        rfl

theorem cell23_5055419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 2, 3].length) (baseStart_5055419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055419 prefixEnd_5055419 := by exact prefixLift 5055419
  have htrace : WordTrace (prefixWord ++ tailWord_5055419) baseStart_5055419 baseEnd_5055419 := by
    simpa [prefixWord, tailWord_5055419, baseEnd_5055419] using wordTrace_append hprefix tailTrace_5055419
  have hstable : (prefixWord ++ tailWord_5055419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055419).length < 2 ^ (prefixWord ++ tailWord_5055419).sum := by decide
  have hdescent : baseEnd_5055419 < baseStart_5055419 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055450 : List Nat := [3, 1, 1, 2, 4, 2, 2, 1, 3, 2, 2]
def baseStart_5055450 : Nat := 118140960795 + 5055450 * 2 ^ 59
def prefixEnd_5055450 : Nat := 4983230072969 + 3 ^ 40 * 5055450 * 2
def baseEnd_5055450 : Nat := 2595875774772350762325415

theorem tailTrace_5055450 : CollatzResearch.WordTrace tailWord_5055450 prefixEnd_5055450 2595875774772350762325415 := by
  unfold tailWord_5055450
  simp only [CollatzResearch.WordTrace]
  refine ⟨46096852383743881741538951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122924939689983684644103869 46096852383743881741538951)
  ·
    refine ⟨69145278575615822612308427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46096852383743881741538951 69145278575615822612308427)
    ·
      refine ⟨103717917863423733918462641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69145278575615822612308427 103717917863423733918462641)
      ·
        refine ⟨77788438397567800438846981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103717917863423733918462641 77788438397567800438846981)
        ·
          refine ⟨14585332199543962582283809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77788438397567800438846981 14585332199543962582283809)
          ·
            refine ⟨10938999149657971936712857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14585332199543962582283809 10938999149657971936712857)
            ·
              refine ⟨8204249362243478952534643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10938999149657971936712857 8204249362243478952534643)
              ·
                refine ⟨12306374043365218428801965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8204249362243478952534643 12306374043365218428801965)
                ·
                  refine ⟨4614890266261956910800737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12306374043365218428801965 4614890266261956910800737)
                  ·
                    refine ⟨3461167699696467683100553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4614890266261956910800737 3461167699696467683100553)
                    ·
                      refine ⟨2595875774772350762325415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3461167699696467683100553 2595875774772350762325415)
                      ·
                        rfl

theorem cell23_5055450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 3, 2, 2].length) (baseStart_5055450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055450 prefixEnd_5055450 := by exact prefixLift 5055450
  have htrace : WordTrace (prefixWord ++ tailWord_5055450) baseStart_5055450 baseEnd_5055450 := by
    simpa [prefixWord, tailWord_5055450, baseEnd_5055450] using wordTrace_append hprefix tailTrace_5055450
  have hstable : (prefixWord ++ tailWord_5055450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055450).length < 2 ^ (prefixWord ++ tailWord_5055450).sum := by decide
  have hdescent : baseEnd_5055450 < baseStart_5055450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055463 : List Nat := [1, 1, 5, 2, 2, 3, 1, 1, 1, 2, 4]
def baseStart_5055463 : Nat := 118140960795 + 5055463 * 2 ^ 59
def prefixEnd_5055463 : Nat := 4983230072969 + 3 ^ 40 * 5055463 * 2
def baseEnd_5055463 : Nat := 2595882450020859211462855

theorem tailTrace_5055463 : CollatzResearch.WordTrace tailWord_5055463 prefixEnd_5055463 2595882450020859211462855 := by
  unfold tailWord_5055463
  simp only [CollatzResearch.WordTrace]
  refine ⟨184387883683928430186379043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122925255789285620124252695 184387883683928430186379043)
  ·
    refine ⟨276581825525892645279568565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184387883683928430186379043 276581825525892645279568565)
    ·
      refine ⟨25929546143052435494959553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 276581825525892645279568565 25929546143052435494959553)
      ·
        refine ⟨19447159607289326621219665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25929546143052435494959553 19447159607289326621219665)
        ·
          refine ⟨14585369705466994965914749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19447159607289326621219665 14585369705466994965914749)
          ·
            refine ⟨5469513639550123112218031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14585369705466994965914749 5469513639550123112218031)
            ·
              refine ⟨8204270459325184668327047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5469513639550123112218031 8204270459325184668327047)
              ·
                refine ⟨12306405688987777002490571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8204270459325184668327047 12306405688987777002490571)
                ·
                  refine ⟨18459608533481665503735857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12306405688987777002490571 18459608533481665503735857)
                  ·
                    refine ⟨13844706400111249127801893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18459608533481665503735857 13844706400111249127801893)
                    ·
                      refine ⟨2595882450020859211462855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13844706400111249127801893 2595882450020859211462855)
                      ·
                        rfl

theorem cell23_5055463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_5055463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055463 prefixEnd_5055463 := by exact prefixLift 5055463
  have htrace : WordTrace (prefixWord ++ tailWord_5055463) baseStart_5055463 baseEnd_5055463 := by
    simpa [prefixWord, tailWord_5055463, baseEnd_5055463] using wordTrace_append hprefix tailTrace_5055463
  have hstable : (prefixWord ++ tailWord_5055463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055463).length < 2 ^ (prefixWord ++ tailWord_5055463).sum := by decide
  have hdescent : baseEnd_5055463 < baseStart_5055463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055470 : List Nat := [4, 1, 2, 1, 4, 1, 2, 2, 1, 2, 3]
def baseStart_5055470 : Nat := 118140960795 + 5055470 * 2 ^ 59
def prefixEnd_5055470 : Nat := 4983230072969 + 3 ^ 40 * 5055470 * 2
def baseEnd_5055470 : Nat := 2595886044385440684075323

theorem tailTrace_5055470 : CollatzResearch.WordTrace tailWord_5055470 prefixEnd_5055470 2595886044385440684075323 := by
  unfold tailWord_5055470
  simp only [CollatzResearch.WordTrace]
  refine ⟨23048517374362883797735483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122925425996602046921255909 23048517374362883797735483)
  ·
    refine ⟨34572776061544325696603225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23048517374362883797735483 34572776061544325696603225)
    ·
      refine ⟨25929582046158244272452419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34572776061544325696603225 25929582046158244272452419)
      ·
        refine ⟨38894373069237366408678629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25929582046158244272452419 38894373069237366408678629)
        ·
          refine ⟨7292694950482006201627243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38894373069237366408678629 7292694950482006201627243)
          ·
            refine ⟨10939042425723009302440865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7292694950482006201627243 10939042425723009302440865)
            ·
              refine ⟨8204281819292256976830649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10939042425723009302440865 8204281819292256976830649)
              ·
                refine ⟨6153211364469192732622987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8204281819292256976830649 6153211364469192732622987)
                ·
                  refine ⟨9229817046703789098934481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6153211364469192732622987 9229817046703789098934481)
                  ·
                    refine ⟨6922362785027841824200861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9229817046703789098934481 6922362785027841824200861)
                    ·
                      refine ⟨2595886044385440684075323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6922362785027841824200861 2595886044385440684075323)
                      ·
                        rfl

theorem cell23_5055470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_5055470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055470 prefixEnd_5055470 := by exact prefixLift 5055470
  have htrace : WordTrace (prefixWord ++ tailWord_5055470) baseStart_5055470 baseEnd_5055470 := by
    simpa [prefixWord, tailWord_5055470, baseEnd_5055470] using wordTrace_append hprefix tailTrace_5055470
  have hstable : (prefixWord ++ tailWord_5055470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055470).length < 2 ^ (prefixWord ++ tailWord_5055470).sum := by decide
  have hdescent : baseEnd_5055470 < baseStart_5055470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055490 : List Nat := [3, 4, 1, 3, 2, 1, 9]
def baseStart_5055490 : Nat := 118140960795 + 5055490 * 2 ^ 59
def prefixEnd_5055490 : Nat := 4983230072969 + 3 ^ 40 * 5055490 * 2
def baseEnd_5055490 : Nat := 32048102641957167973151

theorem tailTrace_5055490 : CollatzResearch.WordTrace tailWord_5055490 prefixEnd_5055490 32048102641957167973151 := by
  unfold tailWord_5055490
  simp only [CollatzResearch.WordTrace]
  refine ⟨46097217113707653449402981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122925912303220409198407949 46097217113707653449402981)
  ·
    refine ⟨8643228208820185021763059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46097217113707653449402981 8643228208820185021763059)
    ·
      refine ⟨12964842313230277532644589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8643228208820185021763059 12964842313230277532644589)
      ·
        refine ⟨4861815867461354074741721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12964842313230277532644589 4861815867461354074741721)
        ·
          refine ⟨3646361900596015556056291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4861815867461354074741721 3646361900596015556056291)
          ·
            refine ⟨5469542850894023334084437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3646361900596015556056291 5469542850894023334084437)
            ·
              refine ⟨32048102641957167973151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5469542850894023334084437 32048102641957167973151)
              ·
                rfl

theorem cell23_5055490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 9].length) (baseStart_5055490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055490 prefixEnd_5055490 := by exact prefixLift 5055490
  have htrace : WordTrace (prefixWord ++ tailWord_5055490) baseStart_5055490 baseEnd_5055490 := by
    simpa [prefixWord, tailWord_5055490, baseEnd_5055490] using wordTrace_append hprefix tailTrace_5055490
  have hstable : (prefixWord ++ tailWord_5055490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055490).length < 2 ^ (prefixWord ++ tailWord_5055490).sum := by decide
  have hdescent : baseEnd_5055490 < baseStart_5055490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055493 : List Nat := [1, 3, 1, 1, 2, 3, 1, 5, 1, 3, 2]
def baseStart_5055493 : Nat := 118140960795 + 5055493 * 2 ^ 59
def prefixEnd_5055493 : Nat := 4983230072969 + 3 ^ 40 * 5055493 * 2
def baseEnd_5055493 : Nat := 2595897854440494094087717

theorem tailTrace_5055493 : CollatzResearch.WordTrace tailWord_5055493 prefixEnd_5055493 2595897854440494094087717 := by
  unfold tailWord_5055493
  simp only [CollatzResearch.WordTrace]
  refine ⟨184388977873819745309971133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122925985249213163539980755 184388977873819745309971133)
  ·
    refine ⟨69145866702682404491239175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184388977873819745309971133 69145866702682404491239175)
    ·
      refine ⟨103718800054023606736858763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69145866702682404491239175 103718800054023606736858763)
      ·
        refine ⟨155578200081035410105288145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103718800054023606736858763 155578200081035410105288145)
        ·
          refine ⟨116683650060776557578966109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155578200081035410105288145 116683650060776557578966109)
          ·
            refine ⟨43756368772791209092112291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116683650060776557578966109 43756368772791209092112291)
            ·
              refine ⟨65634553159186813638168437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43756368772791209092112291 65634553159186813638168437)
              ·
                refine ⟨6153239358673763778578291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65634553159186813638168437 6153239358673763778578291)
                ·
                  refine ⟨9229859038010645667867437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6153239358673763778578291 9229859038010645667867437)
                  ·
                    refine ⟨3461197139253992125450289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9229859038010645667867437 3461197139253992125450289)
                    ·
                      refine ⟨2595897854440494094087717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3461197139253992125450289 2595897854440494094087717)
                      ·
                        rfl

theorem cell23_5055493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 3, 2].length) (baseStart_5055493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055493 prefixEnd_5055493 := by exact prefixLift 5055493
  have htrace : WordTrace (prefixWord ++ tailWord_5055493) baseStart_5055493 baseEnd_5055493 := by
    simpa [prefixWord, tailWord_5055493, baseEnd_5055493] using wordTrace_append hprefix tailTrace_5055493
  have hstable : (prefixWord ++ tailWord_5055493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055493).length < 2 ^ (prefixWord ++ tailWord_5055493).sum := by decide
  have hdescent : baseEnd_5055493 < baseStart_5055493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055527 : List Nat := [1, 1, 7, 1, 1, 1, 3, 2, 1, 3, 2]
def baseStart_5055527 : Nat := 118140960795 + 5055527 * 2 ^ 59
def prefixEnd_5055527 : Nat := 4983230072969 + 3 ^ 40 * 5055527 * 2
def baseEnd_5055527 : Nat := 2595915312782746961062561

theorem tailTrace_5055527 : CollatzResearch.WordTrace tailWord_5055527 prefixEnd_5055527 2595915312782746961062561 := by
  unfold tailWord_5055527
  simp only [CollatzResearch.WordTrace]
  refine ⟨184390217955696569116708835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122926811970464379411139223 184390217955696569116708835)
  ·
    refine ⟨276585326933544853675063253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184390217955696569116708835 276585326933544853675063253)
    ·
      refine ⟨6482468600004957508009295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 276585326933544853675063253 6482468600004957508009295)
      ·
        refine ⟨9723702900007436262013943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6482468600004957508009295 9723702900007436262013943)
        ·
          refine ⟨14585554350011154393020915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9723702900007436262013943 14585554350011154393020915)
          ·
            refine ⟨21878331525016731589531373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14585554350011154393020915 21878331525016731589531373)
            ·
              refine ⟨8204374321881274346074265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21878331525016731589531373 8204374321881274346074265)
              ·
                refine ⟨6153280741410955759555699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8204374321881274346074265 6153280741410955759555699)
                ·
                  refine ⟨9229921112116433639333549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6153280741410955759555699 9229921112116433639333549)
                  ·
                    refine ⟨3461220417043662614750081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9229921112116433639333549 3461220417043662614750081)
                    ·
                      refine ⟨2595915312782746961062561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3461220417043662614750081 2595915312782746961062561)
                      ·
                        rfl

theorem cell23_5055527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_5055527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055527 prefixEnd_5055527 := by exact prefixLift 5055527
  have htrace : WordTrace (prefixWord ++ tailWord_5055527) baseStart_5055527 baseEnd_5055527 := by
    simpa [prefixWord, tailWord_5055527, baseEnd_5055527] using wordTrace_append hprefix tailTrace_5055527
  have hstable : (prefixWord ++ tailWord_5055527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055527).length < 2 ^ (prefixWord ++ tailWord_5055527).sum := by decide
  have hdescent : baseEnd_5055527 < baseStart_5055527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055540 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 3, 4, 2]
def baseStart_5055540 : Nat := 118140960795 + 5055540 * 2 ^ 59
def prefixEnd_5055540 : Nat := 4983230072969 + 3 ^ 40 * 5055540 * 2
def baseEnd_5055540 : Nat := 2595921988031255410200001

theorem tailTrace_5055540 : CollatzResearch.WordTrace tailWord_5055540 prefixEnd_5055540 2595921988031255410200001 := by
  unfold tailWord_5055540
  simp only [CollatzResearch.WordTrace]
  refine ⟨92195346052324736168466037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122927128069766314891288049 92195346052324736168466037)
  ·
    refine ⟨8643313692405444015793691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92195346052324736168466037 8643313692405444015793691)
    ·
      refine ⟨12964970538608166023690537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8643313692405444015793691 12964970538608166023690537)
      ·
        refine ⟨9723727903956124517767903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12964970538608166023690537 9723727903956124517767903)
        ·
          refine ⟨14585591855934186776651855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9723727903956124517767903 14585591855934186776651855)
          ·
            refine ⟨21878387783901280164977783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14585591855934186776651855 21878387783901280164977783)
            ·
              refine ⟨32817581675851920247466675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21878387783901280164977783 32817581675851920247466675)
              ·
                refine ⟨49226372513777880371200013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32817581675851920247466675 49226372513777880371200013)
                ·
                  refine ⟨18459889692666705139200005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49226372513777880371200013 18459889692666705139200005)
                  ·
                    refine ⟨3461229317375007213600001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18459889692666705139200005 3461229317375007213600001)
                    ·
                      refine ⟨2595921988031255410200001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3461229317375007213600001 2595921988031255410200001)
                      ·
                        rfl

theorem cell23_5055540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_5055540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055540 prefixEnd_5055540 := by exact prefixLift 5055540
  have htrace : WordTrace (prefixWord ++ tailWord_5055540) baseStart_5055540 baseEnd_5055540 := by
    simpa [prefixWord, tailWord_5055540, baseEnd_5055540] using wordTrace_append hprefix tailTrace_5055540
  have hstable : (prefixWord ++ tailWord_5055540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055540).length < 2 ^ (prefixWord ++ tailWord_5055540).sum := by decide
  have hdescent : baseEnd_5055540 < baseStart_5055540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055574 : List Nat := [5, 2, 2, 1, 2, 1, 2, 1, 1, 4, 2]
def baseStart_5055574 : Nat := 118140960795 + 5055574 * 2 ^ 59
def prefixEnd_5055574 : Nat := 4983230072969 + 3 ^ 40 * 5055574 * 2
def baseEnd_5055574 : Nat := 2595939446373508277174845

theorem tailTrace_5055574 : CollatzResearch.WordTrace tailWord_5055574 prefixEnd_5055574 2595939446373508277174845 := by
  unfold tailWord_5055574
  simp only [CollatzResearch.WordTrace]
  refine ⟨11524495761657893508979361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122927954791017530762446517 11524495761657893508979361)
  ·
    refine ⟨8643371821243420131734521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11524495761657893508979361 8643371821243420131734521)
    ·
      refine ⟨6482528865932565098800891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8643371821243420131734521 6482528865932565098800891)
      ·
        refine ⟨9723793298898847648201337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6482528865932565098800891 9723793298898847648201337)
        ·
          refine ⟨7292844974174135736151003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9723793298898847648201337 7292844974174135736151003)
          ·
            refine ⟨10939267461261203604226505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7292844974174135736151003 10939267461261203604226505)
            ·
              refine ⟨8204450595945902703169879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10939267461261203604226505 8204450595945902703169879)
              ·
                refine ⟨12306675893918854054754819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8204450595945902703169879 12306675893918854054754819)
                ·
                  refine ⟨18460013840878281082132229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12306675893918854054754819 18460013840878281082132229)
                  ·
                    refine ⟨3461252595164677702899793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18460013840878281082132229 3461252595164677702899793)
                    ·
                      refine ⟨2595939446373508277174845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3461252595164677702899793 2595939446373508277174845)
                      ·
                        rfl

theorem cell23_5055574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_5055574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055574 prefixEnd_5055574 := by exact prefixLift 5055574
  have htrace : WordTrace (prefixWord ++ tailWord_5055574) baseStart_5055574 baseEnd_5055574 := by
    simpa [prefixWord, tailWord_5055574, baseEnd_5055574] using wordTrace_append hprefix tailTrace_5055574
  have hstable : (prefixWord ++ tailWord_5055574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055574).length < 2 ^ (prefixWord ++ tailWord_5055574).sum := by decide
  have hdescent : baseEnd_5055574 < baseStart_5055574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055593 : List Nat := [1, 2, 1, 1, 1, 8, 1, 1, 2, 5]
def baseStart_5055593 : Nat := 118140960795 + 5055593 * 2 ^ 59
def prefixEnd_5055593 : Nat := 4983230072969 + 3 ^ 40 * 5055593 * 2
def baseEnd_5055593 : Nat := 865316400835314567612419

theorem tailTrace_5055593 : CollatzResearch.WordTrace tailWord_5055593 prefixEnd_5055593 865316400835314567612419 := by
  unfold tailWord_5055593
  simp only [CollatzResearch.WordTrace]
  refine ⟨184392625173457462388611433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122928416782304974925740955 184392625173457462388611433)
  ·
    refine ⟨138294468880093096791458575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184392625173457462388611433 138294468880093096791458575)
    ·
      refine ⟨207441703320139645187187863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138294468880093096791458575 207441703320139645187187863)
      ·
        refine ⟨311162554980209467780781795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207441703320139645187187863 311162554980209467780781795)
        ·
          refine ⟨466743832470314201671172693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311162554980209467780781795 466743832470314201671172693)
          ·
            refine ⟨5469654286761494550834055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 466743832470314201671172693 5469654286761494550834055)
            ·
              refine ⟨8204481430142241826251083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5469654286761494550834055 8204481430142241826251083)
              ·
                refine ⟨12306722145213362739376625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8204481430142241826251083 12306722145213362739376625)
                ·
                  refine ⟨9230041608910022054532469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12306722145213362739376625 9230041608910022054532469)
                  ·
                    refine ⟨865316400835314567612419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9230041608910022054532469 865316400835314567612419)
                    ·
                      rfl

theorem cell23_5055593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 5].length) (baseStart_5055593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055593 prefixEnd_5055593 := by exact prefixLift 5055593
  have htrace : WordTrace (prefixWord ++ tailWord_5055593) baseStart_5055593 baseEnd_5055593 := by
    simpa [prefixWord, tailWord_5055593, baseEnd_5055593] using wordTrace_append hprefix tailTrace_5055593
  have hstable : (prefixWord ++ tailWord_5055593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055593).length < 2 ^ (prefixWord ++ tailWord_5055593).sum := by decide
  have hdescent : baseEnd_5055593 < baseStart_5055593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055596 : List Nat := [2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 4]
def baseStart_5055596 : Nat := 118140960795 + 5055596 * 2 ^ 59
def prefixEnd_5055596 : Nat := 4983230072969 + 3 ^ 40 * 5055596 * 2
def baseEnd_5055596 : Nat := 2595950742947907191099743

theorem tailTrace_5055596 : CollatzResearch.WordTrace tailWord_5055596 prefixEnd_5055596 2595950742947907191099743 := by
  unfold tailWord_5055596
  simp only [CollatzResearch.WordTrace]
  refine ⟨92196367296223296950485321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122928489728297729267313761 92196367296223296950485321)
  ·
    refine ⟨69147275472167472712863991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92196367296223296950485321 69147275472167472712863991)
    ·
      refine ⟨103720913208251209069295987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69147275472167472712863991 103720913208251209069295987)
      ·
        refine ⟨155581369812376813603943981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103720913208251209069295987 155581369812376813603943981)
        ·
          refine ⟨58343013679641305101478993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155581369812376813603943981 58343013679641305101478993)
          ·
            refine ⟨43757260259730978826109245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58343013679641305101478993 43757260259730978826109245)
            ·
              refine ⟨16408972597399117059790967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43757260259730978826109245 16408972597399117059790967)
              ·
                refine ⟨24613458896098675589686451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16408972597399117059790967 24613458896098675589686451)
                ·
                  refine ⟨36920188344148013384529677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24613458896098675589686451 36920188344148013384529677)
                  ·
                    refine ⟨13845070629055505019198629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36920188344148013384529677 13845070629055505019198629)
                    ·
                      refine ⟨2595950742947907191099743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13845070629055505019198629 2595950742947907191099743)
                      ·
                        rfl

theorem cell23_5055596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_5055596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055596 prefixEnd_5055596 := by exact prefixLift 5055596
  have htrace : WordTrace (prefixWord ++ tailWord_5055596) baseStart_5055596 baseEnd_5055596 := by
    simpa [prefixWord, tailWord_5055596, baseEnd_5055596] using wordTrace_append hprefix tailTrace_5055596
  have hstable : (prefixWord ++ tailWord_5055596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055596).length < 2 ^ (prefixWord ++ tailWord_5055596).sum := by decide
  have hdescent : baseEnd_5055596 < baseStart_5055596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055613 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 4, 4, 2]
def baseStart_5055613 : Nat := 118140960795 + 5055613 * 2 ^ 59
def prefixEnd_5055613 : Nat := 4983230072969 + 3 ^ 40 * 5055613 * 2
def baseEnd_5055613 : Nat := 2595959472119033624587165

theorem tailTrace_5055613 : CollatzResearch.WordTrace tailWord_5055613 prefixEnd_5055613 2595959472119033624587165 := by
  unfold tailWord_5055613
  simp only [CollatzResearch.WordTrace]
  refine ⟨184393354633385005804339493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122928903088923337202892995 184393354633385005804339493)
  ·
    refine ⟨34573753993759688588313655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184393354633385005804339493 34573753993759688588313655)
    ·
      refine ⟨51860630990639532882470483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34573753993759688588313655 51860630990639532882470483)
      ·
        refine ⟨77790946485959299323705725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51860630990639532882470483 77790946485959299323705725)
        ·
          refine ⟨29171604932234737246389647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77790946485959299323705725 29171604932234737246389647)
          ·
            refine ⟨43757407398352105869584471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29171604932234737246389647 43757407398352105869584471)
            ·
              refine ⟨65636111097528158804376707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43757407398352105869584471 65636111097528158804376707)
              ·
                refine ⟨98454166646292238206565061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65636111097528158804376707 98454166646292238206565061)
                ·
                  refine ⟨18460156246179794663730949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98454166646292238206565061 18460156246179794663730949)
                  ·
                    refine ⟨3461279296158711499449553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18460156246179794663730949 3461279296158711499449553)
                    ·
                      refine ⟨2595959472119033624587165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3461279296158711499449553 2595959472119033624587165)
                      ·
                        rfl

theorem cell23_5055613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 4, 2].length) (baseStart_5055613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055613 prefixEnd_5055613 := by exact prefixLift 5055613
  have htrace : WordTrace (prefixWord ++ tailWord_5055613) baseStart_5055613 baseEnd_5055613 := by
    simpa [prefixWord, tailWord_5055613, baseEnd_5055613] using wordTrace_append hprefix tailTrace_5055613
  have hstable : (prefixWord ++ tailWord_5055613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055613).length < 2 ^ (prefixWord ++ tailWord_5055613).sum := by decide
  have hdescent : baseEnd_5055613 < baseStart_5055613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055626 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 2, 1, 6]
def baseStart_5055626 : Nat := 118140960795 + 5055626 * 2 ^ 59
def prefixEnd_5055626 : Nat := 4983230072969 + 3 ^ 40 * 5055626 * 2
def baseEnd_5055626 : Nat := 2595966147367542073724605

theorem tailTrace_5055626 : CollatzResearch.WordTrace tailWord_5055626 prefixEnd_5055626 2595966147367542073724605 := by
  unfold tailWord_5055626
  simp only [CollatzResearch.WordTrace]
  refine ⟨46098457195584477256140683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122929219188225272683041821 46098457195584477256140683)
  ·
    refine ⟨69147685793376715884211025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46098457195584477256140683 69147685793376715884211025)
    ·
      refine ⟨51860764345032536913158269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69147685793376715884211025 51860764345032536913158269)
      ·
        refine ⟨19447786629387201342434351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51860764345032536913158269 19447786629387201342434351)
        ·
          refine ⟨29171679944080802013651527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19447786629387201342434351 29171679944080802013651527)
          ·
            refine ⟨43757519916121203020477291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29171679944080802013651527 43757519916121203020477291)
            ·
              refine ⟨65636279874181804530715937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43757519916121203020477291 65636279874181804530715937)
              ·
                refine ⟨49227209905636353398036953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65636279874181804530715937 49227209905636353398036953)
                ·
                  refine ⟨36920407429227265048527715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49227209905636353398036953 36920407429227265048527715)
                  ·
                    refine ⟨55380611143840897572791573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36920407429227265048527715 55380611143840897572791573)
                    ·
                      refine ⟨2595966147367542073724605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55380611143840897572791573 2595966147367542073724605)
                      ·
                        rfl

theorem cell23_5055626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_5055626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055626 prefixEnd_5055626 := by exact prefixLift 5055626
  have htrace : WordTrace (prefixWord ++ tailWord_5055626) baseStart_5055626 baseEnd_5055626 := by
    simpa [prefixWord, tailWord_5055626, baseEnd_5055626] using wordTrace_append hprefix tailTrace_5055626
  have hstable : (prefixWord ++ tailWord_5055626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055626).length < 2 ^ (prefixWord ++ tailWord_5055626).sum := by decide
  have hdescent : baseEnd_5055626 < baseStart_5055626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055630 : List Nat := [4, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2]
def baseStart_5055630 : Nat := 118140960795 + 5055630 * 2 ^ 59
def prefixEnd_5055630 : Nat := 4983230072969 + 3 ^ 40 * 5055630 * 2
def baseEnd_5055630 : Nat := 2595968201290160058074587

theorem tailTrace_5055630 : CollatzResearch.WordTrace tailWord_5055630 prefixEnd_5055630 2595968201290160058074587 := by
  unfold tailWord_5055630
  simp only [CollatzResearch.WordTrace]
  refine ⟨23049246834290427213463543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122929316449548945138472229 23049246834290427213463543)
  ·
    refine ⟨34573870251435640820195315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23049246834290427213463543 34573870251435640820195315)
    ·
      refine ⟨51860805377153461230292973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34573870251435640820195315 51860805377153461230292973)
      ·
        refine ⟨19447802016432547961359865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51860805377153461230292973 19447802016432547961359865)
        ·
          refine ⟨14585851512324410971019899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19447802016432547961359865 14585851512324410971019899)
          ·
            refine ⟨21878777268486616456529849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14585851512324410971019899 21878777268486616456529849)
            ·
              refine ⟨16409082951364962342397387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21878777268486616456529849 16409082951364962342397387)
              ·
                refine ⟨24613624427047443513596081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16409082951364962342397387 24613624427047443513596081)
                ·
                  refine ⟨18460218320285582635197061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24613624427047443513596081 18460218320285582635197061)
                  ·
                    refine ⟨3461290935053546744099449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18460218320285582635197061 3461290935053546744099449)
                    ·
                      refine ⟨2595968201290160058074587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3461290935053546744099449 2595968201290160058074587)
                      ·
                        rfl

theorem cell23_5055630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_5055630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055630 prefixEnd_5055630 := by exact prefixLift 5055630
  have htrace : WordTrace (prefixWord ++ tailWord_5055630) baseStart_5055630 baseEnd_5055630 := by
    simpa [prefixWord, tailWord_5055630, baseEnd_5055630] using wordTrace_append hprefix tailTrace_5055630
  have hstable : (prefixWord ++ tailWord_5055630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055630).length < 2 ^ (prefixWord ++ tailWord_5055630).sum := by decide
  have hdescent : baseEnd_5055630 < baseStart_5055630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055663 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 5, 1, 3]
def baseStart_5055663 : Nat := 118140960795 + 5055663 * 2 ^ 59
def prefixEnd_5055663 : Nat := 4983230072969 + 3 ^ 40 * 5055663 * 2
def baseEnd_5055663 : Nat := 2595985146151758428961935

theorem tailTrace_5055663 : CollatzResearch.WordTrace tailWord_5055663 prefixEnd_5055663 2595985146151758428961935 := by
  unfold tailWord_5055663
  simp only [CollatzResearch.WordTrace]
  refine ⟨184395178283203864343659643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122930118855469242895773095 184395178283203864343659643)
  ·
    refine ⟨276592767424805796515489465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184395178283203864343659643 276592767424805796515489465)
    ·
      refine ⟨207444575568604347386617099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276592767424805796515489465 207444575568604347386617099)
      ·
        refine ⟨311166863352906521079925649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207444575568604347386617099 311166863352906521079925649)
        ·
          refine ⟨233375147514679890809944237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311166863352906521079925649 233375147514679890809944237)
          ·
            refine ⟨87515680318004959053729089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 233375147514679890809944237 87515680318004959053729089)
            ·
              refine ⟨65636760238503719290296817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87515680318004959053729089 65636760238503719290296817)
              ·
                refine ⟨49227570178877789467722613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65636760238503719290296817 49227570178877789467722613)
                ·
                  refine ⟨4615084704269792762598995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49227570178877789467722613 4615084704269792762598995)
                  ·
                    refine ⟨6922627056404689143898493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4615084704269792762598995 6922627056404689143898493)
                    ·
                      refine ⟨2595985146151758428961935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6922627056404689143898493 2595985146151758428961935)
                      ·
                        rfl

theorem cell23_5055663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 5, 1, 3].length) (baseStart_5055663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055663 prefixEnd_5055663 := by exact prefixLift 5055663
  have htrace : WordTrace (prefixWord ++ tailWord_5055663) baseStart_5055663 baseEnd_5055663 := by
    simpa [prefixWord, tailWord_5055663, baseEnd_5055663] using wordTrace_append hprefix tailTrace_5055663
  have hstable : (prefixWord ++ tailWord_5055663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055663).length < 2 ^ (prefixWord ++ tailWord_5055663).sum := by decide
  have hdescent : baseEnd_5055663 < baseStart_5055663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055703 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 2, 6, 2]
def baseStart_5055703 : Nat := 118140960795 + 5055703 * 2 ^ 59
def prefixEnd_5055703 : Nat := 4983230072969 + 3 ^ 40 * 5055703 * 2
def baseEnd_5055703 : Nat := 2596005685377938272461751

theorem tailTrace_5055703 : CollatzResearch.WordTrace tailWord_5055703 prefixEnd_5055703 2596005685377938272461751 := by
  unfold tailWord_5055703
  simp only [CollatzResearch.WordTrace]
  refine ⟨184396637203058951175115763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122931091468705967450077175 184396637203058951175115763)
  ·
    refine ⟨276594955804588426762673645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184396637203058951175115763 276594955804588426762673645)
    ·
      refine ⟨103723108426720660036002617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 276594955804588426762673645 103723108426720660036002617)
      ·
        refine ⟨77792331320040495027001963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103723108426720660036002617 77792331320040495027001963)
        ·
          refine ⟨116688496980060742540502945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77792331320040495027001963 116688496980060742540502945)
          ·
            refine ⟨87516372735045556905377209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116688496980060742540502945 87516372735045556905377209)
            ·
              refine ⟨65637279551284167679032907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87516372735045556905377209 65637279551284167679032907)
              ·
                refine ⟨98455919326926251518549361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65637279551284167679032907 98455919326926251518549361)
                ·
                  refine ⟨73841939495194688638912021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98455919326926251518549361 73841939495194688638912021)
                  ·
                    refine ⟨3461340913837251029949001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73841939495194688638912021 3461340913837251029949001)
                    ·
                      refine ⟨2596005685377938272461751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3461340913837251029949001 2596005685377938272461751)
                      ·
                        rfl

theorem cell23_5055703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 6, 2].length) (baseStart_5055703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055703 prefixEnd_5055703 := by exact prefixLift 5055703
  have htrace : WordTrace (prefixWord ++ tailWord_5055703) baseStart_5055703 baseEnd_5055703 := by
    simpa [prefixWord, tailWord_5055703, baseEnd_5055703] using wordTrace_append hprefix tailTrace_5055703
  have hstable : (prefixWord ++ tailWord_5055703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055703).length < 2 ^ (prefixWord ++ tailWord_5055703).sum := by decide
  have hdescent : baseEnd_5055703 < baseStart_5055703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055713 : List Nat := [1, 2, 3, 1, 3, 3, 1, 2, 1, 6]
def baseStart_5055713 : Nat := 118140960795 + 5055713 * 2 ^ 59
def prefixEnd_5055713 : Nat := 4983230072969 + 3 ^ 40 * 5055713 * 2
def baseEnd_5055713 : Nat := 865336940061494411112235

theorem tailTrace_5055713 : CollatzResearch.WordTrace tailWord_5055713 prefixEnd_5055713 865336940061494411112235 := by
  unfold tailWord_5055713
  simp only [CollatzResearch.WordTrace]
  refine ⟨184397001933022722882979793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122931334622015148588653195 184397001933022722882979793)
  ·
    refine ⟨138297751449767042162234845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184397001933022722882979793 138297751449767042162234845)
    ·
      refine ⟨51861656793662640810838067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138297751449767042162234845 51861656793662640810838067)
      ·
        refine ⟨77792485190493961216257101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51861656793662640810838067 77792485190493961216257101)
        ·
          refine ⟨29172181946435235456096413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77792485190493961216257101 29172181946435235456096413)
          ·
            refine ⟨10939568229913213296036155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29172181946435235456096413 10939568229913213296036155)
            ·
              refine ⟨16409352344869819944054233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10939568229913213296036155 16409352344869819944054233)
              ·
                refine ⟨12307014258652364958040675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16409352344869819944054233 12307014258652364958040675)
                ·
                  refine ⟨18460521387978547437061013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12307014258652364958040675 18460521387978547437061013)
                  ·
                    refine ⟨865336940061494411112235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18460521387978547437061013 865336940061494411112235)
                    ·
                      rfl

theorem cell23_5055713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_5055713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055713 prefixEnd_5055713 := by exact prefixLift 5055713
  have htrace : WordTrace (prefixWord ++ tailWord_5055713) baseStart_5055713 baseEnd_5055713 := by
    simpa [prefixWord, tailWord_5055713, baseEnd_5055713] using wordTrace_append hprefix tailTrace_5055713
  have hstable : (prefixWord ++ tailWord_5055713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055713).length < 2 ^ (prefixWord ++ tailWord_5055713).sum := by decide
  have hdescent : baseEnd_5055713 < baseStart_5055713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055717 : List Nat := [1, 3, 1, 4, 3, 1, 3, 1, 1, 5]
def baseStart_5055717 : Nat := 118140960795 + 5055717 * 2 ^ 59
def prefixEnd_5055717 : Nat := 4983230072969 + 3 ^ 40 * 5055717 * 2
def baseEnd_5055717 : Nat := 865337624702367072562229

theorem tailTrace_5055717 : CollatzResearch.WordTrace tailWord_5055717 prefixEnd_5055717 865337624702367072562229 := by
  unfold tailWord_5055717
  simp only [CollatzResearch.WordTrace]
  refine ⟨184397147825008231566125405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122931431883338821044083603 184397147825008231566125405)
  ·
    refine ⟨69148930434378086837297027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184397147825008231566125405 69148930434378086837297027)
    ·
      refine ⟨103723395651567130255945541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69148930434378086837297027 103723395651567130255945541)
      ·
        refine ⟨19448136684668836922989789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103723395651567130255945541 19448136684668836922989789)
        ·
          refine ⟨7293051256750813846121171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19448136684668836922989789 7293051256750813846121171)
          ·
            refine ⟨10939576885126220769181757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7293051256750813846121171 10939576885126220769181757)
            ·
              refine ⟨4102341331922332788443159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10939576885126220769181757 4102341331922332788443159)
              ·
                refine ⟨6153511997883499182664739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4102341331922332788443159 6153511997883499182664739)
                ·
                  refine ⟨9230267996825248773997109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6153511997883499182664739 9230267996825248773997109)
                  ·
                    refine ⟨865337624702367072562229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9230267996825248773997109 865337624702367072562229)
                    ·
                      rfl

theorem cell23_5055717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 1, 5].length) (baseStart_5055717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055717 prefixEnd_5055717 := by exact prefixLift 5055717
  have htrace : WordTrace (prefixWord ++ tailWord_5055717) baseStart_5055717 baseEnd_5055717 := by
    simpa [prefixWord, tailWord_5055717, baseEnd_5055717] using wordTrace_append hprefix tailTrace_5055717
  have hstable : (prefixWord ++ tailWord_5055717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055717).length < 2 ^ (prefixWord ++ tailWord_5055717).sum := by decide
  have hdescent : baseEnd_5055717 < baseStart_5055717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055723 : List Nat := [1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 5]
def baseStart_5055723 : Nat := 118140960795 + 5055723 * 2 ^ 59
def prefixEnd_5055723 : Nat := 4983230072969 + 3 ^ 40 * 5055723 * 2
def baseEnd_5055723 : Nat := 2596015954991028194211659

theorem tailTrace_5055723 : CollatzResearch.WordTrace tailWord_5055723 prefixEnd_5055723 2596015954991028194211659 := by
  unfold tailWord_5055723
  simp only [CollatzResearch.WordTrace]
  refine ⟨184397366662986494590843823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122931577775324329727229215 184397366662986494590843823)
  ·
    refine ⟨276596049994479741886265735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184397366662986494590843823 276596049994479741886265735)
    ·
      refine ⟨414894074991719612829398603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276596049994479741886265735 414894074991719612829398603)
      ·
        refine ⟨622341112487579419244097905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414894074991719612829398603 622341112487579419244097905)
        ·
          refine ⟨466755834365684564433073429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 622341112487579419244097905 466755834365684564433073429)
          ·
            refine ⟨21879179735891463957800317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 466755834365684564433073429 21879179735891463957800317)
            ·
              refine ⟨8204692400959298984175119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21879179735891463957800317 8204692400959298984175119)
              ·
                refine ⟨12307038601438948476262679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8204692400959298984175119 12307038601438948476262679)
                ·
                  refine ⟨18460557902158422714394019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12307038601438948476262679 18460557902158422714394019)
                  ·
                    refine ⟨27690836853237634071591029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18460557902158422714394019 27690836853237634071591029)
                    ·
                      refine ⟨2596015954991028194211659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27690836853237634071591029 2596015954991028194211659)
                      ·
                        rfl

theorem cell23_5055723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 5].length) (baseStart_5055723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055723 prefixEnd_5055723 := by exact prefixLift 5055723
  have htrace : WordTrace (prefixWord ++ tailWord_5055723) baseStart_5055723 baseEnd_5055723 := by
    simpa [prefixWord, tailWord_5055723, baseEnd_5055723] using wordTrace_append hprefix tailTrace_5055723
  have hstable : (prefixWord ++ tailWord_5055723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055723).length < 2 ^ (prefixWord ++ tailWord_5055723).sum := by decide
  have hdescent : baseEnd_5055723 < baseStart_5055723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055743 : List Nat := [1, 1, 2, 2, 1, 7, 1, 8]
def baseStart_5055743 : Nat := 118140960795 + 5055743 * 2 ^ 59
def prefixEnd_5055743 : Nat := 4983230072969 + 3 ^ 40 * 5055743 * 2
def baseEnd_5055743 : Nat := 96149119429782152443021

theorem tailTrace_5055743 : CollatzResearch.WordTrace tailWord_5055743 prefixEnd_5055743 96149119429782152443021 := by
  unfold tailWord_5055743
  simp only [CollatzResearch.WordTrace]
  refine ⟨184398096122914038006571883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122932064081942692004381255 184398096122914038006571883)
  ·
    refine ⟨276597144184371057009857825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184398096122914038006571883 276597144184371057009857825)
    ·
      refine ⟨207447858138278292757393369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276597144184371057009857825 207447858138278292757393369)
      ·
        refine ⟨155585893603708719568045027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207447858138278292757393369 155585893603708719568045027)
        ·
          refine ⟨233378840405563079352067541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155585893603708719568045027 233378840405563079352067541)
          ·
            refine ⟨5469816572005384672314083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 233378840405563079352067541 5469816572005384672314083)
            ·
              refine ⟨8204724858008077008471125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5469816572005384672314083 8204724858008077008471125)
              ·
                refine ⟨96149119429782152443021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8204724858008077008471125 96149119429782152443021)
                ·
                  rfl

theorem cell23_5055743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 8].length) (baseStart_5055743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055743 prefixEnd_5055743 := by exact prefixLift 5055743
  have htrace : WordTrace (prefixWord ++ tailWord_5055743) baseStart_5055743 baseEnd_5055743 := by
    simpa [prefixWord, tailWord_5055743, baseEnd_5055743] using wordTrace_append hprefix tailTrace_5055743
  have hstable : (prefixWord ++ tailWord_5055743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055743).length < 2 ^ (prefixWord ++ tailWord_5055743).sum := by decide
  have hdescent : baseEnd_5055743 < baseStart_5055743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055770 : List Nat := [3, 1, 1, 3, 3, 1, 2, 2, 1, 3, 3]
def baseStart_5055770 : Nat := 118140960795 + 5055770 * 2 ^ 59
def prefixEnd_5055770 : Nat := 4983230072969 + 3 ^ 40 * 5055770 * 2
def baseEnd_5055770 : Nat := 2596040088581789510323943

theorem tailTrace_5055770 : CollatzResearch.WordTrace tailWord_5055770 prefixEnd_5055770 2596040088581789510323943 := by
  unfold tailWord_5055770
  simp only [CollatzResearch.WordTrace]
  refine ⟨46099770223454055404451191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122932720595877481078536509 46099770223454055404451191)
  ·
    refine ⟨69149655335181083106676787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46099770223454055404451191 69149655335181083106676787)
    ·
      refine ⟨103724483002771624660015181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69149655335181083106676787 103724483002771624660015181)
      ·
        refine ⟨38896681126039359247505693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103724483002771624660015181 38896681126039359247505693)
        ·
          refine ⟨14586255422264759717814635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38896681126039359247505693 14586255422264759717814635)
          ·
            refine ⟨21879383133397139576721953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14586255422264759717814635 21879383133397139576721953)
            ·
              refine ⟨16409537350047854682541465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21879383133397139576721953 16409537350047854682541465)
              ·
                refine ⟨12307153012535891011906099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16409537350047854682541465 12307153012535891011906099)
                ·
                  refine ⟨18460729518803836517859149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12307153012535891011906099 18460729518803836517859149)
                  ·
                    refine ⟨6922773569551438694197181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18460729518803836517859149 6922773569551438694197181)
                    ·
                      refine ⟨2596040088581789510323943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6922773569551438694197181 2596040088581789510323943)
                      ·
                        rfl

theorem cell23_5055770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_5055770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055770 prefixEnd_5055770 := by exact prefixLift 5055770
  have htrace : WordTrace (prefixWord ++ tailWord_5055770) baseStart_5055770 baseEnd_5055770 := by
    simpa [prefixWord, tailWord_5055770, baseEnd_5055770] using wordTrace_append hprefix tailTrace_5055770
  have hstable : (prefixWord ++ tailWord_5055770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055770).length < 2 ^ (prefixWord ++ tailWord_5055770).sum := by decide
  have hdescent : baseEnd_5055770 < baseStart_5055770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055804 : List Nat := [2, 2, 2, 2, 1, 4, 3, 1, 2, 1, 3]
def baseStart_5055804 : Nat := 118140960795 + 5055804 * 2 ^ 59
def prefixEnd_5055804 : Nat := 4983230072969 + 3 ^ 40 * 5055804 * 2
def baseEnd_5055804 : Nat := 2596057546924042377298787

theorem tailTrace_5055804 : CollatzResearch.WordTrace tailWord_5055804 prefixEnd_5055804 2596057546924042377298787 := by
  unfold tailWord_5055804
  simp only [CollatzResearch.WordTrace]
  refine ⟨92200160487846522712271233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122933547317128696949694977 92200160487846522712271233)
  ·
    refine ⟨69150120365884892034203425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92200160487846522712271233 69150120365884892034203425)
    ·
      refine ⟨51862590274413669025652569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69150120365884892034203425 51862590274413669025652569)
      ·
        refine ⟨38896942705810251769239427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51862590274413669025652569 38896942705810251769239427)
        ·
          refine ⟨58345414058715377653859141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38896942705810251769239427 58345414058715377653859141)
          ·
            refine ⟨10939765136009133310098589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58345414058715377653859141 10939765136009133310098589)
            ·
              refine ⟨4102411926003424991286971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10939765136009133310098589 4102411926003424991286971)
              ·
                refine ⟨6153617889005137486930457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4102411926003424991286971 6153617889005137486930457)
                ·
                  refine ⟨4615213416753853115197843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6153617889005137486930457 4615213416753853115197843)
                  ·
                    refine ⟨6922820125130779672796765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4615213416753853115197843 6922820125130779672796765)
                    ·
                      refine ⟨2596057546924042377298787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6922820125130779672796765 2596057546924042377298787)
                      ·
                        rfl

theorem cell23_5055804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_5055804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055804 prefixEnd_5055804 := by exact prefixLift 5055804
  have htrace : WordTrace (prefixWord ++ tailWord_5055804) baseStart_5055804 baseEnd_5055804 := by
    simpa [prefixWord, tailWord_5055804, baseEnd_5055804] using wordTrace_append hprefix tailTrace_5055804
  have hstable : (prefixWord ++ tailWord_5055804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055804).length < 2 ^ (prefixWord ++ tailWord_5055804).sum := by decide
  have hdescent : baseEnd_5055804 < baseStart_5055804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055813 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 2, 4, 3]
def baseStart_5055813 : Nat := 118140960795 + 5055813 * 2 ^ 59
def prefixEnd_5055813 : Nat := 4983230072969 + 3 ^ 40 * 5055813 * 2
def baseEnd_5055813 : Nat := 2596062168249932842086245

theorem tailTrace_5055813 : CollatzResearch.WordTrace tailWord_5055813 prefixEnd_5055813 2596062168249932842086245 := by
  unfold tailWord_5055813
  simp only [CollatzResearch.WordTrace]
  refine ⟨184400649232660439961620093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122933766155106959974413395 184400649232660439961620093)
  ·
    refine ⟨69150243462247664985607535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184400649232660439961620093 69150243462247664985607535)
    ·
      refine ⟨103725365193371497478411303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69150243462247664985607535 103725365193371497478411303)
      ·
        refine ⟨155588047790057246217616955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103725365193371497478411303 155588047790057246217616955)
        ·
          refine ⟨233382071685085869326425433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155588047790057246217616955 233382071685085869326425433)
          ·
            refine ⟨175036553763814401994819075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233382071685085869326425433 175036553763814401994819075)
            ·
              refine ⟨262554830645721602992228613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175036553763814401994819075 262554830645721602992228613)
              ·
                refine ⟨49229030746072800561042865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 262554830645721602992228613 49229030746072800561042865)
                ·
                  refine ⟨36921773059554600420782149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49229030746072800561042865 36921773059554600420782149)
                  ·
                    refine ⟨6922832448666487578896653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36921773059554600420782149 6922832448666487578896653)
                    ·
                      refine ⟨2596062168249932842086245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6922832448666487578896653 2596062168249932842086245)
                      ·
                        rfl

theorem cell23_5055813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 4, 3].length) (baseStart_5055813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055813 prefixEnd_5055813 := by exact prefixLift 5055813
  have htrace : WordTrace (prefixWord ++ tailWord_5055813) baseStart_5055813 baseEnd_5055813 := by
    simpa [prefixWord, tailWord_5055813, baseEnd_5055813] using wordTrace_append hprefix tailTrace_5055813
  have hstable : (prefixWord ++ tailWord_5055813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055813).length < 2 ^ (prefixWord ++ tailWord_5055813).sum := by decide
  have hdescent : baseEnd_5055813 < baseStart_5055813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055861 : List Nat := [1, 3, 4, 1, 3, 1, 1, 3, 2, 2, 2]
def baseStart_5055861 : Nat := 118140960795 + 5055861 * 2 ^ 59
def prefixEnd_5055861 : Nat := 4983230072969 + 3 ^ 40 * 5055861 * 2
def baseEnd_5055861 : Nat := 2596086815321348654286025

theorem tailTrace_5055861 : CollatzResearch.WordTrace tailWord_5055861 prefixEnd_5055861 2596086815321348654286025 := by
  unfold tailWord_5055861
  simp only [CollatzResearch.WordTrace]
  refine ⟨184402399936486544159367437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122934933290991029439578291 184402399936486544159367437)
  ·
    refine ⟨69150899976182454059762789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184402399936486544159367437 69150899976182454059762789)
    ·
      refine ⟨12965793745534210136205523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69150899976182454059762789 12965793745534210136205523)
      ·
        refine ⟨19448690618301315204308285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12965793745534210136205523 19448690618301315204308285)
        ·
          refine ⟨7293258981862993201615607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19448690618301315204308285 7293258981862993201615607)
          ·
            refine ⟨10939888472794489802423411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7293258981862993201615607 10939888472794489802423411)
            ·
              refine ⟨16409832709191734703635117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10939888472794489802423411 16409832709191734703635117)
              ·
                refine ⟨6153687265946900513863169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16409832709191734703635117 6153687265946900513863169)
                ·
                  refine ⟨4615265449460175385397377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6153687265946900513863169 4615265449460175385397377)
                  ·
                    refine ⟨3461449087095131539048033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4615265449460175385397377 3461449087095131539048033)
                    ·
                      refine ⟨2596086815321348654286025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3461449087095131539048033 2596086815321348654286025)
                      ·
                        rfl

theorem cell23_5055861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_5055861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055861 prefixEnd_5055861 := by exact prefixLift 5055861
  have htrace : WordTrace (prefixWord ++ tailWord_5055861) baseStart_5055861 baseEnd_5055861 := by
    simpa [prefixWord, tailWord_5055861, baseEnd_5055861] using wordTrace_append hprefix tailTrace_5055861
  have hstable : (prefixWord ++ tailWord_5055861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055861).length < 2 ^ (prefixWord ++ tailWord_5055861).sum := by decide
  have hdescent : baseEnd_5055861 < baseStart_5055861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055863 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 4, 5]
def baseStart_5055863 : Nat := 118140960795 + 5055863 * 2 ^ 59
def prefixEnd_5055863 : Nat := 4983230072969 + 3 ^ 40 * 5055863 * 2
def baseEnd_5055863 : Nat := 865362614094219215487005

theorem tailTrace_5055863 : CollatzResearch.WordTrace tailWord_5055863 prefixEnd_5055863 865362614094219215487005 := by
  unfold tailWord_5055863
  simp only [CollatzResearch.WordTrace]
  refine ⟨184402472882479298500940243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122934981921652865667293495 184402472882479298500940243)
  ·
    refine ⟨276603709323718947751410365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184402472882479298500940243 276603709323718947751410365)
    ·
      refine ⟨103726390996394605406778887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 276603709323718947751410365 103726390996394605406778887)
      ·
        refine ⟨155589586494591908110168331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103726390996394605406778887 155589586494591908110168331)
        ·
          refine ⟨233384379741887862165252497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155589586494591908110168331 233384379741887862165252497)
          ·
            refine ⟨175038284806415896623939373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233384379741887862165252497 175038284806415896623939373)
            ·
              refine ⟨65639356802405961233977265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175038284806415896623939373 65639356802405961233977265)
              ·
                refine ⟨49229517601804470925482949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65639356802405961233977265 49229517601804470925482949)
                ·
                  refine ⟨9230534550338338298528053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49229517601804470925482949 9230534550338338298528053)
                  ·
                    refine ⟨865362614094219215487005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9230534550338338298528053 865362614094219215487005)
                    ·
                      rfl

theorem cell23_5055863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 5].length) (baseStart_5055863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055863 prefixEnd_5055863 := by exact prefixLift 5055863
  have htrace : WordTrace (prefixWord ++ tailWord_5055863) baseStart_5055863 baseEnd_5055863 := by
    simpa [prefixWord, tailWord_5055863, baseEnd_5055863] using wordTrace_append hprefix tailTrace_5055863
  have hstable : (prefixWord ++ tailWord_5055863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055863).length < 2 ^ (prefixWord ++ tailWord_5055863).sum := by decide
  have hdescent : baseEnd_5055863 < baseStart_5055863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055880 : List Nat := [2, 1, 3, 3, 1, 2, 1, 3, 2, 5]
def baseStart_5055880 : Nat := 118140960795 + 5055880 * 2 ^ 59
def prefixEnd_5055880 : Nat := 4983230072969 + 3 ^ 40 * 5055880 * 2
def baseEnd_5055880 : Nat := 865365523817928026649479

theorem tailTrace_5055880 : CollatzResearch.WordTrace tailWord_5055880 prefixEnd_5055880 865365523817928026649479 := by
  unfold tailWord_5055880
  simp only [CollatzResearch.WordTrace]
  refine ⟨92201546461708855202154547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122935395282278473602872729 92201546461708855202154547)
  ·
    refine ⟨138302319692563282803231821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92201546461708855202154547 138302319692563282803231821)
    ·
      refine ⟨51863369884711231051211933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138302319692563282803231821 51863369884711231051211933)
      ·
        refine ⟨19448763706766711644204475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51863369884711231051211933 19448763706766711644204475)
        ·
          refine ⟨29173145560150067466306713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19448763706766711644204475 29173145560150067466306713)
          ·
            refine ⟨21879859170112550599730035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29173145560150067466306713 21879859170112550599730035)
            ·
              refine ⟨32819788755168825899595053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21879859170112550599730035 32819788755168825899595053)
              ·
                refine ⟨12307420783188309712348145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32819788755168825899595053 12307420783188309712348145)
                ·
                  refine ⟨9230565587391232284261109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12307420783188309712348145 9230565587391232284261109)
                  ·
                    refine ⟨865365523817928026649479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9230565587391232284261109 865365523817928026649479)
                    ·
                      rfl

theorem cell23_5055880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_5055880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055880 prefixEnd_5055880 := by exact prefixLift 5055880
  have htrace : WordTrace (prefixWord ++ tailWord_5055880) baseStart_5055880 baseEnd_5055880 := by
    simpa [prefixWord, tailWord_5055880, baseEnd_5055880] using wordTrace_append hprefix tailTrace_5055880
  have hstable : (prefixWord ++ tailWord_5055880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055880).length < 2 ^ (prefixWord ++ tailWord_5055880).sum := by decide
  have hdescent : baseEnd_5055880 < baseStart_5055880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055913 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 4, 4, 4]
def baseStart_5055913 : Nat := 118140960795 + 5055913 * 2 ^ 59
def prefixEnd_5055913 : Nat := 4983230072969 + 3 ^ 40 * 5055913 * 2
def baseEnd_5055913 : Nat := 2596113516315382450835785

theorem tailTrace_5055913 : CollatzResearch.WordTrace tailWord_5055913 prefixEnd_5055913 2596113516315382450835785 := by
  unfold tailWord_5055913
  simp only [CollatzResearch.WordTrace]
  refine ⟨184404296532298157040260393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122936197688198771360173595 184404296532298157040260393)
  ·
    refine ⟨138303222399223617780195295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184404296532298157040260393 138303222399223617780195295)
    ·
      refine ⟨207454833598835426670292943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138303222399223617780195295 207454833598835426670292943)
      ·
        refine ⟨311182250398253140005439415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207454833598835426670292943 311182250398253140005439415)
        ·
          refine ⟨466773375597379710008159123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311182250398253140005439415 466773375597379710008159123)
          ·
            refine ⟨700160063396069565012238685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466773375597379710008159123 700160063396069565012238685)
            ·
              refine ⟨262560023773526086879589507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 700160063396069565012238685 262560023773526086879589507)
              ·
                refine ⟨393840035660289130319384261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262560023773526086879589507 393840035660289130319384261)
                ·
                  refine ⟨73845006686304211934884549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 393840035660289130319384261 73845006686304211934884549)
                  ·
                    refine ⟨13845938753682039737790853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73845006686304211934884549 13845938753682039737790853)
                    ·
                      refine ⟨2596113516315382450835785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13845938753682039737790853 2596113516315382450835785)
                      ·
                        rfl

theorem cell23_5055913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 4, 4].length) (baseStart_5055913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055913 prefixEnd_5055913 := by exact prefixLift 5055913
  have htrace : WordTrace (prefixWord ++ tailWord_5055913) baseStart_5055913 baseEnd_5055913 := by
    simpa [prefixWord, tailWord_5055913, baseEnd_5055913] using wordTrace_append hprefix tailTrace_5055913
  have hstable : (prefixWord ++ tailWord_5055913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055913).length < 2 ^ (prefixWord ++ tailWord_5055913).sum := by decide
  have hdescent : baseEnd_5055913 < baseStart_5055913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055944 : List Nat := [2, 1, 3, 1, 3, 1, 4, 3, 1, 4]
def baseStart_5055944 : Nat := 118140960795 + 5055944 * 2 ^ 59
def prefixEnd_5055944 : Nat := 4983230072969 + 3 ^ 40 * 5055944 * 2
def baseEnd_5055944 : Nat := 865376478071890609849381

theorem tailTrace_5055944 : CollatzResearch.WordTrace tailWord_5055944 prefixEnd_5055944 865376478071890609849381 := by
  unfold tailWord_5055944
  simp only [CollatzResearch.WordTrace]
  refine ⟨92202713597592924667319443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122936951463457232889759257 92202713597592924667319443)
  ·
    refine ⟨138304070396389387000979165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92202713597592924667319443 138304070396389387000979165)
    ·
      refine ⟨51864026398646020125367187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138304070396389387000979165 51864026398646020125367187)
      ·
        refine ⟨77796039597969030188050781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51864026398646020125367187 77796039597969030188050781)
        ·
          refine ⟨29173514849238386320519043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77796039597969030188050781 29173514849238386320519043)
          ·
            refine ⟨43760272273857579480778565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29173514849238386320519043 43760272273857579480778565)
            ·
              refine ⟨8205051051348296152645981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43760272273857579480778565 8205051051348296152645981)
              ·
                refine ⟨3076894144255611057242243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8205051051348296152645981 3076894144255611057242243)
                ·
                  refine ⟨4615341216383416585863365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3076894144255611057242243 4615341216383416585863365)
                  ·
                    refine ⟨865376478071890609849381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4615341216383416585863365 865376478071890609849381)
                    ·
                      rfl

theorem cell23_5055944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_5055944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055944 prefixEnd_5055944 := by exact prefixLift 5055944
  have htrace : WordTrace (prefixWord ++ tailWord_5055944) baseStart_5055944 baseEnd_5055944 := by
    simpa [prefixWord, tailWord_5055944, baseEnd_5055944] using wordTrace_append hprefix tailTrace_5055944
  have hstable : (prefixWord ++ tailWord_5055944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055944).length < 2 ^ (prefixWord ++ tailWord_5055944).sum := by decide
  have hdescent : baseEnd_5055944 < baseStart_5055944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5055963 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 5]
def baseStart_5055963 : Nat := 118140960795 + 5055963 * 2 ^ 59
def prefixEnd_5055963 : Nat := 4983230072969 + 3 ^ 40 * 5055963 * 2
def baseEnd_5055963 : Nat := 2596139190348107255210555

theorem tailTrace_5055963 : CollatzResearch.WordTrace tailWord_5055963 prefixEnd_5055963 2596139190348107255210555 := by
  unfold tailWord_5055963
  simp only [CollatzResearch.WordTrace]
  refine ⟨184406120182117015579580543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122937413454744677053053695 184406120182117015579580543)
  ·
    refine ⟨276609180273175523369370815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184406120182117015579580543 276609180273175523369370815)
    ·
      refine ⟨414913770409763285054056223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276609180273175523369370815 414913770409763285054056223)
      ·
        refine ⟨622370655614644927581084335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414913770409763285054056223 622370655614644927581084335)
        ·
          refine ⟨933555983421967391371626503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 622370655614644927581084335 933555983421967391371626503)
          ·
            refine ⟨1400333975132951087057439755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 933555983421967391371626503 1400333975132951087057439755)
            ·
              refine ⟨2100500962699426630586159633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1400333975132951087057439755 2100500962699426630586159633)
              ·
                refine ⟨1575375722024569972939619725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2100500962699426630586159633 1575375722024569972939619725)
                ·
                  refine ⟨590765895759213739852357397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1575375722024569972939619725 590765895759213739852357397)
                  ·
                    refine ⟨27692151363713144055579253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 590765895759213739852357397 27692151363713144055579253)
                    ·
                      refine ⟨2596139190348107255210555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27692151363713144055579253 2596139190348107255210555)
                      ·
                        rfl

theorem cell23_5055963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 5].length) (baseStart_5055963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5055963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5055963 prefixEnd_5055963 := by exact prefixLift 5055963
  have htrace : WordTrace (prefixWord ++ tailWord_5055963) baseStart_5055963 baseEnd_5055963 := by
    simpa [prefixWord, tailWord_5055963, baseEnd_5055963] using wordTrace_append hprefix tailTrace_5055963
  have hstable : (prefixWord ++ tailWord_5055963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5055963).length < 2 ^ (prefixWord ++ tailWord_5055963).sum := by decide
  have hdescent : baseEnd_5055963 < baseStart_5055963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5055963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056017 : List Nat := [1, 2, 2, 1, 1, 2, 4, 4, 2, 4]
def baseStart_5056017 : Nat := 118140960795 + 5056017 * 2 ^ 59
def prefixEnd_5056017 : Nat := 4983230072969 + 3 ^ 40 * 5056017 * 2
def baseEnd_5056017 : Nat := 865388972767816681311769

theorem tailTrace_5056017 : CollatzResearch.WordTrace tailWord_5056017 prefixEnd_5056017 865388972767816681311769 := by
  unfold tailWord_5056017
  simp only [CollatzResearch.WordTrace]
  refine ⟨184408089723921382802046305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122938726482614255201364203 184408089723921382802046305)
  ·
    refine ⟨138306067292941037101534729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184408089723921382802046305 138306067292941037101534729)
    ·
      refine ⟨103729550469705777826151047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138306067292941037101534729 103729550469705777826151047)
      ·
        refine ⟨155594325704558666739226571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103729550469705777826151047 155594325704558666739226571)
        ·
          refine ⟨233391488556838000108839857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155594325704558666739226571 233391488556838000108839857)
          ·
            refine ⟨175043616417628500081629893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233391488556838000108839857 175043616417628500081629893)
            ·
              refine ⟨32820678078305343765305605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175043616417628500081629893 32820678078305343765305605)
              ·
                refine ⟨6153877139682251955994801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32820678078305343765305605 6153877139682251955994801)
                ·
                  refine ⟨4615407854761688966996101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6153877139682251955994801 4615407854761688966996101)
                  ·
                    refine ⟨865388972767816681311769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4615407854761688966996101 865388972767816681311769)
                    ·
                      rfl

theorem cell23_5056017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2, 4].length) (baseStart_5056017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056017 prefixEnd_5056017 := by exact prefixLift 5056017
  have htrace : WordTrace (prefixWord ++ tailWord_5056017) baseStart_5056017 baseEnd_5056017 := by
    simpa [prefixWord, tailWord_5056017, baseEnd_5056017] using wordTrace_append hprefix tailTrace_5056017
  have hstable : (prefixWord ++ tailWord_5056017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056017).length < 2 ^ (prefixWord ++ tailWord_5056017).sum := by decide
  have hdescent : baseEnd_5056017 < baseStart_5056017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056057 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 3, 3, 3]
def baseStart_5056057 : Nat := 118140960795 + 5056057 * 2 ^ 59
def prefixEnd_5056057 : Nat := 4983230072969 + 3 ^ 40 * 5056057 * 2
def baseEnd_5056057 : Nat := 2596187457529629887435123

theorem tailTrace_5056057 : CollatzResearch.WordTrace tailWord_5056057 prefixEnd_5056057 2596187457529629887435123 := by
  unfold tailWord_5056057
  simp only [CollatzResearch.WordTrace]
  refine ⟨184409548643776469633502425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122939699095850979755668283 184409548643776469633502425)
  ·
    refine ⟨138307161482832352225126819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184409548643776469633502425 138307161482832352225126819)
    ·
      refine ⟨207460742224248528337690229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138307161482832352225126819 207460742224248528337690229)
      ·
        refine ⟨19449444583523299531658459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 207460742224248528337690229 19449444583523299531658459)
        ·
          refine ⟨29174166875284949297487689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19449444583523299531658459 29174166875284949297487689)
          ·
            refine ⟨21880625156463711973115767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29174166875284949297487689 21880625156463711973115767)
            ·
              refine ⟨32820937734695567959673651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21880625156463711973115767 32820937734695567959673651)
              ·
                refine ⟨49231406602043351939510477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32820937734695567959673651 49231406602043351939510477)
                ·
                  refine ⟨18461777475766256977316429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49231406602043351939510477 18461777475766256977316429)
                  ·
                    refine ⟨6923166553412346366493661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18461777475766256977316429 6923166553412346366493661)
                    ·
                      refine ⟨2596187457529629887435123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6923166553412346366493661 2596187457529629887435123)
                      ·
                        rfl

theorem cell23_5056057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_5056057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056057 prefixEnd_5056057 := by exact prefixLift 5056057
  have htrace : WordTrace (prefixWord ++ tailWord_5056057) baseStart_5056057 baseEnd_5056057 := by
    simpa [prefixWord, tailWord_5056057, baseEnd_5056057] using wordTrace_append hprefix tailTrace_5056057
  have hstable : (prefixWord ++ tailWord_5056057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056057).length < 2 ^ (prefixWord ++ tailWord_5056057).sum := by decide
  have hdescent : baseEnd_5056057 < baseStart_5056057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056061 : List Nat := [1, 4, 1, 3, 4, 1, 1, 1, 1, 1, 5]
def baseStart_5056061 : Nat := 118140960795 + 5056061 * 2 ^ 59
def prefixEnd_5056061 : Nat := 4983230072969 + 3 ^ 40 * 5056061 * 2
def baseEnd_5056061 : Nat := 2596189511452247871785105

theorem tailTrace_5056061 : CollatzResearch.WordTrace tailWord_5056061 prefixEnd_5056061 2596189511452247871785105 := by
  unfold tailWord_5056061
  simp only [CollatzResearch.WordTrace]
  refine ⟨184409694535761978316648037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122939796357174652211098691 184409694535761978316648037)
  ·
    refine ⟨34576817725455370934371507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184409694535761978316648037 34576817725455370934371507)
    ·
      refine ⟨51865226588183056401557261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34576817725455370934371507 51865226588183056401557261)
      ·
        refine ⟨19449459970568646150583973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51865226588183056401557261 19449459970568646150583973)
        ·
          refine ⟨3646773744481621153234495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19449459970568646150583973 3646773744481621153234495)
          ·
            refine ⟨5470160616722431729851743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3646773744481621153234495 5470160616722431729851743)
            ·
              refine ⟨8205240925083647594777615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5470160616722431729851743 8205240925083647594777615)
              ·
                refine ⟨12307861387625471392166423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8205240925083647594777615 12307861387625471392166423)
                ·
                  refine ⟨18461792081438207088249635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12307861387625471392166423 18461792081438207088249635)
                  ·
                    refine ⟨27692688122157310632374453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18461792081438207088249635 27692688122157310632374453)
                    ·
                      refine ⟨2596189511452247871785105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27692688122157310632374453 2596189511452247871785105)
                      ·
                        rfl

theorem cell23_5056061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_5056061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056061 prefixEnd_5056061 := by exact prefixLift 5056061
  have htrace : WordTrace (prefixWord ++ tailWord_5056061) baseStart_5056061 baseEnd_5056061 := by
    simpa [prefixWord, tailWord_5056061, baseEnd_5056061] using wordTrace_append hprefix tailTrace_5056061
  have hstable : (prefixWord ++ tailWord_5056061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056061).length < 2 ^ (prefixWord ++ tailWord_5056061).sum := by decide
  have hdescent : baseEnd_5056061 < baseStart_5056061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056080 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 4]
def baseStart_5056080 : Nat := 118140960795 + 5056080 * 2 ^ 59
def prefixEnd_5056080 : Nat := 4983230072969 + 3 ^ 40 * 5056080 * 2
def baseEnd_5056080 : Nat := 2596199267584683297447517

theorem tailTrace_5056080 : CollatzResearch.WordTrace tailWord_5056080 prefixEnd_5056080 2596199267584683297447517 := by
  unfold tailWord_5056080
  simp only [CollatzResearch.WordTrace]
  refine ⟨92205193761346572280794847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122940258348462096374393129 92205193761346572280794847)
  ·
    refine ⟨138307790642019858421192271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92205193761346572280794847 138307790642019858421192271)
    ·
      refine ⟨207461685963029787631788407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138307790642019858421192271 207461685963029787631788407)
      ·
        refine ⟨311192528944544681447682611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207461685963029787631788407 311192528944544681447682611)
        ·
          refine ⟨466788793416817022171523917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311192528944544681447682611 466788793416817022171523917)
          ·
            refine ⟨175045797531306383314321469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 466788793416817022171523917 175045797531306383314321469)
            ·
              refine ⟨65642174074239893742870551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175045797531306383314321469 65642174074239893742870551)
              ·
                refine ⟨98463261111359840614305827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65642174074239893742870551 98463261111359840614305827)
                ·
                  refine ⟨147694891667039760921458741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98463261111359840614305827 147694891667039760921458741)
                  ·
                    refine ⟨13846396093784977586386757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 147694891667039760921458741 13846396093784977586386757)
                    ·
                      refine ⟨2596199267584683297447517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13846396093784977586386757 2596199267584683297447517)
                      ·
                        rfl

theorem cell23_5056080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 4].length) (baseStart_5056080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056080 prefixEnd_5056080 := by exact prefixLift 5056080
  have htrace : WordTrace (prefixWord ++ tailWord_5056080) baseStart_5056080 baseEnd_5056080 := by
    simpa [prefixWord, tailWord_5056080, baseEnd_5056080] using wordTrace_append hprefix tailTrace_5056080
  have hstable : (prefixWord ++ tailWord_5056080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056080).length < 2 ^ (prefixWord ++ tailWord_5056080).sum := by decide
  have hdescent : baseEnd_5056080 < baseStart_5056080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056084 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 5, 3, 2]
def baseStart_5056084 : Nat := 118140960795 + 5056084 * 2 ^ 59
def prefixEnd_5056084 : Nat := 4983230072969 + 3 ^ 40 * 5056084 * 2
def baseEnd_5056084 : Nat := 2596201321507301281797499

theorem tailTrace_5056084 : CollatzResearch.WordTrace tailWord_5056084 prefixEnd_5056084 2596201321507301281797499 := by
  unfold tailWord_5056084
  simp only [CollatzResearch.WordTrace]
  refine ⟨92205266707339326622367653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122940355609785768829823537 92205266707339326622367653)
  ·
    refine ⟨17288487507626123741693935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92205266707339326622367653 17288487507626123741693935)
    ·
      refine ⟨25932731261439185612540903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17288487507626123741693935 25932731261439185612540903)
      ·
        refine ⟨38899096892158778418811355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25932731261439185612540903 38899096892158778418811355)
        ·
          refine ⟨58348645338238167628217033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38899096892158778418811355 58348645338238167628217033)
          ·
            refine ⟨43761484003678625721162775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58348645338238167628217033 43761484003678625721162775)
            ·
              refine ⟨65642226005517938581744163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43761484003678625721162775 65642226005517938581744163)
              ·
                refine ⟨98463339008276907872616245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65642226005517938581744163 98463339008276907872616245)
                ·
                  refine ⟨9230938032025960113057773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98463339008276907872616245 9230938032025960113057773)
                  ·
                    refine ⟨3461601762009735042396665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9230938032025960113057773 3461601762009735042396665)
                    ·
                      refine ⟨2596201321507301281797499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3461601762009735042396665 2596201321507301281797499)
                      ·
                        rfl

theorem cell23_5056084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_5056084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056084 prefixEnd_5056084 := by exact prefixLift 5056084
  have htrace : WordTrace (prefixWord ++ tailWord_5056084) baseStart_5056084 baseEnd_5056084 := by
    simpa [prefixWord, tailWord_5056084, baseEnd_5056084] using wordTrace_append hprefix tailTrace_5056084
  have hstable : (prefixWord ++ tailWord_5056084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056084).length < 2 ^ (prefixWord ++ tailWord_5056084).sum := by decide
  have hdescent : baseEnd_5056084 < baseStart_5056084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056118 : List Nat := [5, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2]
def baseStart_5056118 : Nat := 118140960795 + 5056118 * 2 ^ 59
def prefixEnd_5056118 : Nat := 4983230072969 + 3 ^ 40 * 5056118 * 2
def baseEnd_5056118 : Nat := 2596218779849554148772343

theorem tailTrace_5056118 : CollatzResearch.WordTrace tailWord_5056118 prefixEnd_5056118 2596218779849554148772343 := by
  unfold tailWord_5056118
  simp only [CollatzResearch.WordTrace]
  refine ⟨11525735843534717315717063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122941182331036984700982005 11525735843534717315717063)
  ·
    refine ⟨17288603765302075973575595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11525735843534717315717063 17288603765302075973575595)
    ·
      refine ⟨25932905647953113960363393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17288603765302075973575595 25932905647953113960363393)
      ·
        refine ⟨19449679235964835470272545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25932905647953113960363393 19449679235964835470272545)
        ·
          refine ⟨14587259426973626602704409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19449679235964835470272545 14587259426973626602704409)
          ·
            refine ⟨10940444570230219952028307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14587259426973626602704409 10940444570230219952028307)
            ·
              refine ⟨16410666855345329928042461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10940444570230219952028307 16410666855345329928042461)
              ·
                refine ⟨6154000070754498723015923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16410666855345329928042461 6154000070754498723015923)
                ·
                  refine ⟨9231000106131748084523885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6154000070754498723015923 9231000106131748084523885)
                  ·
                    refine ⟨3461625039799405531696457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9231000106131748084523885 3461625039799405531696457)
                    ·
                      refine ⟨2596218779849554148772343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3461625039799405531696457 2596218779849554148772343)
                      ·
                        rfl

theorem cell23_5056118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_5056118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056118 prefixEnd_5056118 := by exact prefixLift 5056118
  have htrace : WordTrace (prefixWord ++ tailWord_5056118) baseStart_5056118 baseEnd_5056118 := by
    simpa [prefixWord, tailWord_5056118, baseEnd_5056118] using wordTrace_append hprefix tailTrace_5056118
  have hstable : (prefixWord ++ tailWord_5056118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056118).length < 2 ^ (prefixWord ++ tailWord_5056118).sum := by decide
  have hdescent : baseEnd_5056118 < baseStart_5056118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056168 : List Nat := [2, 1, 7, 1, 1, 1, 1, 1, 2, 1, 5]
def baseStart_5056168 : Nat := 118140960795 + 5056168 * 2 ^ 59
def prefixEnd_5056168 : Nat := 4983230072969 + 3 ^ 40 * 5056168 * 2
def baseEnd_5056168 : Nat := 2596244453882278953147113

theorem tailTrace_5056168 : CollatzResearch.WordTrace tailWord_5056168 prefixEnd_5056168 2596244453882278953147113 := by
  unfold tailWord_5056168
  simp only [CollatzResearch.WordTrace]
  refine ⟨92206798573187167795396579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122942398097582890393862105 92206798573187167795396579)
  ·
    refine ⟨138310197859780751693094869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92206798573187167795396579 138310197859780751693094869)
    ·
      refine ⟨3241645262338611367806911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 138310197859780751693094869 3241645262338611367806911)
      ·
        refine ⟨4862467893507917051710367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3241645262338611367806911 4862467893507917051710367)
        ·
          refine ⟨7293701840261875577565551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4862467893507917051710367 7293701840261875577565551)
          ·
            refine ⟨10940552760392813366348327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7293701840261875577565551 10940552760392813366348327)
            ·
              refine ⟨16410829140589220049522491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10940552760392813366348327 16410829140589220049522491)
              ·
                refine ⟨24616243710883830074283737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16410829140589220049522491 24616243710883830074283737)
                ·
                  refine ⟨18462182783162872555712803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24616243710883830074283737 18462182783162872555712803)
                  ·
                    refine ⟨27693274174744308833569205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18462182783162872555712803 27693274174744308833569205)
                    ·
                      refine ⟨2596244453882278953147113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27693274174744308833569205 2596244453882278953147113)
                      ·
                        rfl

theorem cell23_5056168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_5056168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056168 prefixEnd_5056168 := by exact prefixLift 5056168
  have htrace : WordTrace (prefixWord ++ tailWord_5056168) baseStart_5056168 baseEnd_5056168 := by
    simpa [prefixWord, tailWord_5056168, baseEnd_5056168] using wordTrace_append hprefix tailTrace_5056168
  have hstable : (prefixWord ++ tailWord_5056168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056168).length < 2 ^ (prefixWord ++ tailWord_5056168).sum := by decide
  have hdescent : baseEnd_5056168 < baseStart_5056168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056207 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 3, 4, 3]
def baseStart_5056207 : Nat := 118140960795 + 5056207 * 2 ^ 59
def prefixEnd_5056207 : Nat := 4983230072969 + 3 ^ 40 * 5056207 * 2
def baseEnd_5056207 : Nat := 2596264479627804300559433

theorem tailTrace_5056207 : CollatzResearch.WordTrace tailWord_5056207 prefixEnd_5056207 2596264479627804300559433 := by
  unfold tailWord_5056207
  simp only [CollatzResearch.WordTrace]
  refine ⟨184415019593233045251462875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122943346395488696834308583 184415019593233045251462875)
  ·
    refine ⟨276622529389849567877194313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184415019593233045251462875 276622529389849567877194313)
    ·
      refine ⟨207466897042387175907895735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276622529389849567877194313 207466897042387175907895735)
      ·
        refine ⟨311200345563580763861843603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207466897042387175907895735 311200345563580763861843603)
        ·
          refine ⟨466800518345371145792765405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311200345563580763861843603 466800518345371145792765405)
          ·
            refine ⟨175050194379514179672287027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 466800518345371145792765405 175050194379514179672287027)
            ·
              refine ⟨262575291569271269508430541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175050194379514179672287027 262575291569271269508430541)
              ·
                refine ⟨98465734338476726065661453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 262575291569271269508430541 98465734338476726065661453)
                ·
                  refine ⟨36924650376928772274623045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98465734338476726065661453 36924650376928772274623045)
                  ·
                    refine ⟨6923371945674144801491821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36924650376928772274623045 6923371945674144801491821)
                    ·
                      refine ⟨2596264479627804300559433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6923371945674144801491821 2596264479627804300559433)
                      ·
                        rfl

theorem cell23_5056207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 4, 3].length) (baseStart_5056207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056207 prefixEnd_5056207 := by exact prefixLift 5056207
  have htrace : WordTrace (prefixWord ++ tailWord_5056207) baseStart_5056207 baseEnd_5056207 := by
    simpa [prefixWord, tailWord_5056207, baseEnd_5056207] using wordTrace_append hprefix tailTrace_5056207
  have hstable : (prefixWord ++ tailWord_5056207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056207).length < 2 ^ (prefixWord ++ tailWord_5056207).sum := by decide
  have hdescent : baseEnd_5056207 < baseStart_5056207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056224 : List Nat := [2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 3]
def baseStart_5056224 : Nat := 118140960795 + 5056224 * 2 ^ 59
def prefixEnd_5056224 : Nat := 4983230072969 + 3 ^ 40 * 5056224 * 2
def baseEnd_5056224 : Nat := 2596273208798930734046855

theorem tailTrace_5056224 : CollatzResearch.WordTrace tailWord_5056224 prefixEnd_5056224 2596273208798930734046855 := by
  unfold tailWord_5056224
  simp only [CollatzResearch.WordTrace]
  refine ⟨92207819817085728577415863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122943759756114304769887817 92207819817085728577415863)
  ·
    refine ⟨138311729725628592866123795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92207819817085728577415863 138311729725628592866123795)
    ·
      refine ⟨207467594588442889299185693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138311729725628592866123795 207467594588442889299185693)
      ·
        refine ⟨77800347970666083487194635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207467594588442889299185693 77800347970666083487194635)
        ·
          refine ⟨116700521955999125230791953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77800347970666083487194635 116700521955999125230791953)
          ·
            refine ⟨87525391466999343923093965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116700521955999125230791953 87525391466999343923093965)
            ·
              refine ⟨32822021800124753971160237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87525391466999343923093965 32822021800124753971160237)
              ·
                refine ⟨12308258175046782739185089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32822021800124753971160237 12308258175046782739185089)
                ·
                  refine ⟨9231193631285087054388817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12308258175046782739185089 9231193631285087054388817)
                  ·
                    refine ⟨6923395223463815290791613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9231193631285087054388817 6923395223463815290791613)
                    ·
                      refine ⟨2596273208798930734046855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6923395223463815290791613 2596273208798930734046855)
                      ·
                        rfl

theorem cell23_5056224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_5056224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056224 prefixEnd_5056224 := by exact prefixLift 5056224
  have htrace : WordTrace (prefixWord ++ tailWord_5056224) baseStart_5056224 baseEnd_5056224 := by
    simpa [prefixWord, tailWord_5056224, baseEnd_5056224] using wordTrace_append hprefix tailTrace_5056224
  have hstable : (prefixWord ++ tailWord_5056224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056224).length < 2 ^ (prefixWord ++ tailWord_5056224).sum := by decide
  have hdescent : baseEnd_5056224 < baseStart_5056224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056269 : List Nat := [1, 7, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_5056269 : Nat := 118140960795 + 5056269 * 2 ^ 59
def prefixEnd_5056269 : Nat := 4983230072969 + 3 ^ 40 * 5056269 * 2
def baseEnd_5056269 : Nat := 865432105142794352661383

theorem tailTrace_5056269 : CollatzResearch.WordTrace tailWord_5056269 prefixEnd_5056269 865432105142794352661383 := by
  unfold tailWord_5056269
  simp only [CollatzResearch.WordTrace]
  refine ⟨184417280919008429840219861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122944853946005619893479907 184417280919008429840219861)
  ·
    refine ⟨4322280021539260074380153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 184417280919008429840219861 4322280021539260074380153)
    ·
      refine ⟨3241710016154445055785115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4322280021539260074380153 3241710016154445055785115)
      ·
        refine ⟨4862565024231667583677673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3241710016154445055785115 4862565024231667583677673)
        ·
          refine ⟨3646923768173750687758255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4862565024231667583677673 3646923768173750687758255)
          ·
            refine ⟨5470385652260626031637383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3646923768173750687758255 5470385652260626031637383)
            ·
              refine ⟨8205578478390939047456075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5470385652260626031637383 8205578478390939047456075)
              ·
                refine ⟨12308367717586408571184113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8205578478390939047456075 12308367717586408571184113)
                ·
                  refine ⟨9231275788189806428388085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12308367717586408571184113 9231275788189806428388085)
                  ·
                    refine ⟨865432105142794352661383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9231275788189806428388085 865432105142794352661383)
                    ·
                      rfl

theorem cell23_5056269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_5056269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056269 prefixEnd_5056269 := by exact prefixLift 5056269
  have htrace : WordTrace (prefixWord ++ tailWord_5056269) baseStart_5056269 baseEnd_5056269 := by
    simpa [prefixWord, tailWord_5056269, baseEnd_5056269] using wordTrace_append hprefix tailTrace_5056269
  have hstable : (prefixWord ++ tailWord_5056269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056269).length < 2 ^ (prefixWord ++ tailWord_5056269).sum := by decide
  have hdescent : baseEnd_5056269 < baseStart_5056269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056291 : List Nat := [1, 1, 1, 4, 2, 1, 6, 1, 1, 5]
def baseStart_5056291 : Nat := 118140960795 + 5056291 * 2 ^ 59
def prefixEnd_5056291 : Nat := 4983230072969 + 3 ^ 40 * 5056291 * 2
def baseEnd_5056291 : Nat := 865435870667593990636349

theorem tailTrace_5056291 : CollatzResearch.WordTrace tailWord_5056291 prefixEnd_5056291 865435870667593990636349 := by
  unfold tailWord_5056291
  simp only [CollatzResearch.WordTrace]
  refine ⟨184418083324928727597520727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122945388883285818398347151 184418083324928727597520727)
  ·
    refine ⟨276627124987393091396281091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184418083324928727597520727 276627124987393091396281091)
    ·
      refine ⟨414940687481089637094421637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276627124987393091396281091 414940687481089637094421637)
      ·
        refine ⟨77801378902704306955204057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 414940687481089637094421637 77801378902704306955204057)
        ·
          refine ⟨58351034177028230216403043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77801378902704306955204057 58351034177028230216403043)
          ·
            refine ⟨87526551265542345324604565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58351034177028230216403043 87526551265542345324604565)
            ·
              refine ⟨4102807090572297437090839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 87526551265542345324604565 4102807090572297437090839)
              ·
                refine ⟨6154210635858446155636259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4102807090572297437090839 6154210635858446155636259)
                ·
                  refine ⟨9231315953787669233454389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6154210635858446155636259 9231315953787669233454389)
                  ·
                    refine ⟨865435870667593990636349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9231315953787669233454389 865435870667593990636349)
                    ·
                      rfl

theorem cell23_5056291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 1, 5].length) (baseStart_5056291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056291 prefixEnd_5056291 := by exact prefixLift 5056291
  have htrace : WordTrace (prefixWord ++ tailWord_5056291) baseStart_5056291 baseEnd_5056291 := by
    simpa [prefixWord, tailWord_5056291, baseEnd_5056291] using wordTrace_append hprefix tailTrace_5056291
  have hstable : (prefixWord ++ tailWord_5056291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056291).length < 2 ^ (prefixWord ++ tailWord_5056291).sum := by decide
  have hdescent : baseEnd_5056291 < baseStart_5056291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056314 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 3, 1, 5]
def baseStart_5056314 : Nat := 118140960795 + 5056314 * 2 ^ 59
def prefixEnd_5056314 : Nat := 4983230072969 + 3 ^ 40 * 5056314 * 2
def baseEnd_5056314 : Nat := 2596319422057835381921441

theorem tailTrace_5056314 : CollatzResearch.WordTrace tailWord_5056314 prefixEnd_5056314 2596319422057835381921441 := by
  unfold tailWord_5056314
  simp only [CollatzResearch.WordTrace]
  refine ⟨46104730550961350631401999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122945948135896935017071997 46104730550961350631401999)
  ·
    refine ⟨69157095826442025947102999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46104730550961350631401999 69157095826442025947102999)
    ·
      refine ⟨103735643739663038920654499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69157095826442025947102999 103735643739663038920654499)
      ·
        refine ⟨155603465609494558380981749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103735643739663038920654499 155603465609494558380981749)
        ·
          refine ⟨14587824900890114848217039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 155603465609494558380981749 14587824900890114848217039)
          ·
            refine ⟨21881737351335172272325559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14587824900890114848217039 21881737351335172272325559)
            ·
              refine ⟨32822606027002758408488339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21881737351335172272325559 32822606027002758408488339)
              ·
                refine ⟨49233909040504137612732509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32822606027002758408488339 49233909040504137612732509)
                ·
                  refine ⟨18462715890189051604774691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49233909040504137612732509 18462715890189051604774691)
                  ·
                    refine ⟨27694073835283577407162037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18462715890189051604774691 27694073835283577407162037)
                    ·
                      refine ⟨2596319422057835381921441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27694073835283577407162037 2596319422057835381921441)
                      ·
                        rfl

theorem cell23_5056314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_5056314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056314 prefixEnd_5056314 := by exact prefixLift 5056314
  have htrace : WordTrace (prefixWord ++ tailWord_5056314) baseStart_5056314 baseEnd_5056314 := by
    simpa [prefixWord, tailWord_5056314, baseEnd_5056314] using wordTrace_append hprefix tailTrace_5056314
  have hstable : (prefixWord ++ tailWord_5056314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056314).length < 2 ^ (prefixWord ++ tailWord_5056314).sum := by decide
  have hdescent : baseEnd_5056314 < baseStart_5056314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056328 : List Nat := [2, 1, 3, 1, 1, 4, 2, 2, 3, 2, 2]
def baseStart_5056328 : Nat := 118140960795 + 5056328 * 2 ^ 59
def prefixEnd_5056328 : Nat := 4983230072969 + 3 ^ 40 * 5056328 * 2
def baseEnd_5056328 : Nat := 2596326610786998327146377

theorem tailTrace_5056328 : CollatzResearch.WordTrace tailWord_5056328 prefixEnd_5056328 2596326610786998327146377 := by
  unfold tailWord_5056328
  simp only [CollatzResearch.WordTrace]
  refine ⟨92209716412897341458308819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122946288550529788611078425 92209716412897341458308819)
  ·
    refine ⟨138314574619346012187463229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92209716412897341458308819 138314574619346012187463229)
    ·
      refine ⟨51867965482254754570298711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138314574619346012187463229 51867965482254754570298711)
      ·
        refine ⟨77801948223382131855448067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51867965482254754570298711 77801948223382131855448067)
        ·
          refine ⟨116702922335073197783172101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77801948223382131855448067 116702922335073197783172101)
          ·
            refine ⟨21881797937826224584344769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116702922335073197783172101 21881797937826224584344769)
            ·
              refine ⟨16411348453369668438258577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21881797937826224584344769 16411348453369668438258577)
              ·
                refine ⟨12308511340027251328693933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16411348453369668438258577 12308511340027251328693933)
                ·
                  refine ⟨4615691752510219248260225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12308511340027251328693933 4615691752510219248260225)
                  ·
                    refine ⟨3461768814382664436195169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4615691752510219248260225 3461768814382664436195169)
                    ·
                      refine ⟨2596326610786998327146377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3461768814382664436195169 2596326610786998327146377)
                      ·
                        rfl

theorem cell23_5056328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 3, 2, 2].length) (baseStart_5056328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056328 prefixEnd_5056328 := by exact prefixLift 5056328
  have htrace : WordTrace (prefixWord ++ tailWord_5056328) baseStart_5056328 baseEnd_5056328 := by
    simpa [prefixWord, tailWord_5056328, baseEnd_5056328] using wordTrace_append hprefix tailTrace_5056328
  have hstable : (prefixWord ++ tailWord_5056328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056328).length < 2 ^ (prefixWord ++ tailWord_5056328).sum := by decide
  have hdescent : baseEnd_5056328 < baseStart_5056328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056348 : List Nat := [2, 2, 4, 2, 2, 1, 2, 1, 1, 1, 5]
def baseStart_5056348 : Nat := 118140960795 + 5056348 * 2 ^ 59
def prefixEnd_5056348 : Nat := 4983230072969 + 3 ^ 40 * 5056348 * 2
def baseEnd_5056348 : Nat := 2596336880400088248896285

theorem tailTrace_5056348 : CollatzResearch.WordTrace tailWord_5056348 prefixEnd_5056348 2596336880400088248896285 := by
  unfold tailWord_5056348
  simp only [CollatzResearch.WordTrace]
  refine ⟨92210081142861113166172849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122946774857148150888230465 92210081142861113166172849)
  ·
    refine ⟨69157560857145834874629637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92210081142861113166172849 69157560857145834874629637)
    ·
      refine ⟨12967042660714844038993057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69157560857145834874629637 12967042660714844038993057)
      ·
        refine ⟨9725281995536133029244793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12967042660714844038993057 9725281995536133029244793)
        ·
          refine ⟨7293961496652099771933595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9725281995536133029244793 7293961496652099771933595)
          ·
            refine ⟨10940942244978149657900393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7293961496652099771933595 10940942244978149657900393)
            ·
              refine ⟨8205706683733612243425295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10940942244978149657900393 8205706683733612243425295)
              ·
                refine ⟨12308560025600418365137943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8205706683733612243425295 12308560025600418365137943)
                ·
                  refine ⟨18462840038400627547706915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12308560025600418365137943 18462840038400627547706915)
                  ·
                    refine ⟨27694260057600941321560373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18462840038400627547706915 27694260057600941321560373)
                    ·
                      refine ⟨2596336880400088248896285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27694260057600941321560373 2596336880400088248896285)
                      ·
                        rfl

theorem cell23_5056348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_5056348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056348 prefixEnd_5056348 := by exact prefixLift 5056348
  have htrace : WordTrace (prefixWord ++ tailWord_5056348) baseStart_5056348 baseEnd_5056348 := by
    simpa [prefixWord, tailWord_5056348, baseEnd_5056348] using wordTrace_append hprefix tailTrace_5056348
  have hstable : (prefixWord ++ tailWord_5056348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056348).length < 2 ^ (prefixWord ++ tailWord_5056348).sum := by decide
  have hdescent : baseEnd_5056348 < baseStart_5056348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056371 : List Nat := [1, 1, 1, 2, 2, 1, 3, 4, 3, 3, 2]
def baseStart_5056371 : Nat := 118140960795 + 5056371 * 2 ^ 59
def prefixEnd_5056371 : Nat := 4983230072969 + 3 ^ 40 * 5056371 * 2
def baseEnd_5056371 : Nat := 2596348690455141658908679

theorem tailTrace_5056371 : CollatzResearch.WordTrace tailWord_5056371 prefixEnd_5056371 2596348690455141658908679 := by
  unfold tailWord_5056371
  simp only [CollatzResearch.WordTrace]
  refine ⟨184421001164638901260432967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122947334109759267506955311 184421001164638901260432967)
  ·
    refine ⟨276631501746958351890649451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184421001164638901260432967 276631501746958351890649451)
    ·
      refine ⟨414947252620437527835974177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276631501746958351890649451 414947252620437527835974177)
      ·
        refine ⟨311210439465328145876980633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 414947252620437527835974177 311210439465328145876980633)
        ·
          refine ⟨233407829598996109407735475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311210439465328145876980633 233407829598996109407735475)
          ·
            refine ⟨350111744398494164111603213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233407829598996109407735475 350111744398494164111603213)
            ·
              refine ⟨131291904149435311541851205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 350111744398494164111603213 131291904149435311541851205)
              ·
                refine ⟨24617232028019120914097101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131291904149435311541851205 24617232028019120914097101)
                ·
                  refine ⟨9231462010507170342786413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24617232028019120914097101 9231462010507170342786413)
                  ·
                    refine ⟨3461798253940188878544905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9231462010507170342786413 3461798253940188878544905)
                    ·
                      refine ⟨2596348690455141658908679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3461798253940188878544905 2596348690455141658908679)
                      ·
                        rfl

theorem cell23_5056371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 3, 2].length) (baseStart_5056371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056371 prefixEnd_5056371 := by exact prefixLift 5056371
  have htrace : WordTrace (prefixWord ++ tailWord_5056371) baseStart_5056371 baseEnd_5056371 := by
    simpa [prefixWord, tailWord_5056371, baseEnd_5056371] using wordTrace_append hprefix tailTrace_5056371
  have hstable : (prefixWord ++ tailWord_5056371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056371).length < 2 ^ (prefixWord ++ tailWord_5056371).sum := by decide
  have hdescent : baseEnd_5056371 < baseStart_5056371 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056382 : List Nat := [4, 2, 3, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_5056382 : Nat := 118140960795 + 5056382 * 2 ^ 59
def prefixEnd_5056382 : Nat := 4983230072969 + 3 ^ 40 * 5056382 * 2
def baseEnd_5056382 : Nat := 2596354338742341115871129

theorem tailTrace_5056382 : CollatzResearch.WordTrace tailWord_5056382 prefixEnd_5056382 2596354338742341115871129 := by
  unfold tailWord_5056382
  simp only [CollatzResearch.WordTrace]
  refine ⟨23052675295949881267385425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122947601578399366759388933 23052675295949881267385425)
  ·
    refine ⟨17289506471962410950539069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23052675295949881267385425 17289506471962410950539069)
    ·
      refine ⟨6483564926985904106452151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17289506471962410950539069 6483564926985904106452151)
      ·
        refine ⟨9725347390478856159678227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6483564926985904106452151 9725347390478856159678227)
        ·
          refine ⟨14588021085718284239517341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9725347390478856159678227 14588021085718284239517341)
          ·
            refine ⟨5470507907144356589819003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14588021085718284239517341 5470507907144356589819003)
            ·
              refine ⟨8205761860716534884728505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5470507907144356589819003 8205761860716534884728505)
              ·
                refine ⟨6154321395537401163546379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8205761860716534884728505 6154321395537401163546379)
                ·
                  refine ⟨9231482093306101745319569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6154321395537401163546379 9231482093306101745319569)
                  ·
                    refine ⟨6923611569979576308989677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9231482093306101745319569 6923611569979576308989677)
                    ·
                      refine ⟨2596354338742341115871129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6923611569979576308989677 2596354338742341115871129)
                      ·
                        rfl

theorem cell23_5056382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_5056382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056382 prefixEnd_5056382 := by exact prefixLift 5056382
  have htrace : WordTrace (prefixWord ++ tailWord_5056382) baseStart_5056382 baseEnd_5056382 := by
    simpa [prefixWord, tailWord_5056382, baseEnd_5056382] using wordTrace_append hprefix tailTrace_5056382
  have hstable : (prefixWord ++ tailWord_5056382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056382).length < 2 ^ (prefixWord ++ tailWord_5056382).sum := by decide
  have hdescent : baseEnd_5056382 < baseStart_5056382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056401 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 3, 4, 2]
def baseStart_5056401 : Nat := 118140960795 + 5056401 * 2 ^ 59
def prefixEnd_5056401 : Nat := 4983230072969 + 3 ^ 40 * 5056401 * 2
def baseEnd_5056401 : Nat := 2596364094874776541533541

theorem tailTrace_5056401 : CollatzResearch.WordTrace tailWord_5056401 prefixEnd_5056401 2596364094874776541533541 := by
  unfold tailWord_5056401
  simp only [CollatzResearch.WordTrace]
  refine ⟨184422095354530216384025057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122948063569686810922683371 184422095354530216384025057)
  ·
    refine ⟨138316571515897662288018793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184422095354530216384025057 138316571515897662288018793)
    ·
      refine ⟨103737428636923246716014095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138316571515897662288018793 103737428636923246716014095)
      ·
        refine ⟨155606142955384870074021143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103737428636923246716014095 155606142955384870074021143)
        ·
          refine ⟨233409214433077305111031715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155606142955384870074021143 233409214433077305111031715)
          ·
            refine ⟨350113821649615957666547573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233409214433077305111031715 350113821649615957666547573)
            ·
              refine ⟨32823170779651496031238835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 350113821649615957666547573 32823170779651496031238835)
              ·
                refine ⟨49234756169477244046858253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32823170779651496031238835 49234756169477244046858253)
                ·
                  refine ⟨18463033563553966517571845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49234756169477244046858253 18463033563553966517571845)
                  ·
                    refine ⟨3461818793166368722044721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18463033563553966517571845 3461818793166368722044721)
                    ·
                      refine ⟨2596364094874776541533541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3461818793166368722044721 2596364094874776541533541)
                      ·
                        rfl

theorem cell23_5056401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 4, 2].length) (baseStart_5056401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056401 prefixEnd_5056401 := by exact prefixLift 5056401
  have htrace : WordTrace (prefixWord ++ tailWord_5056401) baseStart_5056401 baseEnd_5056401 := by
    simpa [prefixWord, tailWord_5056401, baseEnd_5056401] using wordTrace_append hprefix tailTrace_5056401
  have hstable : (prefixWord ++ tailWord_5056401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056401).length < 2 ^ (prefixWord ++ tailWord_5056401).sum := by decide
  have hdescent : baseEnd_5056401 < baseStart_5056401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056405 : List Nat := [1, 3, 2, 1, 1, 3, 5, 1, 1, 3, 2]
def baseStart_5056405 : Nat := 118140960795 + 5056405 * 2 ^ 59
def prefixEnd_5056405 : Nat := 4983230072969 + 3 ^ 40 * 5056405 * 2
def baseEnd_5056405 : Nat := 2596366148797394525883523

theorem tailTrace_5056405 : CollatzResearch.WordTrace tailWord_5056405 prefixEnd_5056405 2596366148797394525883523 := by
  unfold tailWord_5056405
  simp only [CollatzResearch.WordTrace]
  refine ⟨184422241246515725067170669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122948160831010483378113779 184422241246515725067170669)
  ·
    refine ⟨69158340467443396900189001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184422241246515725067170669 69158340467443396900189001)
    ·
      refine ⟨51868755350582547675141751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69158340467443396900189001 51868755350582547675141751)
      ·
        refine ⟨77803133025873821512712627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51868755350582547675141751 77803133025873821512712627)
        ·
          refine ⟨116704699538810732269068941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77803133025873821512712627 116704699538810732269068941)
          ·
            refine ⟨43764262327054024600900853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116704699538810732269068941 43764262327054024600900853)
            ·
              refine ⟨4102899593161314806334455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43764262327054024600900853 4102899593161314806334455)
              ·
                refine ⟨6154349389741972209501683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4102899593161314806334455 6154349389741972209501683)
                ·
                  refine ⟨9231524084612958314252525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6154349389741972209501683 9231524084612958314252525)
                  ·
                    refine ⟨3461821531729859367844697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9231524084612958314252525 3461821531729859367844697)
                    ·
                      refine ⟨2596366148797394525883523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3461821531729859367844697 2596366148797394525883523)
                      ·
                        rfl

theorem cell23_5056405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 1, 3, 2].length) (baseStart_5056405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056405 prefixEnd_5056405 := by exact prefixLift 5056405
  have htrace : WordTrace (prefixWord ++ tailWord_5056405) baseStart_5056405 baseEnd_5056405 := by
    simpa [prefixWord, tailWord_5056405, baseEnd_5056405] using wordTrace_append hprefix tailTrace_5056405
  have hstable : (prefixWord ++ tailWord_5056405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056405).length < 2 ^ (prefixWord ++ tailWord_5056405).sum := by decide
  have hdescent : baseEnd_5056405 < baseStart_5056405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056464 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 5]
def baseStart_5056464 : Nat := 118140960795 + 5056464 * 2 ^ 59
def prefixEnd_5056464 : Nat := 4983230072969 + 3 ^ 40 * 5056464 * 2
def baseEnd_5056464 : Nat := 2596396444156009795045751

theorem tailTrace_5056464 : CollatzResearch.WordTrace tailWord_5056464 prefixEnd_5056464 2596396444156009795045751 := by
  unfold tailWord_5056464
  simp only [CollatzResearch.WordTrace]
  refine ⟨92212196576650989071784223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122949595435534652095712297 92212196576650989071784223)
  ·
    refine ⟨138318294864976483607676335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92212196576650989071784223 138318294864976483607676335)
    ·
      refine ⟨207477442297464725411514503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138318294864976483607676335 207477442297464725411514503)
      ·
        refine ⟨311216163446197088117271755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207477442297464725411514503 311216163446197088117271755)
        ·
          refine ⟨466824245169295632175907633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311216163446197088117271755 466824245169295632175907633)
          ·
            refine ⟨350118183876971724131930725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 466824245169295632175907633 350118183876971724131930725)
            ·
              refine ⟨65647159476932198274737011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 350118183876971724131930725 65647159476932198274737011)
              ·
                refine ⟨98470739215398297412105517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65647159476932198274737011 98470739215398297412105517)
                ·
                  refine ⟨36926527205774361529539569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98470739215398297412105517 36926527205774361529539569)
                  ·
                    refine ⟨27694895404330771147154677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36926527205774361529539569 27694895404330771147154677)
                    ·
                      refine ⟨2596396444156009795045751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27694895404330771147154677 2596396444156009795045751)
                      ·
                        rfl

theorem cell23_5056464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 5].length) (baseStart_5056464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056464 prefixEnd_5056464 := by exact prefixLift 5056464
  have htrace : WordTrace (prefixWord ++ tailWord_5056464) baseStart_5056464 baseEnd_5056464 := by
    simpa [prefixWord, tailWord_5056464, baseEnd_5056464] using wordTrace_append hprefix tailTrace_5056464
  have hstable : (prefixWord ++ tailWord_5056464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056464).length < 2 ^ (prefixWord ++ tailWord_5056464).sum := by decide
  have hdescent : baseEnd_5056464 < baseStart_5056464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056511 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 6, 2, 3]
def baseStart_5056511 : Nat := 118140960795 + 5056511 * 2 ^ 59
def prefixEnd_5056511 : Nat := 4983230072969 + 3 ^ 40 * 5056511 * 2
def baseEnd_5056511 : Nat := 2596420577746771111158035

theorem tailTrace_5056511 : CollatzResearch.WordTrace tailWord_5056511 prefixEnd_5056511 2596420577746771111158035 := by
  unfold tailWord_5056511
  simp only [CollatzResearch.WordTrace]
  refine ⟨184426107384131705170529387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122950738256087803447019591 184426107384131705170529387)
  ·
    refine ⟨276639161076197557755794081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184426107384131705170529387 276639161076197557755794081)
    ·
      refine ⟨207479370807148168316845561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276639161076197557755794081 207479370807148168316845561)
      ·
        refine ⟨155609528105361126237634171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207479370807148168316845561 155609528105361126237634171)
        ·
          refine ⟨233414292158041689356451257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155609528105361126237634171 233414292158041689356451257)
          ·
            refine ⟨175060719118531267017338443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233414292158041689356451257 175060719118531267017338443)
            ·
              refine ⟨262591078677796900526007665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175060719118531267017338443 262591078677796900526007665)
              ·
                refine ⟨196943309008347675394505749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262591078677796900526007665 196943309008347675394505749)
                ·
                  refine ⟨9231717609766297284117457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 196943309008347675394505749 9231717609766297284117457)
                  ·
                    refine ⟨6923788207324722963088093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9231717609766297284117457 6923788207324722963088093)
                    ·
                      refine ⟨2596420577746771111158035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6923788207324722963088093 2596420577746771111158035)
                      ·
                        rfl

theorem cell23_5056511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 2, 3].length) (baseStart_5056511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056511 prefixEnd_5056511 := by exact prefixLift 5056511
  have htrace : WordTrace (prefixWord ++ tailWord_5056511) baseStart_5056511 baseEnd_5056511 := by
    simpa [prefixWord, tailWord_5056511, baseEnd_5056511] using wordTrace_append hprefix tailTrace_5056511
  have hstable : (prefixWord ++ tailWord_5056511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056511).length < 2 ^ (prefixWord ++ tailWord_5056511).sum := by decide
  have hdescent : baseEnd_5056511 < baseStart_5056511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056601 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 3, 1, 5]
def baseStart_5056601 : Nat := 118140960795 + 5056601 * 2 ^ 59
def prefixEnd_5056601 : Nat := 4983230072969 + 3 ^ 40 * 5056601 * 2
def baseEnd_5056601 : Nat := 2596466791005675759032621

theorem tailTrace_5056601 : CollatzResearch.WordTrace tailWord_5056601 prefixEnd_5056601 2596466791005675759032621 := by
  unfold tailWord_5056601
  simp only [CollatzResearch.WordTrace]
  refine ⟨184429389953805650541305657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122952926635870433694203771 184429389953805650541305657)
  ·
    refine ⟨138322042465354237905979243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184429389953805650541305657 138322042465354237905979243)
    ·
      refine ⟨207483063698031356858968865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138322042465354237905979243 207483063698031356858968865)
      ·
        refine ⟨155612297773523517644226649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207483063698031356858968865 155612297773523517644226649)
        ·
          refine ⟨116709223330142638233169987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155612297773523517644226649 116709223330142638233169987)
          ·
            refine ⟨175063834995213957349754981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116709223330142638233169987 175063834995213957349754981)
            ·
              refine ⟨32824469061602617003079059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175063834995213957349754981 32824469061602617003079059)
              ·
                refine ⟨49236703592403925504618589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32824469061602617003079059 49236703592403925504618589)
                ·
                  refine ⟨18463763847151472064231971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49236703592403925504618589 18463763847151472064231971)
                  ·
                    refine ⟨27695645770727208096347957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18463763847151472064231971 27695645770727208096347957)
                    ·
                      refine ⟨2596466791005675759032621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27695645770727208096347957 2596466791005675759032621)
                      ·
                        rfl

theorem cell23_5056601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_5056601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056601 prefixEnd_5056601 := by exact prefixLift 5056601
  have htrace : WordTrace (prefixWord ++ tailWord_5056601) baseStart_5056601 baseEnd_5056601 := by
    simpa [prefixWord, tailWord_5056601, baseEnd_5056601] using wordTrace_append hprefix tailTrace_5056601
  have hstable : (prefixWord ++ tailWord_5056601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056601).length < 2 ^ (prefixWord ++ tailWord_5056601).sum := by decide
  have hdescent : baseEnd_5056601 < baseStart_5056601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056608 : List Nat := [2, 1, 1, 3, 2, 4, 2, 1, 1, 6]
def baseStart_5056608 : Nat := 118140960795 + 5056608 * 2 ^ 59
def prefixEnd_5056608 : Nat := 4983230072969 + 3 ^ 40 * 5056608 * 2
def baseEnd_5056608 : Nat := 865490128456752410548363

theorem tailTrace_5056608 : CollatzResearch.WordTrace tailWord_5056608 prefixEnd_5056608 865490128456752410548363 := by
  unfold tailWord_5056608
  simp only [CollatzResearch.WordTrace]
  refine ⟨92214822632390145368405239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122953096843186860491206985 92214822632390145368405239)
  ·
    refine ⟨138322233948585218052607859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92214822632390145368405239 138322233948585218052607859)
    ·
      refine ⟨207483350922877827078911789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138322233948585218052607859 207483350922877827078911789)
      ·
        refine ⟨77806256596079185154591921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207483350922877827078911789 77806256596079185154591921)
        ·
          refine ⟨58354692447059388865943941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77806256596079185154591921 58354692447059388865943941)
          ·
            refine ⟨10941504833823635412364489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58354692447059388865943941 10941504833823635412364489)
            ·
              refine ⟨8206128625367726559273367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10941504833823635412364489 8206128625367726559273367)
              ·
                refine ⟨12309192938051589838910051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8206128625367726559273367 12309192938051589838910051)
                ·
                  refine ⟨18463789407077384758365077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12309192938051589838910051 18463789407077384758365077)
                  ·
                    refine ⟨865490128456752410548363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18463789407077384758365077 865490128456752410548363)
                    ·
                      rfl

theorem cell23_5056608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 1, 6].length) (baseStart_5056608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056608 prefixEnd_5056608 := by exact prefixLift 5056608
  have htrace : WordTrace (prefixWord ++ tailWord_5056608) baseStart_5056608 baseEnd_5056608 := by
    simpa [prefixWord, tailWord_5056608, baseEnd_5056608] using wordTrace_append hprefix tailTrace_5056608
  have hstable : (prefixWord ++ tailWord_5056608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056608).length < 2 ^ (prefixWord ++ tailWord_5056608).sum := by decide
  have hdescent : baseEnd_5056608 < baseStart_5056608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056611 : List Nat := [1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 6]
def baseStart_5056611 : Nat := 118140960795 + 5056611 * 2 ^ 59
def prefixEnd_5056611 : Nat := 4983230072969 + 3 ^ 40 * 5056611 * 2
def baseEnd_5056611 : Nat := 2596471925812220719907575

theorem tailTrace_5056611 : CollatzResearch.WordTrace tailWord_5056611 prefixEnd_5056611 2596471925812220719907575 := by
  unfold tailWord_5056611
  simp only [CollatzResearch.WordTrace]
  refine ⟨184429754683769422249169687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122953169789179614832779791 184429754683769422249169687)
  ·
    refine ⟨276644632025654133373754531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184429754683769422249169687 276644632025654133373754531)
    ·
      refine ⟨414966948038481200060631797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276644632025654133373754531 414966948038481200060631797)
      ·
        refine ⟨38903151378607612505684231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 414966948038481200060631797 38903151378607612505684231)
        ·
          refine ⟨58354727067911418758526347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38903151378607612505684231 58354727067911418758526347)
          ·
            refine ⟨87532090601867128137789521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58354727067911418758526347 87532090601867128137789521)
            ·
              refine ⟨65649067951400346103342141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87532090601867128137789521 65649067951400346103342141)
              ·
                refine ⟨24618400481775129788753303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65649067951400346103342141 24618400481775129788753303)
                ·
                  refine ⟨36927600722662694683129955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24618400481775129788753303 36927600722662694683129955)
                  ·
                    refine ⟨55391401083994042024694933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36927600722662694683129955 55391401083994042024694933)
                    ·
                      refine ⟨2596471925812220719907575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55391401083994042024694933 2596471925812220719907575)
                      ·
                        rfl

theorem cell23_5056611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_5056611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056611 prefixEnd_5056611 := by exact prefixLift 5056611
  have htrace : WordTrace (prefixWord ++ tailWord_5056611) baseStart_5056611 baseEnd_5056611 := by
    simpa [prefixWord, tailWord_5056611, baseEnd_5056611] using wordTrace_append hprefix tailTrace_5056611
  have hstable : (prefixWord ++ tailWord_5056611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056611).length < 2 ^ (prefixWord ++ tailWord_5056611).sum := by decide
  have hdescent : baseEnd_5056611 < baseStart_5056611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056665 : List Nat := [1, 2, 1, 2, 1, 2, 1, 7, 2, 1, 3]
def baseStart_5056665 : Nat := 118140960795 + 5056665 * 2 ^ 59
def prefixEnd_5056665 : Nat := 4983230072969 + 3 ^ 40 * 5056665 * 2
def baseEnd_5056665 : Nat := 2596499653767563508632327

theorem tailTrace_5056665 : CollatzResearch.WordTrace tailWord_5056665 prefixEnd_5056665 2596499653767563508632327 := by
  unfold tailWord_5056665
  simp only [CollatzResearch.WordTrace]
  refine ⟨184431724225573789471635449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122954482817049192981090299 184431724225573789471635449)
  ·
    refine ⟨138323793169180342103726587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184431724225573789471635449 138323793169180342103726587)
    ·
      refine ⟨207485689753770513155589881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138323793169180342103726587 207485689753770513155589881)
      ·
        refine ⟨155614267315327884866692411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207485689753770513155589881 155614267315327884866692411)
        ·
          refine ⟨233421400972991827300038617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155614267315327884866692411 233421400972991827300038617)
          ·
            refine ⟨175066050729743870475028963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233421400972991827300038617 175066050729743870475028963)
            ·
              refine ⟨262599076094615805712543445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175066050729743870475028963 262599076094615805712543445)
              ·
                refine ⟨6154665845967557946387737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 262599076094615805712543445 6154665845967557946387737)
                ·
                  refine ⟨4615999384475668459790803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6154665845967557946387737 4615999384475668459790803)
                  ·
                    refine ⟨6923999076713502689686205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4615999384475668459790803 6923999076713502689686205)
                    ·
                      refine ⟨2596499653767563508632327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6923999076713502689686205 2596499653767563508632327)
                      ·
                        rfl

theorem cell23_5056665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 2, 1, 3].length) (baseStart_5056665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056665 prefixEnd_5056665 := by exact prefixLift 5056665
  have htrace : WordTrace (prefixWord ++ tailWord_5056665) baseStart_5056665 baseEnd_5056665 := by
    simpa [prefixWord, tailWord_5056665, baseEnd_5056665] using wordTrace_append hprefix tailTrace_5056665
  have hstable : (prefixWord ++ tailWord_5056665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056665).length < 2 ^ (prefixWord ++ tailWord_5056665).sum := by decide
  have hdescent : baseEnd_5056665 < baseStart_5056665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056726 : List Nat := [5, 2, 1, 2, 1, 1, 3, 2, 1, 3, 2]
def baseStart_5056726 : Nat := 118140960795 + 5056726 * 2 ^ 59
def prefixEnd_5056726 : Nat := 4983230072969 + 3 ^ 40 * 5056726 * 2
def baseEnd_5056726 : Nat := 2596530976087487769969547

theorem tailTrace_5056726 : CollatzResearch.WordTrace tailWord_5056726 prefixEnd_5056726 2596530976087487769969547 := by
  unfold tailWord_5056726
  simp only [CollatzResearch.WordTrace]
  refine ⟨11527121817397049805600377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122955966052235197926404021 11527121817397049805600377)
  ·
    refine ⟨8645341363047787354200283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11527121817397049805600377 8645341363047787354200283)
    ·
      refine ⟨12968012044571681031300425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8645341363047787354200283 12968012044571681031300425)
      ·
        refine ⟨9726009033428760773475319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12968012044571681031300425 9726009033428760773475319)
        ·
          refine ⟨14589013550143141160212979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9726009033428760773475319 14589013550143141160212979)
          ·
            refine ⟨21883520325214711740319469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14589013550143141160212979 21883520325214711740319469)
            ·
              refine ⟨8206320121955516902619801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21883520325214711740319469 8206320121955516902619801)
              ·
                refine ⟨6154740091466637676964851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8206320121955516902619801 6154740091466637676964851)
                ·
                  refine ⟨9232110137199956515447277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6154740091466637676964851 9232110137199956515447277)
                  ·
                    refine ⟨3462041301449983693292729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9232110137199956515447277 3462041301449983693292729)
                    ·
                      refine ⟨2596530976087487769969547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3462041301449983693292729 2596530976087487769969547)
                      ·
                        rfl

theorem cell23_5056726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_5056726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056726 prefixEnd_5056726 := by exact prefixLift 5056726
  have htrace : WordTrace (prefixWord ++ tailWord_5056726) baseStart_5056726 baseEnd_5056726 := by
    simpa [prefixWord, tailWord_5056726, baseEnd_5056726] using wordTrace_append hprefix tailTrace_5056726
  have hstable : (prefixWord ++ tailWord_5056726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056726).length < 2 ^ (prefixWord ++ tailWord_5056726).sum := by decide
  have hdescent : baseEnd_5056726 < baseStart_5056726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056739 : List Nat := [1, 1, 1, 8, 1, 1, 1, 2, 1, 4, 2]
def baseStart_5056739 : Nat := 118140960795 + 5056739 * 2 ^ 59
def prefixEnd_5056739 : Nat := 4983230072969 + 3 ^ 40 * 5056739 * 2
def baseEnd_5056739 : Nat := 2596537651335996219106987

theorem tailTrace_5056739 : CollatzResearch.WordTrace tailWord_5056739 prefixEnd_5056739 2596537651335996219106987 := by
  unfold tailWord_5056739
  simp only [CollatzResearch.WordTrace]
  refine ⟨184434423227305700109829271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122956282151537133406552847 184434423227305700109829271)
  ·
    refine ⟨276651634840958550164743907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184434423227305700109829271 276651634840958550164743907)
    ·
      refine ⟨414977452261437825247115861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276651634840958550164743907 414977452261437825247115861)
      ·
        refine ⟨4863017018688724514614639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 414977452261437825247115861 4863017018688724514614639)
        ·
          refine ⟨7294525528033086771921959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4863017018688724514614639 7294525528033086771921959)
          ·
            refine ⟨10941788292049630157882939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7294525528033086771921959 10941788292049630157882939)
            ·
              refine ⟨16412682438074445236824409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10941788292049630157882939 16412682438074445236824409)
              ·
                refine ⟨12309511828555833927618307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16412682438074445236824409 12309511828555833927618307)
                ·
                  refine ⟨18464267742833750891427461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12309511828555833927618307 18464267742833750891427461)
                  ·
                    refine ⟨3462050201781328292142649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18464267742833750891427461 3462050201781328292142649)
                    ·
                      refine ⟨2596537651335996219106987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3462050201781328292142649 2596537651335996219106987)
                      ·
                        rfl

theorem cell23_5056739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_5056739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056739 prefixEnd_5056739 := by exact prefixLift 5056739
  have htrace : WordTrace (prefixWord ++ tailWord_5056739) baseStart_5056739 baseEnd_5056739 := by
    simpa [prefixWord, tailWord_5056739, baseEnd_5056739] using wordTrace_append hprefix tailTrace_5056739
  have hstable : (prefixWord ++ tailWord_5056739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056739).length < 2 ^ (prefixWord ++ tailWord_5056739).sum := by decide
  have hdescent : baseEnd_5056739 < baseStart_5056739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056762 : List Nat := [3, 1, 1, 1, 1, 5, 4, 2, 5]
def baseStart_5056762 : Nat := 118140960795 + 5056762 * 2 ^ 59
def prefixEnd_5056762 : Nat := 4983230072969 + 3 ^ 40 * 5056762 * 2
def baseEnd_5056762 : Nat := 288505495710116625457709

theorem tailTrace_5056762 : CollatzResearch.WordTrace tailWord_5056762 prefixEnd_5056762 288505495710116625457709 := by
  unfold tailWord_5056762
  simp only [CollatzResearch.WordTrace]
  refine ⟨46108815526555593759479135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122956841404148250025277693 46108815526555593759479135)
  ·
    refine ⟨69163223289833390639218703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46108815526555593759479135 69163223289833390639218703)
    ·
      refine ⟨103744834934750085958828055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69163223289833390639218703 103744834934750085958828055)
      ·
        refine ⟨155617252402125128938242083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103744834934750085958828055 155617252402125128938242083)
        ·
          refine ⟨233425878603187693407363125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155617252402125128938242083 233425878603187693407363125)
          ·
            refine ⟨21883676119048846256940293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 233425878603187693407363125 21883676119048846256940293)
            ·
              refine ⟨4103189272321658673176305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21883676119048846256940293 4103189272321658673176305)
              ·
                refine ⟨3077391954241244004882229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4103189272321658673176305 3077391954241244004882229)
                ·
                  refine ⟨288505495710116625457709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3077391954241244004882229 288505495710116625457709)
                  ·
                    rfl

theorem cell23_5056762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 2, 5].length) (baseStart_5056762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056762 prefixEnd_5056762 := by exact prefixLift 5056762
  have htrace : WordTrace (prefixWord ++ tailWord_5056762) baseStart_5056762 baseEnd_5056762 := by
    simpa [prefixWord, tailWord_5056762, baseEnd_5056762] using wordTrace_append hprefix tailTrace_5056762
  have hstable : (prefixWord ++ tailWord_5056762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056762).length < 2 ^ (prefixWord ++ tailWord_5056762).sum := by decide
  have hdescent : baseEnd_5056762 < baseStart_5056762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056768 : List Nat := [2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 5]
def baseStart_5056768 : Nat := 118140960795 + 5056768 * 2 ^ 59
def prefixEnd_5056768 : Nat := 4983230072969 + 3 ^ 40 * 5056768 * 2
def baseEnd_5056768 : Nat := 2596552542274976605644353

theorem tailTrace_5056768 : CollatzResearch.WordTrace tailWord_5056768 prefixEnd_5056768 2596552542274976605644353 := by
  unfold tailWord_5056768
  simp only [CollatzResearch.WordTrace]
  refine ⟨92217740472100319031317479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122956987296133758708423305 92217740472100319031317479)
  ·
    refine ⟨138326610708150478546976219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92217740472100319031317479 138326610708150478546976219)
    ·
      refine ⟨207489916062225717820464329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138326610708150478546976219 207489916062225717820464329)
      ·
        refine ⟨155617437046669288365348247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207489916062225717820464329 155617437046669288365348247)
        ·
          refine ⟨233426155570003932548022371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155617437046669288365348247 233426155570003932548022371)
          ·
            refine ⟨350139233355005898822033557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233426155570003932548022371 350139233355005898822033557)
            ·
              refine ⟨16412776563515901507282823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 350139233355005898822033557 16412776563515901507282823)
              ·
                refine ⟨24619164845273852260924235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16412776563515901507282823 24619164845273852260924235)
                ·
                  refine ⟨36928747267910778391386353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24619164845273852260924235 36928747267910778391386353)
                  ·
                    refine ⟨27696560450933083793539765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36928747267910778391386353 27696560450933083793539765)
                    ·
                      refine ⟨2596552542274976605644353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27696560450933083793539765 2596552542274976605644353)
                      ·
                        rfl

theorem cell23_5056768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_5056768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056768 prefixEnd_5056768 := by exact prefixLift 5056768
  have htrace : WordTrace (prefixWord ++ tailWord_5056768) baseStart_5056768 baseEnd_5056768 := by
    simpa [prefixWord, tailWord_5056768, baseEnd_5056768] using wordTrace_append hprefix tailTrace_5056768
  have hstable : (prefixWord ++ tailWord_5056768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056768).length < 2 ^ (prefixWord ++ tailWord_5056768).sum := by decide
  have hdescent : baseEnd_5056768 < baseStart_5056768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056772 : List Nat := [2, 3, 2, 2, 3, 1, 1, 1, 2, 3, 3]
def baseStart_5056772 : Nat := 118140960795 + 5056772 * 2 ^ 59
def prefixEnd_5056772 : Nat := 4983230072969 + 3 ^ 40 * 5056772 * 2
def baseEnd_5056772 : Nat := 2596554596197594589994335

theorem tailTrace_5056772 : CollatzResearch.WordTrace tailWord_5056772 prefixEnd_5056772 2596554596197594589994335 := by
  unfold tailWord_5056772
  simp only [CollatzResearch.WordTrace]
  refine ⟨92217813418093073372890285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122957084557457431163853713 92217813418093073372890285)
  ·
    refine ⟨34581680031784902514833857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92217813418093073372890285 34581680031784902514833857)
    ·
      refine ⟨25936260023838676886125393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34581680031784902514833857 25936260023838676886125393)
      ·
        refine ⟨19452195017879007664594045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25936260023838676886125393 19452195017879007664594045)
        ·
          refine ⟨7294573131704627874222767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19452195017879007664594045 7294573131704627874222767)
          ·
            refine ⟨10941859697556941811334151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7294573131704627874222767 10941859697556941811334151)
            ·
              refine ⟨16412789546335412717001227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10941859697556941811334151 16412789546335412717001227)
              ·
                refine ⟨24619184319503119075501841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16412789546335412717001227 24619184319503119075501841)
                ·
                  refine ⟨18464388239627339306626381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24619184319503119075501841 18464388239627339306626381)
                  ·
                    refine ⟨6924145589860252239984893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18464388239627339306626381 6924145589860252239984893)
                    ·
                      refine ⟨2596554596197594589994335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6924145589860252239984893 2596554596197594589994335)
                      ·
                        rfl

theorem cell23_5056772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_5056772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056772 prefixEnd_5056772 := by exact prefixLift 5056772
  have htrace : WordTrace (prefixWord ++ tailWord_5056772) baseStart_5056772 baseEnd_5056772 := by
    simpa [prefixWord, tailWord_5056772, baseEnd_5056772] using wordTrace_append hprefix tailTrace_5056772
  have hstable : (prefixWord ++ tailWord_5056772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056772).length < 2 ^ (prefixWord ++ tailWord_5056772).sum := by decide
  have hdescent : baseEnd_5056772 < baseStart_5056772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056795 : List Nat := [1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 4]
def baseStart_5056795 : Nat := 118140960795 + 5056795 * 2 ^ 59
def prefixEnd_5056795 : Nat := 4983230072969 + 3 ^ 40 * 5056795 * 2
def baseEnd_5056795 : Nat := 2596566406252648000006729

theorem tailTrace_5056795 : CollatzResearch.WordTrace tailWord_5056795 prefixEnd_5056795 2596566406252648000006729 := by
  unfold tailWord_5056795
  simp only [CollatzResearch.WordTrace]
  refine ⟨184436465715102821673867839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122957643810068547782578559 184436465715102821673867839)
  ·
    refine ⟨276654698572654232510801759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184436465715102821673867839 276654698572654232510801759)
    ·
      refine ⟨414982047858981348766202639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276654698572654232510801759 414982047858981348766202639)
      ·
        refine ⟨622473071788472023149303959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414982047858981348766202639 622473071788472023149303959)
        ·
          refine ⟨933709607682708034723955939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 622473071788472023149303959 933709607682708034723955939)
          ·
            refine ⟨1400564411524062052085933909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 933709607682708034723955939 1400564411524062052085933909)
            ·
              refine ⟨8206432098773801086441019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1400564411524062052085933909 8206432098773801086441019)
              ·
                refine ⟨12309648148160701629661529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8206432098773801086441019 12309648148160701629661529)
                ·
                  refine ⟨9232236111120526222246147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12309648148160701629661529 9232236111120526222246147)
                  ·
                    refine ⟨13848354166680789333369221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9232236111120526222246147 13848354166680789333369221)
                    ·
                      refine ⟨2596566406252648000006729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13848354166680789333369221 2596566406252648000006729)
                      ·
                        rfl

theorem cell23_5056795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 4].length) (baseStart_5056795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056795 prefixEnd_5056795 := by exact prefixLift 5056795
  have htrace : WordTrace (prefixWord ++ tailWord_5056795) baseStart_5056795 baseEnd_5056795 := by
    simpa [prefixWord, tailWord_5056795, baseEnd_5056795] using wordTrace_append hprefix tailTrace_5056795
  have hstable : (prefixWord ++ tailWord_5056795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056795).length < 2 ^ (prefixWord ++ tailWord_5056795).sum := by decide
  have hdescent : baseEnd_5056795 < baseStart_5056795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056807 : List Nat := [1, 1, 8, 1, 2, 1, 1, 2, 2, 2, 2]
def baseStart_5056807 : Nat := 118140960795 + 5056807 * 2 ^ 59
def prefixEnd_5056807 : Nat := 4983230072969 + 3 ^ 40 * 5056807 * 2
def baseEnd_5056807 : Nat := 2596572568020501953056675

theorem tailTrace_5056807 : CollatzResearch.WordTrace tailWord_5056807 prefixEnd_5056807 2596572568020501953056675 := by
  unfold tailWord_5056807
  simp only [CollatzResearch.WordTrace]
  refine ⟨184436903391059347723304675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122957935594039565148869783 184436903391059347723304675)
  ·
    refine ⟨276655355086589021584957013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184436903391059347723304675 276655355086589021584957013)
    ·
      refine ⟨3242054942420965096698715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 276655355086589021584957013 3242054942420965096698715)
      ·
        refine ⟨4863082413631447645048073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3242054942420965096698715 4863082413631447645048073)
        ·
          refine ⟨3647311810223585733786055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4863082413631447645048073 3647311810223585733786055)
          ·
            refine ⟨5470967715335378600679083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3647311810223585733786055 5470967715335378600679083)
            ·
              refine ⟨8206451573003067901018625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5470967715335378600679083 8206451573003067901018625)
              ·
                refine ⟨6154838679752300925763969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8206451573003067901018625 6154838679752300925763969)
                ·
                  refine ⟨4616129009814225694322977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6154838679752300925763969 4616129009814225694322977)
                  ·
                    refine ⟨3462096757360669270742233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4616129009814225694322977 3462096757360669270742233)
                    ·
                      refine ⟨2596572568020501953056675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3462096757360669270742233 2596572568020501953056675)
                      ·
                        rfl

theorem cell23_5056807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_5056807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056807 prefixEnd_5056807 := by exact prefixLift 5056807
  have htrace : WordTrace (prefixWord ++ tailWord_5056807) baseStart_5056807 baseEnd_5056807 := by
    simpa [prefixWord, tailWord_5056807, baseEnd_5056807] using wordTrace_append hprefix tailTrace_5056807
  have hstable : (prefixWord ++ tailWord_5056807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056807).length < 2 ^ (prefixWord ++ tailWord_5056807).sum := by decide
  have hdescent : baseEnd_5056807 < baseStart_5056807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056815 : List Nat := [1, 1, 2, 1, 2, 1, 4, 4, 2, 2, 3]
def baseStart_5056815 : Nat := 118140960795 + 5056815 * 2 ^ 59
def prefixEnd_5056815 : Nat := 4983230072969 + 3 ^ 40 * 5056815 * 2
def baseEnd_5056815 : Nat := 2596576675865737921756637

theorem tailTrace_5056815 : CollatzResearch.WordTrace tailWord_5056815 prefixEnd_5056815 2596576675865737921756637 := by
  unfold tailWord_5056815
  simp only [CollatzResearch.WordTrace]
  refine ⟨184437195175030365089595899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122958130116686910059730599 184437195175030365089595899)
  ·
    refine ⟨276655792762545547634393849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184437195175030365089595899 276655792762545547634393849)
    ·
      refine ⟨207491844571909160725795387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276655792762545547634393849 207491844571909160725795387)
      ·
        refine ⟨311237766857863741088693081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207491844571909160725795387 311237766857863741088693081)
        ·
          refine ⟨233428325143397805816519811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311237766857863741088693081 233428325143397805816519811)
          ·
            refine ⟨350142487715096708724779717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233428325143397805816519811 350142487715096708724779717)
            ·
              refine ⟨65651716446580632885896197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 350142487715096708724779717 65651716446580632885896197)
              ·
                refine ⟨12309696833733868666105537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65651716446580632885896197 12309696833733868666105537)
                ·
                  refine ⟨9232272625300401499579153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12309696833733868666105537 9232272625300401499579153)
                  ·
                    refine ⟨6924204468975301124684365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9232272625300401499579153 6924204468975301124684365)
                    ·
                      refine ⟨2596576675865737921756637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6924204468975301124684365 2596576675865737921756637)
                      ·
                        rfl

theorem cell23_5056815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 2, 3].length) (baseStart_5056815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056815 prefixEnd_5056815 := by exact prefixLift 5056815
  have htrace : WordTrace (prefixWord ++ tailWord_5056815) baseStart_5056815 baseEnd_5056815 := by
    simpa [prefixWord, tailWord_5056815, baseEnd_5056815] using wordTrace_append hprefix tailTrace_5056815
  have hstable : (prefixWord ++ tailWord_5056815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056815).length < 2 ^ (prefixWord ++ tailWord_5056815).sum := by decide
  have hdescent : baseEnd_5056815 < baseStart_5056815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056899 : List Nat := [1, 1, 1, 3, 6, 2, 1, 2, 1, 5]
def baseStart_5056899 : Nat := 118140960795 + 5056899 * 2 ^ 59
def prefixEnd_5056899 : Nat := 4983230072969 + 3 ^ 40 * 5056899 * 2
def baseEnd_5056899 : Nat := 865539936080238531035417

theorem tailTrace_5056899 : CollatzResearch.WordTrace tailWord_5056899 prefixEnd_5056899 865539936080238531035417 := by
  unfold tailWord_5056899
  simp only [CollatzResearch.WordTrace]
  refine ⟨184440258906726047435653751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122960172604484031623769167 184440258906726047435653751)
  ·
    refine ⟨276660388360089071153480627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184440258906726047435653751 276660388360089071153480627)
    ·
      refine ⟨414990582540133606730220941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276660388360089071153480627 414990582540133606730220941)
      ·
        refine ⟨155621468452550102523832853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 414990582540133606730220941 155621468452550102523832853)
        ·
          refine ⟨7294756333713286055804665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 155621468452550102523832853 7294756333713286055804665)
          ·
            refine ⟨5471067250284964541853499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7294756333713286055804665 5471067250284964541853499)
            ·
              refine ⟨8206600875427446812780249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5471067250284964541853499 8206600875427446812780249)
              ·
                refine ⟨6154950656570585109585187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8206600875427446812780249 6154950656570585109585187)
                ·
                  refine ⟨9232425984855877664377781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6154950656570585109585187 9232425984855877664377781)
                  ·
                    refine ⟨865539936080238531035417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9232425984855877664377781 865539936080238531035417)
                    ·
                      rfl

theorem cell23_5056899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 5].length) (baseStart_5056899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056899 prefixEnd_5056899 := by exact prefixLift 5056899
  have htrace : WordTrace (prefixWord ++ tailWord_5056899) baseStart_5056899 baseEnd_5056899 := by
    simpa [prefixWord, tailWord_5056899, baseEnd_5056899] using wordTrace_append hprefix tailTrace_5056899
  have hstable : (prefixWord ++ tailWord_5056899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056899).length < 2 ^ (prefixWord ++ tailWord_5056899).sum := by decide
  have hdescent : baseEnd_5056899 < baseStart_5056899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056916 : List Nat := [2, 4, 2, 1, 3, 1, 3, 1, 1, 5]
def baseStart_5056916 : Nat := 118140960795 + 5056916 * 2 ^ 59
def prefixEnd_5056916 : Nat := 4983230072969 + 3 ^ 40 * 5056916 * 2
def baseEnd_5056916 : Nat := 865542845803947342197891

theorem tailTrace_5056916 : CollatzResearch.WordTrace tailWord_5056916 prefixEnd_5056916 865542845803947342197891 := by
  unfold tailWord_5056916
  simp only [CollatzResearch.WordTrace]
  refine ⟨92220439473832229669511301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122960585965109639559348401 92220439473832229669511301)
  ·
    refine ⟨17291332401343543063033369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92220439473832229669511301 17291332401343543063033369)
    ·
      refine ⟨12968499301007657297275027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17291332401343543063033369 12968499301007657297275027)
      ·
        refine ⟨19452748951511485945912541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12968499301007657297275027 19452748951511485945912541)
        ·
          refine ⟨7294780856816807229717203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19452748951511485945912541 7294780856816807229717203)
          ·
            refine ⟨10942171285225210844575805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7294780856816807229717203 10942171285225210844575805)
            ·
              refine ⟨4103314231959454066715927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10942171285225210844575805 4103314231959454066715927)
              ·
                refine ⟨6154971347939181100073891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4103314231959454066715927 6154971347939181100073891)
                ·
                  refine ⟨9232457021908771650110837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6154971347939181100073891 9232457021908771650110837)
                  ·
                    refine ⟨865542845803947342197891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9232457021908771650110837 865542845803947342197891)
                    ·
                      rfl

theorem cell23_5056916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_5056916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056916 prefixEnd_5056916 := by exact prefixLift 5056916
  have htrace : WordTrace (prefixWord ++ tailWord_5056916) baseStart_5056916 baseEnd_5056916 := by
    simpa [prefixWord, tailWord_5056916, baseEnd_5056916] using wordTrace_append hprefix tailTrace_5056916
  have hstable : (prefixWord ++ tailWord_5056916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056916).length < 2 ^ (prefixWord ++ tailWord_5056916).sum := by decide
  have hdescent : baseEnd_5056916 < baseStart_5056916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056922 : List Nat := [3, 1, 1, 4, 1, 2, 3, 1, 1, 1, 5]
def baseStart_5056922 : Nat := 118140960795 + 5056922 * 2 ^ 59
def prefixEnd_5056922 : Nat := 4983230072969 + 3 ^ 40 * 5056922 * 2
def baseEnd_5056922 : Nat := 2596631618295769003118645

theorem tailTrace_5056922 : CollatzResearch.WordTrace tailWord_5056922 prefixEnd_5056922 2596631618295769003118645 := by
  unfold tailWord_5056922
  simp only [CollatzResearch.WordTrace]
  refine ⟨46110274446410680590935255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122960731857095148242494013 46110274446410680590935255)
  ·
    refine ⟨69165411669616020886402883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46110274446410680590935255 69165411669616020886402883)
    ·
      refine ⟨103748117504424031329604325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69165411669616020886402883 103748117504424031329604325)
      ·
        refine ⟨19452772032079505874300811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103748117504424031329604325 19452772032079505874300811)
        ·
          refine ⟨29179158048119258811451217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19452772032079505874300811 29179158048119258811451217)
          ·
            refine ⟨21884368536089444108588413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29179158048119258811451217 21884368536089444108588413)
            ·
              refine ⟨8206638201033541540720655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21884368536089444108588413 8206638201033541540720655)
              ·
                refine ⟨12309957301550312311080983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8206638201033541540720655 12309957301550312311080983)
                ·
                  refine ⟨18464935952325468466621475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12309957301550312311080983 18464935952325468466621475)
                  ·
                    refine ⟨27697403928488202699932213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18464935952325468466621475 27697403928488202699932213)
                    ·
                      refine ⟨2596631618295769003118645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27697403928488202699932213 2596631618295769003118645)
                      ·
                        rfl

theorem cell23_5056922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_5056922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056922 prefixEnd_5056922 := by exact prefixLift 5056922
  have htrace : WordTrace (prefixWord ++ tailWord_5056922) baseStart_5056922 baseEnd_5056922 := by
    simpa [prefixWord, tailWord_5056922, baseEnd_5056922] using wordTrace_append hprefix tailTrace_5056922
  have hstable : (prefixWord ++ tailWord_5056922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056922).length < 2 ^ (prefixWord ++ tailWord_5056922).sum := by decide
  have hdescent : baseEnd_5056922 < baseStart_5056922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056925 : List Nat := [1, 4, 2, 1, 4, 11]
def baseStart_5056925 : Nat := 118140960795 + 5056925 * 2 ^ 59
def prefixEnd_5056925 : Nat := 4983230072969 + 3 ^ 40 * 5056925 * 2
def baseEnd_5056925 : Nat := 10685733163529763339017

theorem tailTrace_5056925 : CollatzResearch.WordTrace tailWord_5056925 prefixEnd_5056925 10685733163529763339017 := by
  unfold tailWord_5056925
  simp only [CollatzResearch.WordTrace]
  refine ⟨184441207204631853876100229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122960804803087902584066819 184441207204631853876100229)
  ·
    refine ⟨34582726350868472601768793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184441207204631853876100229 34582726350868472601768793)
    ·
      refine ⟨25937044763151354451326595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34582726350868472601768793 25937044763151354451326595)
      ·
        refine ⟨38905567144727031676989893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25937044763151354451326595 38905567144727031676989893)
        ·
          refine ⟨7294793839636318439435605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38905567144727031676989893 7294793839636318439435605)
          ·
            refine ⟨10685733163529763339017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7294793839636318439435605 10685733163529763339017)
            ·
              rfl

theorem cell23_5056925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 11].length) (baseStart_5056925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056925 prefixEnd_5056925 := by exact prefixLift 5056925
  have htrace : WordTrace (prefixWord ++ tailWord_5056925) baseStart_5056925 baseEnd_5056925 := by
    simpa [prefixWord, tailWord_5056925, baseEnd_5056925] using wordTrace_append hprefix tailTrace_5056925
  have hstable : (prefixWord ++ tailWord_5056925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056925).length < 2 ^ (prefixWord ++ tailWord_5056925).sum := by decide
  have hdescent : baseEnd_5056925 < baseStart_5056925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056949 : List Nat := [1, 3, 3, 2, 3, 1, 2, 1, 1, 2, 4]
def baseStart_5056949 : Nat := 118140960795 + 5056949 * 2 ^ 59
def prefixEnd_5056949 : Nat := 4983230072969 + 3 ^ 40 * 5056949 * 2
def baseEnd_5056949 : Nat := 2596645482273440397481021

theorem tailTrace_5056949 : CollatzResearch.WordTrace tailWord_5056949 prefixEnd_5056949 2596645482273440397481021 := by
  unfold tailWord_5056949
  simp only [CollatzResearch.WordTrace]
  refine ⟨184442082556544905974973901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122961388371029937316649267 184442082556544905974973901)
  ·
    refine ⟨69165780958704339740615213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184442082556544905974973901 69165780958704339740615213)
    ·
      refine ⟨25937167859514127402730705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69165780958704339740615213 25937167859514127402730705)
      ·
        refine ⟨19452875894635595552048029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25937167859514127402730705 19452875894635595552048029)
        ·
          refine ⟨7294828460488348332018011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19452875894635595552048029 7294828460488348332018011)
          ·
            refine ⟨10942242690732522498027017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7294828460488348332018011 10942242690732522498027017)
            ·
              refine ⟨8206682018049391873520263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10942242690732522498027017 8206682018049391873520263)
              ·
                refine ⟨12310023027074087810280395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8206682018049391873520263 12310023027074087810280395)
                ·
                  refine ⟨18465034540611131715420593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12310023027074087810280395 18465034540611131715420593)
                  ·
                    refine ⟨13848775905458348786565445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18465034540611131715420593 13848775905458348786565445)
                    ·
                      refine ⟨2596645482273440397481021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13848775905458348786565445 2596645482273440397481021)
                      ·
                        rfl

theorem cell23_5056949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_5056949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056949 prefixEnd_5056949 := by exact prefixLift 5056949
  have htrace : WordTrace (prefixWord ++ tailWord_5056949) baseStart_5056949 baseEnd_5056949 := by
    simpa [prefixWord, tailWord_5056949, baseEnd_5056949] using wordTrace_append hprefix tailTrace_5056949
  have hstable : (prefixWord ++ tailWord_5056949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056949).length < 2 ^ (prefixWord ++ tailWord_5056949).sum := by decide
  have hdescent : baseEnd_5056949 < baseStart_5056949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056952 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 6, 1, 3]
def baseStart_5056952 : Nat := 118140960795 + 5056952 * 2 ^ 59
def prefixEnd_5056952 : Nat := 4983230072969 + 3 ^ 40 * 5056952 * 2
def baseEnd_5056952 : Nat := 2596647022715403885743507

theorem tailTrace_5056952 : CollatzResearch.WordTrace tailWord_5056952 prefixEnd_5056952 2596647022715403885743507 := by
  unfold tailWord_5056952
  simp only [CollatzResearch.WordTrace]
  refine ⟨92221095987767018743666555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122961461317022691658222073 92221095987767018743666555)
  ·
    refine ⟨138331643981650528115499833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92221095987767018743666555 138331643981650528115499833)
    ·
      refine ⟨103748732986237896086624875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138331643981650528115499833 103748732986237896086624875)
      ·
        refine ⟨155623099479356844129937313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103748732986237896086624875 155623099479356844129937313)
        ·
          refine ⟨116717324609517633097452985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155623099479356844129937313 116717324609517633097452985)
          ·
            refine ⟨87537993457138224823089739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116717324609517633097452985 87537993457138224823089739)
            ·
              refine ⟨131306990185707337234634609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87537993457138224823089739 131306990185707337234634609)
              ·
                refine ⟨98480242639280502925975957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131306990185707337234634609 98480242639280502925975957)
                ·
                  refine ⟨4616261373716273574655123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98480242639280502925975957 4616261373716273574655123)
                  ·
                    refine ⟨6924392060574410361982685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4616261373716273574655123 6924392060574410361982685)
                    ·
                      refine ⟨2596647022715403885743507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6924392060574410361982685 2596647022715403885743507)
                      ·
                        rfl

theorem cell23_5056952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 6, 1, 3].length) (baseStart_5056952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056952 prefixEnd_5056952 := by exact prefixLift 5056952
  have htrace : WordTrace (prefixWord ++ tailWord_5056952) baseStart_5056952 baseEnd_5056952 := by
    simpa [prefixWord, tailWord_5056952, baseEnd_5056952] using wordTrace_append hprefix tailTrace_5056952
  have hstable : (prefixWord ++ tailWord_5056952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056952).length < 2 ^ (prefixWord ++ tailWord_5056952).sum := by decide
  have hdescent : baseEnd_5056952 < baseStart_5056952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056985 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 4, 6]
def baseStart_5056985 : Nat := 118140960795 + 5056985 * 2 ^ 59
def prefixEnd_5056985 : Nat := 4983230072969 + 3 ^ 40 * 5056985 * 2
def baseEnd_5056985 : Nat := 865554655859000752210285

theorem tailTrace_5056985 : CollatzResearch.WordTrace tailWord_5056985 prefixEnd_5056985 865554655859000752210285 := by
  unfold tailWord_5056985
  simp only [CollatzResearch.WordTrace]
  refine ⟨184443395584414484123284409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122962263722942989415522939 184443395584414484123284409)
  ·
    refine ⟨138332546688310863092463307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184443395584414484123284409 138332546688310863092463307)
    ·
      refine ⟨207498820032466294638694961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138332546688310863092463307 207498820032466294638694961)
      ·
        refine ⟨155624115024349720979021221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207498820032466294638694961 155624115024349720979021221)
        ·
          refine ⟨29179521567065572683566479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 155624115024349720979021221 29179521567065572683566479)
          ·
            refine ⟨43769282350598359025349719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29179521567065572683566479 43769282350598359025349719)
            ·
              refine ⟨65653923525897538538024579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43769282350598359025349719 65653923525897538538024579)
              ·
                refine ⟨98480885288846307807036869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65653923525897538538024579 98480885288846307807036869)
                ·
                  refine ⟨18465165991658682713819413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98480885288846307807036869 18465165991658682713819413)
                  ·
                    refine ⟨865554655859000752210285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18465165991658682713819413 865554655859000752210285)
                    ·
                      rfl

theorem cell23_5056985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 6].length) (baseStart_5056985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5056985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5056985 prefixEnd_5056985 := by exact prefixLift 5056985
  have htrace : WordTrace (prefixWord ++ tailWord_5056985) baseStart_5056985 baseEnd_5056985 := by
    simpa [prefixWord, tailWord_5056985, baseEnd_5056985] using wordTrace_append hprefix tailTrace_5056985
  have hstable : (prefixWord ++ tailWord_5056985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056985).length < 2 ^ (prefixWord ++ tailWord_5056985).sum := by decide
  have hdescent : baseEnd_5056985 < baseStart_5056985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057002 : List Nat := [3, 1, 3, 1, 3, 1, 2, 1, 2, 6]
def baseStart_5057002 : Nat := 118140960795 + 5057002 * 2 ^ 59
def prefixEnd_5057002 : Nat := 4983230072969 + 3 ^ 40 * 5057002 * 2
def baseEnd_5057002 : Nat := 865557565582709563372759

theorem tailTrace_5057002 : CollatzResearch.WordTrace tailWord_5057002 prefixEnd_5057002 865557565582709563372759 := by
  unfold tailWord_5057002
  simp only [CollatzResearch.WordTrace]
  refine ⟨46111003906338224006663315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122962677083568597351102173 46111003906338224006663315)
  ·
    refine ⟨69166505859507336009994973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46111003906338224006663315 69166505859507336009994973)
    ·
      refine ⟨25937439697315251003748115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69166505859507336009994973 25937439697315251003748115)
      ·
        refine ⟨38906159545972876505622173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25937439697315251003748115 38906159545972876505622173)
        ·
          refine ⟨14589809829739828689608315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38906159545972876505622173 14589809829739828689608315)
          ·
            refine ⟨21884714744609743034412473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14589809829739828689608315 21884714744609743034412473)
            ·
              refine ⟨16413536058457307275809355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21884714744609743034412473 16413536058457307275809355)
              ·
                refine ⟨24620304087685960913714033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16413536058457307275809355 24620304087685960913714033)
                ·
                  refine ⟨18465228065764470685285525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24620304087685960913714033 18465228065764470685285525)
                  ·
                    refine ⟨865557565582709563372759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18465228065764470685285525 865557565582709563372759)
                    ·
                      rfl

theorem cell23_5057002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_5057002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057002 prefixEnd_5057002 := by exact prefixLift 5057002
  have htrace : WordTrace (prefixWord ++ tailWord_5057002) baseStart_5057002 baseEnd_5057002 := by
    simpa [prefixWord, tailWord_5057002, baseEnd_5057002] using wordTrace_append hprefix tailTrace_5057002
  have hstable : (prefixWord ++ tailWord_5057002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057002).length < 2 ^ (prefixWord ++ tailWord_5057002).sum := by decide
  have hdescent : baseEnd_5057002 < baseStart_5057002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057060 : List Nat := [2, 3, 1, 5, 1, 1, 1, 3, 2, 2, 2]
def baseStart_5057060 : Nat := 118140960795 + 5057060 * 2 ^ 59
def prefixEnd_5057060 : Nat := 4983230072969 + 3 ^ 40 * 5057060 * 2
def baseEnd_5057060 : Nat := 2596702478626089463193011

theorem tailTrace_5057060 : CollatzResearch.WordTrace tailWord_5057060 prefixEnd_5057060 2596702478626089463193011 := by
  unfold tailWord_5057060
  simp only [CollatzResearch.WordTrace]
  refine ⟨92223065529571385966132317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122964087372761847954843089 92223065529571385966132317)
  ·
    refine ⟨34583649573589269737299619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92223065529571385966132317 34583649573589269737299619)
    ·
      refine ⟨51875474360383904605949429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34583649573589269737299619 51875474360383904605949429)
      ·
        refine ⟨4863325721285991056807759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51875474360383904605949429 4863325721285991056807759)
        ·
          refine ⟨7294988581928986585211639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4863325721285991056807759 7294988581928986585211639)
          ·
            refine ⟨10942482872893479877817459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7294988581928986585211639 10942482872893479877817459)
            ·
              refine ⟨16413724309340219816726189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10942482872893479877817459 16413724309340219816726189)
              ·
                refine ⟨6155146616002582431272321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16413724309340219816726189 6155146616002582431272321)
                ·
                  refine ⟨4616359962001936823454241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6155146616002582431272321 4616359962001936823454241)
                  ·
                    refine ⟨3462269971501452617590681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4616359962001936823454241 3462269971501452617590681)
                    ·
                      refine ⟨2596702478626089463193011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3462269971501452617590681 2596702478626089463193011)
                      ·
                        rfl

theorem cell23_5057060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_5057060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057060 prefixEnd_5057060 := by exact prefixLift 5057060
  have htrace : WordTrace (prefixWord ++ tailWord_5057060) baseStart_5057060 baseEnd_5057060 := by
    simpa [prefixWord, tailWord_5057060, baseEnd_5057060] using wordTrace_append hprefix tailTrace_5057060
  have hstable : (prefixWord ++ tailWord_5057060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057060).length < 2 ^ (prefixWord ++ tailWord_5057060).sum := by decide
  have hdescent : baseEnd_5057060 < baseStart_5057060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057156 : List Nat := [2, 3, 2, 1, 3, 3, 1, 2, 6]
def baseStart_5057156 : Nat := 118140960795 + 5057156 * 2 ^ 59
def prefixEnd_5057156 : Nat := 4983230072969 + 3 ^ 40 * 5057156 * 2
def baseEnd_5057156 : Nat := 288527974752102343065841

theorem tailTrace_5057156 : CollatzResearch.WordTrace tailWord_5057156 prefixEnd_5057156 288527974752102343065841 := by
  unfold tailWord_5057156
  simp only [CollatzResearch.WordTrace]
  refine ⟨92224816233397490163879661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122966421644529986885172881 92224816233397490163879661)
  ·
    refine ⟨34584306087524058811454873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92224816233397490163879661 34584306087524058811454873)
    ·
      refine ⟨25938229565643044108591155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34584306087524058811454873 25938229565643044108591155)
      ·
        refine ⟨38907344348464566162886733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25938229565643044108591155 38907344348464566162886733)
        ·
          refine ⟨14590254130674212311082525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38907344348464566162886733 14590254130674212311082525)
          ·
            refine ⟨5471345299002829616655947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14590254130674212311082525 5471345299002829616655947)
            ·
              refine ⟨8207017948504244424983921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5471345299002829616655947 8207017948504244424983921)
              ·
                refine ⟨6155263461378183318737941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8207017948504244424983921 6155263461378183318737941)
                ·
                  refine ⟨288527974752102343065841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6155263461378183318737941 288527974752102343065841)
                  ·
                    rfl

theorem cell23_5057156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 6].length) (baseStart_5057156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057156 prefixEnd_5057156 := by exact prefixLift 5057156
  have htrace : WordTrace (prefixWord ++ tailWord_5057156) baseStart_5057156 baseEnd_5057156 := by
    simpa [prefixWord, tailWord_5057156, baseEnd_5057156] using wordTrace_append hprefix tailTrace_5057156
  have hstable : (prefixWord ++ tailWord_5057156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057156).length < 2 ^ (prefixWord ++ tailWord_5057156).sum := by decide
  have hdescent : baseEnd_5057156 < baseStart_5057156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057189 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 1, 8, 2]
def baseStart_5057189 : Nat := 118140960795 + 5057189 * 2 ^ 59
def prefixEnd_5057189 : Nat := 4983230072969 + 3 ^ 40 * 5057189 * 2
def baseEnd_5057189 : Nat := 2596768717630519458479917

theorem tailTrace_5057189 : CollatzResearch.WordTrace tailWord_5057189 prefixEnd_5057189 2596768717630519458479917 := by
  unfold tailWord_5057189
  simp only [CollatzResearch.WordTrace]
  refine ⟨184450836075675426963710621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122967224050450284642473747 184450836075675426963710621)
  ·
    refine ⟨69169063528378285111391483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184450836075675426963710621 69169063528378285111391483)
    ·
      refine ⟨103753595292567427667087225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69169063528378285111391483 103753595292567427667087225)
      ·
        refine ⟨77815196469425570750315419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103753595292567427667087225 77815196469425570750315419)
        ·
          refine ⟨116722794704138356125473129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77815196469425570750315419 116722794704138356125473129)
          ·
            refine ⟨87542096028103767094104847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116722794704138356125473129 87542096028103767094104847)
            ·
              refine ⟨131313144042155650641157271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87542096028103767094104847 131313144042155650641157271)
              ·
                refine ⟨196969716063233475961735907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131313144042155650641157271 196969716063233475961735907)
                ·
                  refine ⟨295454574094850213942603861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196969716063233475961735907 295454574094850213942603861)
                  ·
                    refine ⟨3462358290174025944639889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 295454574094850213942603861 3462358290174025944639889)
                    ·
                      refine ⟨2596768717630519458479917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3462358290174025944639889 2596768717630519458479917)
                      ·
                        rfl

theorem cell23_5057189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 8, 2].length) (baseStart_5057189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057189 prefixEnd_5057189 := by exact prefixLift 5057189
  have htrace : WordTrace (prefixWord ++ tailWord_5057189) baseStart_5057189 baseEnd_5057189 := by
    simpa [prefixWord, tailWord_5057189, baseEnd_5057189] using wordTrace_append hprefix tailTrace_5057189
  have hstable : (prefixWord ++ tailWord_5057189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057189).length < 2 ^ (prefixWord ++ tailWord_5057189).sum := by decide
  have hdescent : baseEnd_5057189 < baseStart_5057189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057194 : List Nat := [3, 1, 5, 2, 2, 1, 1, 3, 1, 4]
def baseStart_5057194 : Nat := 118140960795 + 5057194 * 2 ^ 59
def prefixEnd_5057194 : Nat := 4983230072969 + 3 ^ 40 * 5057194 * 2
def baseEnd_5057194 : Nat := 865590428344597312972465

theorem tailTrace_5057194 : CollatzResearch.WordTrace tailWord_5057194 prefixEnd_5057194 865590428344597312972465 := by
  unfold tailWord_5057194
  simp only [CollatzResearch.WordTrace]
  refine ⟨46112754610164328204410659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122967345627104875211761757 46112754610164328204410659)
  ·
    refine ⟨69169131915246492306615989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46112754610164328204410659 69169131915246492306615989)
    ·
      refine ⟨6484606117054358653745249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69169131915246492306615989 6484606117054358653745249)
      ·
        refine ⟨4863454587790768990308937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6484606117054358653745249 4863454587790768990308937)
        ·
          refine ⟨3647590940843076742731703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4863454587790768990308937 3647590940843076742731703)
          ·
            refine ⟨5471386411264615114097555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3647590940843076742731703 5471386411264615114097555)
            ·
              refine ⟨8207079616896922671146333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5471386411264615114097555 8207079616896922671146333)
              ·
                refine ⟨3077654856336346001679875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8207079616896922671146333 3077654856336346001679875)
                ·
                  refine ⟨4616482284504519002519813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3077654856336346001679875 4616482284504519002519813)
                  ·
                    refine ⟨865590428344597312972465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4616482284504519002519813 865590428344597312972465)
                    ·
                      rfl

theorem cell23_5057194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_5057194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057194 prefixEnd_5057194 := by exact prefixLift 5057194
  have htrace : WordTrace (prefixWord ++ tailWord_5057194) baseStart_5057194 baseEnd_5057194 := by
    simpa [prefixWord, tailWord_5057194, baseEnd_5057194] using wordTrace_append hprefix tailTrace_5057194
  have hstable : (prefixWord ++ tailWord_5057194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057194).length < 2 ^ (prefixWord ++ tailWord_5057194).sum := by decide
  have hdescent : baseEnd_5057194 < baseStart_5057194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057199 : List Nat := [1, 1, 2, 1, 2, 5, 1, 2, 4, 4]
def baseStart_5057199 : Nat := 118140960795 + 5057199 * 2 ^ 59
def prefixEnd_5057199 : Nat := 4983230072969 + 3 ^ 40 * 5057199 * 2
def baseEnd_5057199 : Nat := 865591284145688139784957

theorem tailTrace_5057199 : CollatzResearch.WordTrace tailWord_5057199 prefixEnd_5057199 865591284145688139784957 := by
  unfold tailWord_5057199
  simp only [CollatzResearch.WordTrace]
  refine ⟨184451200805639198671574651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122967467203759465781049767 184451200805639198671574651)
  ·
    refine ⟨276676801208458798007361977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184451200805639198671574651 276676801208458798007361977)
    ·
      refine ⟨207507600906344098505521483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276676801208458798007361977 207507600906344098505521483)
      ·
        refine ⟨311261401359516147758282225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207507600906344098505521483 311261401359516147758282225)
        ·
          refine ⟨233446051019637110818711669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311261401359516147758282225 233446051019637110818711669)
          ·
            refine ⟨21885567283090979139254219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 233446051019637110818711669 21885567283090979139254219)
            ·
              refine ⟨32828350924636468708881329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21885567283090979139254219 32828350924636468708881329)
              ·
                refine ⟨24621263193477351531660997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32828350924636468708881329 24621263193477351531660997)
                ·
                  refine ⟨4616486848777003412186437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24621263193477351531660997 4616486848777003412186437)
                  ·
                    refine ⟨865591284145688139784957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4616486848777003412186437 865591284145688139784957)
                    ·
                      rfl

theorem cell23_5057199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 4, 4].length) (baseStart_5057199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057199 prefixEnd_5057199 := by exact prefixLift 5057199
  have htrace : WordTrace (prefixWord ++ tailWord_5057199) baseStart_5057199 baseEnd_5057199 := by
    simpa [prefixWord, tailWord_5057199, baseEnd_5057199] using wordTrace_append hprefix tailTrace_5057199
  have hstable : (prefixWord ++ tailWord_5057199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057199).length < 2 ^ (prefixWord ++ tailWord_5057199).sum := by decide
  have hdescent : baseEnd_5057199 < baseStart_5057199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057209 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 5, 2, 3]
def baseStart_5057209 : Nat := 118140960795 + 5057209 * 2 ^ 59
def prefixEnd_5057209 : Nat := 4983230072969 + 3 ^ 40 * 5057209 * 2
def baseEnd_5057209 : Nat := 2596778987243609380229825

theorem tailTrace_5057209 : CollatzResearch.WordTrace tailWord_5057209 prefixEnd_5057209 2596778987243609380229825 := by
  unfold tailWord_5057209
  simp only [CollatzResearch.WordTrace]
  refine ⟨184451565535602970379438681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122967710357068646919625787 184451565535602970379438681)
  ·
    refine ⟨138338674151702227784579011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184451565535602970379438681 138338674151702227784579011)
    ·
      refine ⟨207508011227553341676868517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138338674151702227784579011 207508011227553341676868517)
      ·
        refine ⟨38907752105166251564412847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207508011227553341676868517 38907752105166251564412847)
        ·
          refine ⟨58361628157749377346619271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38907752105166251564412847 58361628157749377346619271)
          ·
            refine ⟨87542442236624066019928907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58361628157749377346619271 87542442236624066019928907)
            ·
              refine ⟨131313663354936099029893361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87542442236624066019928907 131313663354936099029893361)
              ·
                refine ⟨98485247516202074272420021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131313663354936099029893361 98485247516202074272420021)
                ·
                  refine ⟨9232991954643944463039377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98485247516202074272420021 9232991954643944463039377)
                  ·
                    refine ⟨6924743965982958347279533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9232991954643944463039377 6924743965982958347279533)
                    ·
                      refine ⟨2596778987243609380229825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6924743965982958347279533 2596778987243609380229825)
                      ·
                        rfl

theorem cell23_5057209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_5057209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057209 prefixEnd_5057209 := by exact prefixLift 5057209
  have htrace : WordTrace (prefixWord ++ tailWord_5057209) baseStart_5057209 baseEnd_5057209 := by
    simpa [prefixWord, tailWord_5057209, baseEnd_5057209] using wordTrace_append hprefix tailTrace_5057209
  have hstable : (prefixWord ++ tailWord_5057209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057209).length < 2 ^ (prefixWord ++ tailWord_5057209).sum := by decide
  have hdescent : baseEnd_5057209 < baseStart_5057209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057217 : List Nat := [1, 2, 6, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_5057217 : Nat := 118140960795 + 5057217 * 2 ^ 59
def prefixEnd_5057217 : Nat := 4983230072969 + 3 ^ 40 * 5057217 * 2
def baseEnd_5057217 : Nat := 2596783095088845348929789

theorem tailTrace_5057217 : CollatzResearch.WordTrace tailWord_5057217 prefixEnd_5057217 2596783095088845348929789 := by
  unfold tailWord_5057217
  simp only [CollatzResearch.WordTrace]
  refine ⟨184451857319573987745729905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122967904879715991830486603 184451857319573987745729905)
  ·
    refine ⟨138338892989680490809297429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184451857319573987745729905 138338892989680490809297429)
    ·
      refine ⟨6484635608891273006685817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 138338892989680490809297429 6484635608891273006685817)
      ·
        refine ⟨4863476706668454755014363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6484635608891273006685817 4863476706668454755014363)
        ·
          refine ⟨7295215060002682132521545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4863476706668454755014363 7295215060002682132521545)
          ·
            refine ⟨5471411295002011599391159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7295215060002682132521545 5471411295002011599391159)
            ·
              refine ⟨8207116942503017399086739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5471411295002011599391159 8207116942503017399086739)
              ·
                refine ⟨12310675413754526098630109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8207116942503017399086739 12310675413754526098630109)
                ·
                  refine ⟨4616503280157947286986291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12310675413754526098630109 4616503280157947286986291)
                  ·
                    refine ⟨6924754920236920930479437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4616503280157947286986291 6924754920236920930479437)
                    ·
                      refine ⟨2596783095088845348929789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6924754920236920930479437 2596783095088845348929789)
                      ·
                        rfl

theorem cell23_5057217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_5057217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057217 prefixEnd_5057217 := by exact prefixLift 5057217
  have htrace : WordTrace (prefixWord ++ tailWord_5057217) baseStart_5057217 baseEnd_5057217 := by
    simpa [prefixWord, tailWord_5057217, baseEnd_5057217] using wordTrace_append hprefix tailTrace_5057217
  have hstable : (prefixWord ++ tailWord_5057217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057217).length < 2 ^ (prefixWord ++ tailWord_5057217).sum := by decide
  have hdescent : baseEnd_5057217 < baseStart_5057217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057268 : List Nat := [2, 6, 1, 1, 3, 1, 2, 2, 1, 1, 3]
def baseStart_5057268 : Nat := 118140960795 + 5057268 * 2 ^ 59
def prefixEnd_5057268 : Nat := 4983230072969 + 3 ^ 40 * 5057268 * 2
def baseEnd_5057268 : Nat := 2596809282602224649392055

theorem tailTrace_5057268 : CollatzResearch.WordTrace tailWord_5057268 prefixEnd_5057268 2596809282602224649392055 := by
  unfold tailWord_5057268
  simp only [CollatzResearch.WordTrace]
  refine ⟨92226858721194611727918229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122969144961592815637224305 92226858721194611727918229)
  ·
    refine ⟨4323134002555997424746167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 92226858721194611727918229 4323134002555997424746167)
    ·
      refine ⟨6484701003833996137119251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4323134002555997424746167 6484701003833996137119251)
      ·
        refine ⟨9727051505750994205678877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6484701003833996137119251 9727051505750994205678877)
        ·
          refine ⟨3647644314656622827129579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9727051505750994205678877 3647644314656622827129579)
          ·
            refine ⟨5471466471984934240694369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3647644314656622827129579 5471466471984934240694369)
            ·
              refine ⟨4103599853988700680520777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5471466471984934240694369 4103599853988700680520777)
              ·
                refine ⟨3077699890491525510390583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4103599853988700680520777 3077699890491525510390583)
                ·
                  refine ⟨4616549835737288265585875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3077699890491525510390583 4616549835737288265585875)
                  ·
                    refine ⟨6924824753605932398378813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4616549835737288265585875 6924824753605932398378813)
                    ·
                      refine ⟨2596809282602224649392055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6924824753605932398378813 2596809282602224649392055)
                      ·
                        rfl

theorem cell23_5057268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_5057268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057268 prefixEnd_5057268 := by exact prefixLift 5057268
  have htrace : WordTrace (prefixWord ++ tailWord_5057268) baseStart_5057268 baseEnd_5057268 := by
    simpa [prefixWord, tailWord_5057268, baseEnd_5057268] using wordTrace_append hprefix tailTrace_5057268
  have hstable : (prefixWord ++ tailWord_5057268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057268).length < 2 ^ (prefixWord ++ tailWord_5057268).sum := by decide
  have hdescent : baseEnd_5057268 < baseStart_5057268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057299 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 2, 4, 3]
def baseStart_5057299 : Nat := 118140960795 + 5057299 * 2 ^ 59
def prefixEnd_5057299 : Nat := 4983230072969 + 3 ^ 40 * 5057299 * 2
def baseEnd_5057299 : Nat := 2596825200502514028104411

theorem tailTrace_5057299 : CollatzResearch.WordTrace tailWord_5057299 prefixEnd_5057299 2596825200502514028104411 := by
  unfold tailWord_5057299
  simp only [CollatzResearch.WordTrace]
  refine ⟨184454848105276915750214951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122969898736851277166809967 184454848105276915750214951)
  ·
    refine ⟨276682272157915373625322427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184454848105276915750214951 276682272157915373625322427)
    ·
      refine ⟨415023408236873060437983641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276682272157915373625322427 415023408236873060437983641)
      ·
        refine ⟨311267556177654795328487731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 415023408236873060437983641 311267556177654795328487731)
        ·
          refine ⟨466901334266482192992731597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311267556177654795328487731 466901334266482192992731597)
          ·
            refine ⟨175088000349930822372274349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 466901334266482192992731597 175088000349930822372274349)
            ·
              refine ⟨65658000131224058389602881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175088000349930822372274349 65658000131224058389602881)
              ·
                refine ⟨49243500098418043792202161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65658000131224058389602881 49243500098418043792202161)
                ·
                  refine ⟨36932625073813532844151621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49243500098418043792202161 36932625073813532844151621)
                  ·
                    refine ⟨6924867201340037408278429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36932625073813532844151621 6924867201340037408278429)
                    ·
                      refine ⟨2596825200502514028104411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6924867201340037408278429 2596825200502514028104411)
                      ·
                        rfl

theorem cell23_5057299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 4, 3].length) (baseStart_5057299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057299 prefixEnd_5057299 := by exact prefixLift 5057299
  have htrace : WordTrace (prefixWord ++ tailWord_5057299) baseStart_5057299 baseEnd_5057299 := by
    simpa [prefixWord, tailWord_5057299, baseEnd_5057299] using wordTrace_append hprefix tailTrace_5057299
  have hstable : (prefixWord ++ tailWord_5057299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057299).length < 2 ^ (prefixWord ++ tailWord_5057299).sum := by decide
  have hdescent : baseEnd_5057299 < baseStart_5057299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057313 : List Nat := [1, 2, 3, 2, 1, 2, 2, 2, 4, 2, 2]
def baseStart_5057313 : Nat := 118140960795 + 5057313 * 2 ^ 59
def prefixEnd_5057313 : Nat := 4983230072969 + 3 ^ 40 * 5057313 * 2
def baseEnd_5057313 : Nat := 2596832389231676973329347

theorem tailTrace_5057313 : CollatzResearch.WordTrace tailWord_5057313 prefixEnd_5057313 2596832389231676973329347 := by
  unfold tailWord_5057313
  simp only [CollatzResearch.WordTrace]
  refine ⟨184455358727226196141224593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122970239151484130760816395 184455358727226196141224593)
  ·
    refine ⟨138341519045419647105918445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184455358727226196141224593 138341519045419647105918445)
    ·
      refine ⟨51878069642032367664719417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138341519045419647105918445 51878069642032367664719417)
      ·
        refine ⟨38908552231524275748539563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51878069642032367664719417 38908552231524275748539563)
        ·
          refine ⟨58362828347286413622809345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38908552231524275748539563 58362828347286413622809345)
          ·
            refine ⟨43772121260464810217107009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58362828347286413622809345 43772121260464810217107009)
            ·
              refine ⟨32829090945348607662830257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43772121260464810217107009 32829090945348607662830257)
              ·
                refine ⟨24621818209011455747122693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32829090945348607662830257 24621818209011455747122693)
                ·
                  refine ⟨4616590914189647952585505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24621818209011455747122693 4616590914189647952585505)
                  ·
                    refine ⟨3462443185642235964439129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4616590914189647952585505 3462443185642235964439129)
                    ·
                      refine ⟨2596832389231676973329347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3462443185642235964439129 2596832389231676973329347)
                      ·
                        rfl

theorem cell23_5057313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_5057313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057313 prefixEnd_5057313 := by exact prefixLift 5057313
  have htrace : WordTrace (prefixWord ++ tailWord_5057313) baseStart_5057313 baseEnd_5057313 := by
    simpa [prefixWord, tailWord_5057313, baseEnd_5057313] using wordTrace_append hprefix tailTrace_5057313
  have hstable : (prefixWord ++ tailWord_5057313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057313).length < 2 ^ (prefixWord ++ tailWord_5057313).sum := by decide
  have hdescent : baseEnd_5057313 < baseStart_5057313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057336 : List Nat := [2, 1, 2, 1, 3, 2, 1, 6, 5]
def baseStart_5057336 : Nat := 118140960795 + 5057336 * 2 ^ 59
def prefixEnd_5057336 : Nat := 4983230072969 + 3 ^ 40 * 5057336 * 2
def baseEnd_5057336 : Nat := 288538244365192264815749

theorem tailTrace_5057336 : CollatzResearch.WordTrace tailWord_5057336 prefixEnd_5057336 288538244365192264815749 := by
  unfold tailWord_5057336
  simp only [CollatzResearch.WordTrace]
  refine ⟨92228098803071435534655931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122970798404095247379541241 92228098803071435534655931)
  ·
    refine ⟨138342148204607153301983897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92228098803071435534655931 138342148204607153301983897)
    ·
      refine ⟨103756611153455364976487923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138342148204607153301983897 103756611153455364976487923)
      ·
        refine ⟨155634916730183047464731885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103756611153455364976487923 155634916730183047464731885)
        ·
          refine ⟨58363093773818642799274457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155634916730183047464731885 58363093773818642799274457)
          ·
            refine ⟨43772320330363982099455843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58363093773818642799274457 43772320330363982099455843)
            ·
              refine ⟨65658480495545973149183765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43772320330363982099455843 65658480495545973149183765)
              ·
                refine ⟨3077741273228717491367989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65658480495545973149183765 3077741273228717491367989)
                ·
                  refine ⟨288538244365192264815749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3077741273228717491367989 288538244365192264815749)
                  ·
                    rfl

theorem cell23_5057336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 6, 5].length) (baseStart_5057336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057336 prefixEnd_5057336 := by exact prefixLift 5057336
  have htrace : WordTrace (prefixWord ++ tailWord_5057336) baseStart_5057336 baseEnd_5057336 := by
    simpa [prefixWord, tailWord_5057336, baseEnd_5057336] using wordTrace_append hprefix tailTrace_5057336
  have hstable : (prefixWord ++ tailWord_5057336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057336).length < 2 ^ (prefixWord ++ tailWord_5057336).sum := by decide
  have hdescent : baseEnd_5057336 < baseStart_5057336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057349 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 6, 5]
def baseStart_5057349 : Nat := 118140960795 + 5057349 * 2 ^ 59
def prefixEnd_5057349 : Nat := 4983230072969 + 3 ^ 40 * 5057349 * 2
def baseEnd_5057349 : Nat := 865616958178412944159727

theorem tailTrace_5057349 : CollatzResearch.WordTrace tailWord_5057349 prefixEnd_5057349 865616958178412944159727 := by
  unfold tailWord_5057349
  simp only [CollatzResearch.WordTrace]
  refine ⟨184456671755095774289535101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122971114503397182859690067 184456671755095774289535101)
  ·
    refine ⟨69171251908160915358575663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184456671755095774289535101 69171251908160915358575663)
    ·
      refine ⟨103756877862241373037863495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69171251908160915358575663 103756877862241373037863495)
      ·
        refine ⟨155635316793362059556795243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103756877862241373037863495 155635316793362059556795243)
        ·
          refine ⟨233452975190043089335192865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155635316793362059556795243 233452975190043089335192865)
          ·
            refine ⟨175089731392532317001394649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233452975190043089335192865 175089731392532317001394649)
            ·
              refine ⟨131317298544399237751045987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175089731392532317001394649 131317298544399237751045987)
              ·
                refine ⟨196975947816598856626568981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131317298544399237751045987 196975947816598856626568981)
                ·
                  refine ⟨9233247553903071404370421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 196975947816598856626568981 9233247553903071404370421)
                  ·
                    refine ⟨865616958178412944159727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9233247553903071404370421 865616958178412944159727)
                    ·
                      rfl

theorem cell23_5057349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 5].length) (baseStart_5057349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057349 prefixEnd_5057349 := by exact prefixLift 5057349
  have htrace : WordTrace (prefixWord ++ tailWord_5057349) baseStart_5057349 baseEnd_5057349 := by
    simpa [prefixWord, tailWord_5057349, baseEnd_5057349] using wordTrace_append hprefix tailTrace_5057349
  have hstable : (prefixWord ++ tailWord_5057349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057349).length < 2 ^ (prefixWord ++ tailWord_5057349).sum := by decide
  have hdescent : baseEnd_5057349 < baseStart_5057349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057399 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 6]
def baseStart_5057399 : Nat := 118140960795 + 5057399 * 2 ^ 59
def prefixEnd_5057399 : Nat := 4983230072969 + 3 ^ 40 * 5057399 * 2
def baseEnd_5057399 : Nat := 2596876548567963636853951

theorem tailTrace_5057399 : CollatzResearch.WordTrace tailWord_5057399 prefixEnd_5057399 2596876548567963636853951 := by
  unfold tailWord_5057399
  simp only [CollatzResearch.WordTrace]
  refine ⟨184458495404914632828855251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122972330269943088552570167 184458495404914632828855251)
  ·
    refine ⟨276687743107371949243282877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184458495404914632828855251 276687743107371949243282877)
    ·
      refine ⟨103757903665264480966231079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 276687743107371949243282877 103757903665264480966231079)
      ·
        refine ⟨155636855497896721449346619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103757903665264480966231079 155636855497896721449346619)
        ·
          refine ⟨233455283246845082174019929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155636855497896721449346619 233455283246845082174019929)
          ·
            refine ⟨175091462435133811630514947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233455283246845082174019929 175091462435133811630514947)
            ·
              refine ⟨262637193652700717445772421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175091462435133811630514947 262637193652700717445772421)
              ·
                refine ⟨49244473809881384521082329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 262637193652700717445772421 49244473809881384521082329)
                ·
                  refine ⟨36933355357411038390811747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49244473809881384521082329 36933355357411038390811747)
                  ·
                    refine ⟨55400033036116557586217621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36933355357411038390811747 55400033036116557586217621)
                    ·
                      refine ⟨2596876548567963636853951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55400033036116557586217621 2596876548567963636853951)
                      ·
                        rfl

theorem cell23_5057399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_5057399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057399 prefixEnd_5057399 := by exact prefixLift 5057399
  have htrace : WordTrace (prefixWord ++ tailWord_5057399) baseStart_5057399 baseEnd_5057399 := by
    simpa [prefixWord, tailWord_5057399, baseEnd_5057399] using wordTrace_append hprefix tailTrace_5057399
  have hstable : (prefixWord ++ tailWord_5057399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057399).length < 2 ^ (prefixWord ++ tailWord_5057399).sum := by decide
  have hdescent : baseEnd_5057399 < baseStart_5057399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057447 : List Nat := [1, 1, 6, 1, 3, 1, 1, 4, 1, 4]
def baseStart_5057447 : Nat := 118140960795 + 5057447 * 2 ^ 59
def prefixEnd_5057447 : Nat := 4983230072969 + 3 ^ 40 * 5057447 * 2
def baseEnd_5057447 : Nat := 865633731879793149684577

theorem tailTrace_5057447 : CollatzResearch.WordTrace tailWord_5057447 prefixEnd_5057447 865633731879793149684577 := by
  unfold tailWord_5057447
  simp only [CollatzResearch.WordTrace]
  refine ⟨184460246108740737026602595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122973497405827158017735063 184460246108740737026602595)
  ·
    refine ⟨276690369163111105539903893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184460246108740737026602595 276690369163111105539903893)
    ·
      refine ⟨12969861054520833072182995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 276690369163111105539903893 12969861054520833072182995)
      ·
        refine ⟨19454791581781249608274493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12969861054520833072182995 19454791581781249608274493)
        ·
          refine ⟨7295546843167968603102935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19454791581781249608274493 7295546843167968603102935)
          ·
            refine ⟨10943320264751952904654403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7295546843167968603102935 10943320264751952904654403)
            ·
              refine ⟨16414980397127929356981605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10943320264751952904654403 16414980397127929356981605)
              ·
                refine ⟨3077808824461486754434051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16414980397127929356981605 3077808824461486754434051)
                ·
                  refine ⟨4616713236692230131651077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3077808824461486754434051 4616713236692230131651077)
                  ·
                    refine ⟨865633731879793149684577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4616713236692230131651077 865633731879793149684577)
                    ·
                      rfl

theorem cell23_5057447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_5057447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057447 prefixEnd_5057447 := by exact prefixLift 5057447
  have htrace : WordTrace (prefixWord ++ tailWord_5057447) baseStart_5057447 baseEnd_5057447 := by
    simpa [prefixWord, tailWord_5057447, baseEnd_5057447] using wordTrace_append hprefix tailTrace_5057447
  have hstable : (prefixWord ++ tailWord_5057447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057447).length < 2 ^ (prefixWord ++ tailWord_5057447).sum := by decide
  have hdescent : baseEnd_5057447 < baseStart_5057447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057460 : List Nat := [2, 5, 2, 1, 1, 1, 2, 3, 6]
def baseStart_5057460 : Nat := 118140960795 + 5057460 * 2 ^ 59
def prefixEnd_5057460 : Nat := 4983230072969 + 3 ^ 40 * 5057460 * 2
def baseEnd_5057460 : Nat := 288545318987543099799019

theorem tailTrace_5057460 : CollatzResearch.WordTrace tailWord_5057460 prefixEnd_5057460 288545318987543099799019 := by
  unfold tailWord_5057460
  simp only [CollatzResearch.WordTrace]
  refine ⟨92230360128846820123412917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122973813505129093497883889 92230360128846820123412917)
  ·
    refine ⟨8646596262079389386569961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92230360128846820123412917 8646596262079389386569961)
    ·
      refine ⟨6484947196559542039927471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8646596262079389386569961 6484947196559542039927471)
      ·
        refine ⟨9727420794839313059891207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6484947196559542039927471 9727420794839313059891207)
        ·
          refine ⟨14591131192258969589836811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9727420794839313059891207 14591131192258969589836811)
          ·
            refine ⟨21886696788388454384755217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14591131192258969589836811 21886696788388454384755217)
            ·
              refine ⟨16415022591291340788566413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21886696788388454384755217 16415022591291340788566413)
              ·
                refine ⟨6155633471734252795712405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16415022591291340788566413 6155633471734252795712405)
                ·
                  refine ⟨288545318987543099799019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6155633471734252795712405 288545318987543099799019)
                  ·
                    rfl

theorem cell23_5057460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_5057460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057460 prefixEnd_5057460 := by exact prefixLift 5057460
  have htrace : WordTrace (prefixWord ++ tailWord_5057460) baseStart_5057460 baseEnd_5057460 := by
    simpa [prefixWord, tailWord_5057460, baseEnd_5057460] using wordTrace_append hprefix tailTrace_5057460
  have hstable : (prefixWord ++ tailWord_5057460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057460).length < 2 ^ (prefixWord ++ tailWord_5057460).sum := by decide
  have hdescent : baseEnd_5057460 < baseStart_5057460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057463 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 4, 3, 2]
def baseStart_5057463 : Nat := 118140960795 + 5057463 * 2 ^ 59
def prefixEnd_5057463 : Nat := 4983230072969 + 3 ^ 40 * 5057463 * 2
def baseEnd_5057463 : Nat := 2596909411329851386453657

theorem tailTrace_5057463 : CollatzResearch.WordTrace tailWord_5057463 prefixEnd_5057463 2596909411329851386453657 := by
  unfold tailWord_5057463
  simp only [CollatzResearch.WordTrace]
  refine ⟨184460829676682771759185043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122973886451121847839456695 184460829676682771759185043)
  ·
    refine ⟨276691244515024157638777565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184460829676682771759185043 276691244515024157638777565)
    ·
      refine ⟨103759216693134059114541587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 276691244515024157638777565 103759216693134059114541587)
      ·
        refine ⟨155638825039701088671812381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103759216693134059114541587 155638825039701088671812381)
        ·
          refine ⟨58364559389887908251929643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155638825039701088671812381 58364559389887908251929643)
          ·
            refine ⟨87546839084831862377894465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58364559389887908251929643 87546839084831862377894465)
            ·
              refine ⟨65660129313623896783420849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87546839084831862377894465 65660129313623896783420849)
              ·
                refine ⟨49245096985217922587565637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65660129313623896783420849 49245096985217922587565637)
                ·
                  refine ⟨9233455684728360485168557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49245096985217922587565637 9233455684728360485168557)
                  ·
                    refine ⟨3462545881773135181938209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9233455684728360485168557 3462545881773135181938209)
                    ·
                      refine ⟨2596909411329851386453657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3462545881773135181938209 2596909411329851386453657)
                      ·
                        rfl

theorem cell23_5057463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 3, 2].length) (baseStart_5057463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057463 prefixEnd_5057463 := by exact prefixLift 5057463
  have htrace : WordTrace (prefixWord ++ tailWord_5057463) baseStart_5057463 baseEnd_5057463 := by
    simpa [prefixWord, tailWord_5057463, baseEnd_5057463] using wordTrace_append hprefix tailTrace_5057463
  have hstable : (prefixWord ++ tailWord_5057463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057463).length < 2 ^ (prefixWord ++ tailWord_5057463).sum := by decide
  have hdescent : baseEnd_5057463 < baseStart_5057463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057470 : List Nat := [4, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3]
def baseStart_5057470 : Nat := 118140960795 + 5057470 * 2 ^ 59
def prefixEnd_5057470 : Nat := 4983230072969 + 3 ^ 40 * 5057470 * 2
def baseEnd_5057470 : Nat := 2596913005694432859066125

theorem tailTrace_5057470 : CollatzResearch.WordTrace tailWord_5057470 prefixEnd_5057470 2596913005694432859066125 := by
  unfold tailWord_5057470
  simp only [CollatzResearch.WordTrace]
  refine ⟨23057635623457176494336233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122974056658438274636459909 23057635623457176494336233)
  ·
    refine ⟨17293226717592882370752175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23057635623457176494336233 17293226717592882370752175)
    ·
      refine ⟨25939840076389323556128263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17293226717592882370752175 25939840076389323556128263)
      ·
        refine ⟨38909760114583985334192395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25939840076389323556128263 38909760114583985334192395)
        ·
          refine ⟨58364640171875978001288593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38909760114583985334192395 58364640171875978001288593)
          ·
            refine ⟨43773480128906983500966445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58364640171875978001288593 43773480128906983500966445)
            ·
              refine ⟨16415055048340118812862417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43773480128906983500966445 16415055048340118812862417)
              ·
                refine ⟨12311291286255089109646813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16415055048340118812862417 12311291286255089109646813)
                ·
                  refine ⟨4616734232345658416117555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12311291286255089109646813 4616734232345658416117555)
                  ·
                    refine ⟨6925101348518487624176333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4616734232345658416117555 6925101348518487624176333)
                    ·
                      refine ⟨2596913005694432859066125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6925101348518487624176333 2596913005694432859066125)
                      ·
                        rfl

theorem cell23_5057470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_5057470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057470 prefixEnd_5057470 := by exact prefixLift 5057470
  have htrace : WordTrace (prefixWord ++ tailWord_5057470) baseStart_5057470 baseEnd_5057470 := by
    simpa [prefixWord, tailWord_5057470, baseEnd_5057470] using wordTrace_append hprefix tailTrace_5057470
  have hstable : (prefixWord ++ tailWord_5057470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057470).length < 2 ^ (prefixWord ++ tailWord_5057470).sum := by decide
  have hdescent : baseEnd_5057470 < baseStart_5057470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057480 : List Nat := [2, 1, 3, 1, 5, 1, 1, 1, 1, 5, 2]
def baseStart_5057480 : Nat := 118140960795 + 5057480 * 2 ^ 59
def prefixEnd_5057480 : Nat := 4983230072969 + 3 ^ 40 * 5057480 * 2
def baseEnd_5057480 : Nat := 2596918140500977819941079

theorem tailTrace_5057480 : CollatzResearch.WordTrace tailWord_5057480 prefixEnd_5057480 2596918140500977819941079 := by
  unfold tailWord_5057480
  simp only [CollatzResearch.WordTrace]
  refine ⟨92230724858810591831276947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122974299811747455775035929 92230724858810591831276947)
  ·
    refine ⟨138346087288215887746915421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92230724858810591831276947 138346087288215887746915421)
    ·
      refine ⟨51879782733080957905093283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138346087288215887746915421 51879782733080957905093283)
      ·
        refine ⟨77819674099621436857639925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51879782733080957905093283 77819674099621436857639925)
        ·
          refine ⟨7295594446839509705403743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77819674099621436857639925 7295594446839509705403743)
          ·
            refine ⟨10943391670259264558105615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7295594446839509705403743 10943391670259264558105615)
            ·
              refine ⟨16415087505388896837158423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10943391670259264558105615 16415087505388896837158423)
              ·
                refine ⟨24622631258083345255737635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16415087505388896837158423 24622631258083345255737635)
                ·
                  refine ⟨36933946887125017883606453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24622631258083345255737635 36933946887125017883606453)
                  ·
                    refine ⟨3462557520667970426588105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36933946887125017883606453 3462557520667970426588105)
                    ·
                      refine ⟨2596918140500977819941079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3462557520667970426588105 2596918140500977819941079)
                      ·
                        rfl

theorem cell23_5057480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 1, 5, 2].length) (baseStart_5057480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057480 prefixEnd_5057480 := by exact prefixLift 5057480
  have htrace : WordTrace (prefixWord ++ tailWord_5057480) baseStart_5057480 baseEnd_5057480 := by
    simpa [prefixWord, tailWord_5057480, baseEnd_5057480] using wordTrace_append hprefix tailTrace_5057480
  have hstable : (prefixWord ++ tailWord_5057480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057480).length < 2 ^ (prefixWord ++ tailWord_5057480).sum := by decide
  have hdescent : baseEnd_5057480 < baseStart_5057480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057487 : List Nat := [1, 1, 2, 1, 1, 7, 2, 3, 1, 1, 3]
def baseStart_5057487 : Nat := 118140960795 + 5057487 * 2 ^ 59
def prefixEnd_5057487 : Nat := 4983230072969 + 3 ^ 40 * 5057487 * 2
def baseEnd_5057487 : Nat := 2596921734865559292553547

theorem tailTrace_5057487 : CollatzResearch.WordTrace tailWord_5057487 prefixEnd_5057487 2596921734865559292553547 := by
  unfold tailWord_5057487
  simp only [CollatzResearch.WordTrace]
  refine ⟨184461705028595823858058715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122974470019063882572039143 184461705028595823858058715)
  ·
    refine ⟨276692557542893735787088073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184461705028595823858058715 276692557542893735787088073)
    ·
      refine ⟨207519418157170301840316055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276692557542893735787088073 207519418157170301840316055)
      ·
        refine ⟨311279127235755452760474083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207519418157170301840316055 311279127235755452760474083)
        ·
          refine ⟨466918690853633179140711125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311279127235755452760474083 466918690853633179140711125)
          ·
            refine ⟨10943406816882027636110417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 466918690853633179140711125 10943406816882027636110417)
            ·
              refine ⟨8207555112661520727082813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10943406816882027636110417 8207555112661520727082813)
              ·
                refine ⟨3077833167248070272656055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8207555112661520727082813 3077833167248070272656055)
                ·
                  refine ⟨4616749750872105408984083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3077833167248070272656055 4616749750872105408984083)
                  ·
                    refine ⟨6925124626308158113476125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4616749750872105408984083 6925124626308158113476125)
                    ·
                      refine ⟨2596921734865559292553547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6925124626308158113476125 2596921734865559292553547)
                      ·
                        rfl

theorem cell23_5057487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 3, 1, 1, 3].length) (baseStart_5057487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057487 prefixEnd_5057487 := by exact prefixLift 5057487
  have htrace : WordTrace (prefixWord ++ tailWord_5057487) baseStart_5057487 baseEnd_5057487 := by
    simpa [prefixWord, tailWord_5057487, baseEnd_5057487] using wordTrace_append hprefix tailTrace_5057487
  have hstable : (prefixWord ++ tailWord_5057487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057487).length < 2 ^ (prefixWord ++ tailWord_5057487).sum := by decide
  have hdescent : baseEnd_5057487 < baseStart_5057487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057490 : List Nat := [3, 2, 2, 3, 1, 2, 1, 3, 1, 5]
def baseStart_5057490 : Nat := 118140960795 + 5057490 * 2 ^ 59
def prefixEnd_5057490 : Nat := 4983230072969 + 3 ^ 40 * 5057490 * 2
def baseEnd_5057490 : Nat := 865641091769174260272011

theorem tailTrace_5057490 : CollatzResearch.WordTrace tailWord_5057490 prefixEnd_5057490 865641091769174260272011 := by
  unfold tailWord_5057490
  simp only [CollatzResearch.WordTrace]
  refine ⟨46115453611896238842604481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122974542965056636913611949 46115453611896238842604481)
  ·
    refine ⟨34586590208922179131953361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46115453611896238842604481 34586590208922179131953361)
    ·
      refine ⟨25939942656691634348965021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34586590208922179131953361 25939942656691634348965021)
      ·
        refine ⟨9727478496259362880861883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25939942656691634348965021 9727478496259362880861883)
        ·
          refine ⟨14591217744389044321292825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9727478496259362880861883 14591217744389044321292825)
          ·
            refine ⟨10943413308291783240969619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14591217744389044321292825 10943413308291783240969619)
            ·
              refine ⟨16415119962437674861454429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10943413308291783240969619 16415119962437674861454429)
              ·
                refine ⟨6155669985914128073045411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16415119962437674861454429 6155669985914128073045411)
                ·
                  refine ⟨9233504978871192109568117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6155669985914128073045411 9233504978871192109568117)
                  ·
                    refine ⟨865641091769174260272011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9233504978871192109568117 865641091769174260272011)
                    ·
                      rfl

theorem cell23_5057490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_5057490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057490 prefixEnd_5057490 := by exact prefixLift 5057490
  have htrace : WordTrace (prefixWord ++ tailWord_5057490) baseStart_5057490 baseEnd_5057490 := by
    simpa [prefixWord, tailWord_5057490, baseEnd_5057490] using wordTrace_append hprefix tailTrace_5057490
  have hstable : (prefixWord ++ tailWord_5057490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057490).length < 2 ^ (prefixWord ++ tailWord_5057490).sum := by decide
  have hdescent : baseEnd_5057490 < baseStart_5057490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057538 : List Nat := [3, 4, 1, 3, 1, 2, 1, 3, 1, 1, 3]
def baseStart_5057538 : Nat := 118140960795 + 5057538 * 2 ^ 59
def prefixEnd_5057538 : Nat := 4983230072969 + 3 ^ 40 * 5057538 * 2
def baseEnd_5057538 : Nat := 2596947922378938593015813

theorem tailTrace_5057538 : CollatzResearch.WordTrace tailWord_5057538 prefixEnd_5057538 2596947922378938593015813 := by
  unfold tailWord_5057538
  simp only [CollatzResearch.WordTrace]
  refine ⟨46115891287852764892041317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122975710100940706378776845 46115891287852764892041317)
  ·
    refine ⟨8646729616472393417257747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46115891287852764892041317 8646729616472393417257747)
    ·
      refine ⟨12970094424708590125886621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8646729616472393417257747 12970094424708590125886621)
      ·
        refine ⟨4863785409265721297207483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12970094424708590125886621 4863785409265721297207483)
        ·
          refine ⟨7295678113898581945811225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4863785409265721297207483 7295678113898581945811225)
          ·
            refine ⟨5471758585423936459358419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7295678113898581945811225 5471758585423936459358419)
            ·
              refine ⟨8207637878135904689037629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5471758585423936459358419 8207637878135904689037629)
              ·
                refine ⟨3077864204300964258389111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8207637878135904689037629 3077864204300964258389111)
                ·
                  refine ⟨4616796306451446387583667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3077864204300964258389111 4616796306451446387583667)
                  ·
                    refine ⟨6925194459677169581375501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4616796306451446387583667 6925194459677169581375501)
                    ·
                      refine ⟨2596947922378938593015813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6925194459677169581375501 2596947922378938593015813)
                      ·
                        rfl

theorem cell23_5057538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_5057538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057538 prefixEnd_5057538 := by exact prefixLift 5057538
  have htrace : WordTrace (prefixWord ++ tailWord_5057538) baseStart_5057538 baseEnd_5057538 := by
    simpa [prefixWord, tailWord_5057538, baseEnd_5057538] using wordTrace_append hprefix tailTrace_5057538
  have hstable : (prefixWord ++ tailWord_5057538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057538).length < 2 ^ (prefixWord ++ tailWord_5057538).sum := by decide
  have hdescent : baseEnd_5057538 < baseStart_5057538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057543 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 3, 3, 3]
def baseStart_5057543 : Nat := 118140960795 + 5057543 * 2 ^ 59
def prefixEnd_5057543 : Nat := 4983230072969 + 3 ^ 40 * 5057543 * 2
def baseEnd_5057543 : Nat := 2596950489782211073453289

theorem tailTrace_5057543 : CollatzResearch.WordTrace tailWord_5057543 prefixEnd_5057543 2596950489782211073453289 := by
  unfold tailWord_5057543
  simp only [CollatzResearch.WordTrace]
  refine ⟨184463747516392945422097283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122975831677595296948064855 184463747516392945422097283)
  ·
    refine ⟨276695621274589418133145925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184463747516392945422097283 276695621274589418133145925)
    ·
      refine ⟨51880428988985515899964861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 276695621274589418133145925 51880428988985515899964861)
      ·
        refine ⟨19455160870869568462486823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51880428988985515899964861 19455160870869568462486823)
        ·
          refine ⟨29182741306304352693730235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19455160870869568462486823 29182741306304352693730235)
          ·
            refine ⟨43774111959456529040595353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29182741306304352693730235 43774111959456529040595353)
            ·
              refine ⟨32830583969592396780446515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43774111959456529040595353 32830583969592396780446515)
              ·
                refine ⟨49245875954388595170669773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32830583969592396780446515 49245875954388595170669773)
                ·
                  refine ⟨18467203482895723189001165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49245875954388595170669773 18467203482895723189001165)
                  ·
                    refine ⟨6925201306085896195875437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18467203482895723189001165 6925201306085896195875437)
                    ·
                      refine ⟨2596950489782211073453289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6925201306085896195875437 2596950489782211073453289)
                      ·
                        rfl

theorem cell23_5057543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_5057543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057543 prefixEnd_5057543 := by exact prefixLift 5057543
  have htrace : WordTrace (prefixWord ++ tailWord_5057543) baseStart_5057543 baseEnd_5057543 := by
    simpa [prefixWord, tailWord_5057543, baseEnd_5057543] using wordTrace_append hprefix tailTrace_5057543
  have hstable : (prefixWord ++ tailWord_5057543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057543).length < 2 ^ (prefixWord ++ tailWord_5057543).sum := by decide
  have hdescent : baseEnd_5057543 < baseStart_5057543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057544 : List Nat := [2, 1, 3, 2, 1, 3, 3, 3, 1, 2, 2]
def baseStart_5057544 : Nat := 118140960795 + 5057544 * 2 ^ 59
def prefixEnd_5057544 : Nat := 4983230072969 + 3 ^ 40 * 5057544 * 2
def baseEnd_5057544 : Nat := 2596951003262865569540785

theorem tailTrace_5057544 : CollatzResearch.WordTrace tailWord_5057544 prefixEnd_5057544 2596951003262865569540785 := by
  unfold tailWord_5057544
  simp only [CollatzResearch.WordTrace]
  refine ⟨92231891994694661296441843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122975855992926215061922457 92231891994694661296441843)
  ·
    refine ⟨138347837992041991944662765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92231891994694661296441843 138347837992041991944662765)
    ·
      refine ⟨51880439247015746979248537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138347837992041991944662765 51880439247015746979248537)
      ·
        refine ⟨38910329435261810234436403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51880439247015746979248537 38910329435261810234436403)
        ·
          refine ⟨58365494152892715351654605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38910329435261810234436403 58365494152892715351654605)
          ·
            refine ⟨21887060307334768256870477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58365494152892715351654605 21887060307334768256870477)
            ·
              refine ⟨8207647615250538096326429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21887060307334768256870477 8207647615250538096326429)
              ·
                refine ⟨3077867855718951786122411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8207647615250538096326429 3077867855718951786122411)
                ·
                  refine ⟨4616801783578427679183617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3077867855718951786122411 4616801783578427679183617)
                  ·
                    refine ⟨3462601337683820759387713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4616801783578427679183617 3462601337683820759387713)
                    ·
                      refine ⟨2596951003262865569540785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3462601337683820759387713 2596951003262865569540785)
                      ·
                        rfl

theorem cell23_5057544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_5057544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057544 prefixEnd_5057544 := by exact prefixLift 5057544
  have htrace : WordTrace (prefixWord ++ tailWord_5057544) baseStart_5057544 baseEnd_5057544 := by
    simpa [prefixWord, tailWord_5057544, baseEnd_5057544] using wordTrace_append hprefix tailTrace_5057544
  have hstable : (prefixWord ++ tailWord_5057544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057544).length < 2 ^ (prefixWord ++ tailWord_5057544).sum := by decide
  have hdescent : baseEnd_5057544 < baseStart_5057544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057560 : List Nat := [2, 1, 2, 3, 2, 2, 2, 1, 4, 1, 3]
def baseStart_5057560 : Nat := 118140960795 + 5057560 * 2 ^ 59
def prefixEnd_5057560 : Nat := 4983230072969 + 3 ^ 40 * 5057560 * 2
def baseEnd_5057560 : Nat := 2596959218953337506940711

theorem tailTrace_5057560 : CollatzResearch.WordTrace tailWord_5057560 prefixEnd_5057560 2596959218953337506940711 := by
  unfold tailWord_5057560
  simp only [CollatzResearch.WordTrace]
  refine ⟨92232183778665678662733067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122976245038220904883644089 92232183778665678662733067)
  ·
    refine ⟨138348275667998517994099601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92232183778665678662733067 138348275667998517994099601)
    ·
      refine ⟨103761206750998888495574701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138348275667998517994099601 103761206750998888495574701)
      ·
        refine ⟨38910452531624583185840513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103761206750998888495574701 38910452531624583185840513)
        ·
          refine ⟨29182839398718437389380385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38910452531624583185840513 29182839398718437389380385)
          ·
            refine ⟨21887129549038828042035289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29182839398718437389380385 21887129549038828042035289)
            ·
              refine ⟨16415347161779121031526467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21887129549038828042035289 16415347161779121031526467)
              ·
                refine ⟨24623020742668681547289701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16415347161779121031526467 24623020742668681547289701)
                ·
                  refine ⟨4616816389250377790116819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24623020742668681547289701 4616816389250377790116819)
                  ·
                    refine ⟨6925224583875566685175229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4616816389250377790116819 6925224583875566685175229)
                    ·
                      refine ⟨2596959218953337506940711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6925224583875566685175229 2596959218953337506940711)
                      ·
                        rfl

theorem cell23_5057560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_5057560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057560 prefixEnd_5057560 := by exact prefixLift 5057560
  have htrace : WordTrace (prefixWord ++ tailWord_5057560) baseStart_5057560 baseEnd_5057560 := by
    simpa [prefixWord, tailWord_5057560, baseEnd_5057560] using wordTrace_append hprefix tailTrace_5057560
  have hstable : (prefixWord ++ tailWord_5057560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057560).length < 2 ^ (prefixWord ++ tailWord_5057560).sum := by decide
  have hdescent : baseEnd_5057560 < baseStart_5057560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057600 : List Nat := [2, 1, 1, 2, 2, 3, 3, 2, 1, 4, 2]
def baseStart_5057600 : Nat := 118140960795 + 5057600 * 2 ^ 59
def prefixEnd_5057600 : Nat := 4983230072969 + 3 ^ 40 * 5057600 * 2
def baseEnd_5057600 : Nat := 2596979758179517350440527

theorem tailTrace_5057600 : CollatzResearch.WordTrace tailWord_5057600 prefixEnd_5057600 2596979758179517350440527 := by
  unfold tailWord_5057600
  simp only [CollatzResearch.WordTrace]
  refine ⟨92232913238593222078461127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122977217651457629437948169 92232913238593222078461127)
  ·
    refine ⟨138349369857889833117691691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92232913238593222078461127 138349369857889833117691691)
    ·
      refine ⟨207524054786834749676537537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138349369857889833117691691 207524054786834749676537537)
      ·
        refine ⟨155643041090126062257403153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207524054786834749676537537 155643041090126062257403153)
        ·
          refine ⟨116732280817594546693052365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155643041090126062257403153 116732280817594546693052365)
          ·
            refine ⟨43774605306597955009894637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116732280817594546693052365 43774605306597955009894637)
            ·
              refine ⟨16415476989974233128710489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43774605306597955009894637 16415476989974233128710489)
              ·
                refine ⟨12311607742480674846532867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16415476989974233128710489 12311607742480674846532867)
                ·
                  refine ⟨18467411613721012269799301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12311607742480674846532867 18467411613721012269799301)
                  ·
                    refine ⟨3462639677572689800587369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18467411613721012269799301 3462639677572689800587369)
                    ·
                      refine ⟨2596979758179517350440527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3462639677572689800587369 2596979758179517350440527)
                      ·
                        rfl

theorem cell23_5057600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 1, 4, 2].length) (baseStart_5057600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057600 prefixEnd_5057600 := by exact prefixLift 5057600
  have htrace : WordTrace (prefixWord ++ tailWord_5057600) baseStart_5057600 baseEnd_5057600 := by
    simpa [prefixWord, tailWord_5057600, baseEnd_5057600] using wordTrace_append hprefix tailTrace_5057600
  have hstable : (prefixWord ++ tailWord_5057600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057600).length < 2 ^ (prefixWord ++ tailWord_5057600).sum := by decide
  have hdescent : baseEnd_5057600 < baseStart_5057600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057616 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 7]
def baseStart_5057616 : Nat := 118140960795 + 5057616 * 2 ^ 59
def prefixEnd_5057616 : Nat := 4983230072969 + 3 ^ 40 * 5057616 * 2
def baseEnd_5057616 : Nat := 2596987973869989287840453

theorem tailTrace_5057616 : CollatzResearch.WordTrace tailWord_5057616 prefixEnd_5057616 2596987973869989287840453 := by
  unfold tailWord_5057616
  simp only [CollatzResearch.WordTrace]
  refine ⟨92233205022564239444752351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122977606696752319259669801 92233205022564239444752351)
  ·
    refine ⟨138349807533846359167128527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92233205022564239444752351 138349807533846359167128527)
    ·
      refine ⟨207524711300769538750692791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138349807533846359167128527 207524711300769538750692791)
      ·
        refine ⟨311287066951154308126039187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207524711300769538750692791 311287066951154308126039187)
        ·
          refine ⟨466930600426731462189058781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311287066951154308126039187 466930600426731462189058781)
          ·
            refine ⟨175098975160024298320897043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 466930600426731462189058781 175098975160024298320897043)
            ·
              refine ⟨262648462740036447481345565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175098975160024298320897043 262648462740036447481345565)
              ·
                refine ⟨98493173527513667805504587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 262648462740036447481345565 98493173527513667805504587)
                ·
                  refine ⟨147739760291270501708256881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98493173527513667805504587 147739760291270501708256881)
                  ·
                    refine ⟨110804820218452876281192661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 147739760291270501708256881 110804820218452876281192661)
                    ·
                      refine ⟨2596987973869989287840453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 110804820218452876281192661 2596987973869989287840453)
                      ·
                        rfl

theorem cell23_5057616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 7].length) (baseStart_5057616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057616 prefixEnd_5057616 := by exact prefixLift 5057616
  have htrace : WordTrace (prefixWord ++ tailWord_5057616) baseStart_5057616 baseEnd_5057616 := by
    simpa [prefixWord, tailWord_5057616, baseEnd_5057616] using wordTrace_append hprefix tailTrace_5057616
  have hstable : (prefixWord ++ tailWord_5057616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057616).length < 2 ^ (prefixWord ++ tailWord_5057616).sum := by decide
  have hdescent : baseEnd_5057616 < baseStart_5057616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057617 : List Nat := [1, 2, 2, 1, 3, 1, 3, 4, 2, 2, 2]
def baseStart_5057617 : Nat := 118140960795 + 5057617 * 2 ^ 59
def prefixEnd_5057617 : Nat := 4983230072969 + 3 ^ 40 * 5057617 * 2
def baseEnd_5057617 : Nat := 2596988487350643783927949

theorem tailTrace_5057617 : CollatzResearch.WordTrace tailWord_5057617 prefixEnd_5057617 2596988487350643783927949 := by
  unfold tailWord_5057617
  simp only [CollatzResearch.WordTrace]
  refine ⟨184466446518124856060291105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122977631012083237373527403 184466446518124856060291105)
  ·
    refine ⟨138349834888593642045218329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184466446518124856060291105 138349834888593642045218329)
    ·
      refine ⟨103762376166445231533913747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138349834888593642045218329 103762376166445231533913747)
      ·
        refine ⟨155643564249667847300870621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103762376166445231533913747 155643564249667847300870621)
        ·
          refine ⟨58366336593625442737826483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155643564249667847300870621 58366336593625442737826483)
          ·
            refine ⟨87549504890438164106739725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58366336593625442737826483 87549504890438164106739725)
            ·
              refine ⟨32831064333914311540027397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87549504890438164106739725 32831064333914311540027397)
              ·
                refine ⟨6155824562608933413755137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32831064333914311540027397 6155824562608933413755137)
                ·
                  refine ⟨4616868421956700060316353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6155824562608933413755137 4616868421956700060316353)
                  ·
                    refine ⟨3462651316467525045237265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4616868421956700060316353 3462651316467525045237265)
                    ·
                      refine ⟨2596988487350643783927949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3462651316467525045237265 2596988487350643783927949)
                      ·
                        rfl

theorem cell23_5057617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 2, 2, 2].length) (baseStart_5057617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057617 prefixEnd_5057617 := by exact prefixLift 5057617
  have htrace : WordTrace (prefixWord ++ tailWord_5057617) baseStart_5057617 baseEnd_5057617 := by
    simpa [prefixWord, tailWord_5057617, baseEnd_5057617] using wordTrace_append hprefix tailTrace_5057617
  have hstable : (prefixWord ++ tailWord_5057617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057617).length < 2 ^ (prefixWord ++ tailWord_5057617).sum := by decide
  have hdescent : baseEnd_5057617 < baseStart_5057617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057633 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 1, 5, 3]
def baseStart_5057633 : Nat := 118140960795 + 5057633 * 2 ^ 59
def prefixEnd_5057633 : Nat := 4983230072969 + 3 ^ 40 * 5057633 * 2
def baseEnd_5057633 : Nat := 2596996703041115721327875

theorem tailTrace_5057633 : CollatzResearch.WordTrace tailWord_5057633 prefixEnd_5057633 2596996703041115721327875 := by
  unfold tailWord_5057633
  simp only [CollatzResearch.WordTrace]
  refine ⟨184467030086066890792873553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122978020057377927195249035 184467030086066890792873553)
  ·
    refine ⟨138350272564550168094655165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184467030086066890792873553 138350272564550168094655165)
    ·
      refine ⟨51881352211706313035495687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138350272564550168094655165 51881352211706313035495687)
      ·
        refine ⟨77822028317559469553243531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51881352211706313035495687 77822028317559469553243531)
        ·
          refine ⟨116733042476339204329865297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77822028317559469553243531 116733042476339204329865297)
          ·
            refine ⟨87549781857254403247398973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116733042476339204329865297 87549781857254403247398973)
            ·
              refine ⟨32831168196470401217774615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87549781857254403247398973 32831168196470401217774615)
              ·
                refine ⟨49246752294705601826661923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32831168196470401217774615 49246752294705601826661923)
                ·
                  refine ⟨73870128442058402739992885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49246752294705601826661923 73870128442058402739992885)
                  ·
                    refine ⟨6925324541442975256874333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73870128442058402739992885 6925324541442975256874333)
                    ·
                      refine ⟨2596996703041115721327875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6925324541442975256874333 2596996703041115721327875)
                      ·
                        rfl

theorem cell23_5057633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_5057633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057633 prefixEnd_5057633 := by exact prefixLift 5057633
  have htrace : WordTrace (prefixWord ++ tailWord_5057633) baseStart_5057633 baseEnd_5057633 := by
    simpa [prefixWord, tailWord_5057633, baseEnd_5057633] using wordTrace_append hprefix tailTrace_5057633
  have hstable : (prefixWord ++ tailWord_5057633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057633).length < 2 ^ (prefixWord ++ tailWord_5057633).sum := by decide
  have hdescent : baseEnd_5057633 < baseStart_5057633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057634 : List Nat := [3, 3, 2, 2, 1, 2, 2, 1, 1, 4, 2]
def baseStart_5057634 : Nat := 118140960795 + 5057634 * 2 ^ 59
def prefixEnd_5057634 : Nat := 4983230072969 + 3 ^ 40 * 5057634 * 2
def baseEnd_5057634 : Nat := 2596997216521770217415371

theorem tailTrace_5057634 : CollatzResearch.WordTrace tailWord_5057634 prefixEnd_5057634 2596997216521770217415371 := by
  unfold tailWord_5057634
  simp only [CollatzResearch.WordTrace]
  refine ⟨46116766639765816990914989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122978044372708845309106637 46116766639765816990914989)
  ·
    refine ⟨17293787489912181371593121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46116766639765816990914989 17293787489912181371593121)
    ·
      refine ⟨12970340617434136028694841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17293787489912181371593121 12970340617434136028694841)
      ·
        refine ⟨9727755463075602021521131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12970340617434136028694841 9727755463075602021521131)
        ·
          refine ⟨14591633194613403032281697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9727755463075602021521131 14591633194613403032281697)
          ·
            refine ⟨10943724895960052274211273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14591633194613403032281697 10943724895960052274211273)
            ·
              refine ⟨8207793671970039205658455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10943724895960052274211273 8207793671970039205658455)
              ·
                refine ⟨12311690507955058808487683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8207793671970039205658455 12311690507955058808487683)
                ·
                  refine ⟨18467535761932588212731525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12311690507955058808487683 18467535761932588212731525)
                  ·
                    refine ⟨3462662955362360289887161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18467535761932588212731525 3462662955362360289887161)
                    ·
                      refine ⟨2596997216521770217415371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3462662955362360289887161 2596997216521770217415371)
                      ·
                        rfl

theorem cell23_5057634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_5057634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057634 prefixEnd_5057634 := by exact prefixLift 5057634
  have htrace : WordTrace (prefixWord ++ tailWord_5057634) baseStart_5057634 baseEnd_5057634 := by
    simpa [prefixWord, tailWord_5057634, baseEnd_5057634] using wordTrace_append hprefix tailTrace_5057634
  have hstable : (prefixWord ++ tailWord_5057634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057634).length < 2 ^ (prefixWord ++ tailWord_5057634).sum := by decide
  have hdescent : baseEnd_5057634 < baseStart_5057634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057657 : List Nat := [1, 2, 1, 3, 5, 1, 2, 3, 5]
def baseStart_5057657 : Nat := 118140960795 + 5057657 * 2 ^ 59
def prefixEnd_5057657 : Nat := 4983230072969 + 3 ^ 40 * 5057657 * 2
def baseEnd_5057657 : Nat := 288556558508535958603085

theorem tailTrace_5057657 : CollatzResearch.WordTrace tailWord_5057657 prefixEnd_5057657 288556558508535958603085 := by
  unfold tailWord_5057657
  simp only [CollatzResearch.WordTrace]
  refine ⟨184467905437979942891747225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122978603625319961927831483 184467905437979942891747225)
  ·
    refine ⟨138350929078484957168810419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184467905437979942891747225 138350929078484957168810419)
    ·
      refine ⟨207526393617727435753215629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138350929078484957168810419 207526393617727435753215629)
      ·
        refine ⟨77822397606647788407455861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207526393617727435753215629 77822397606647788407455861)
        ·
          refine ⟨7295849775623230163198987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77822397606647788407455861 7295849775623230163198987)
          ·
            refine ⟨10943774663434845244798481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7295849775623230163198987 10943774663434845244798481)
            ·
              refine ⟨8207830997576133933598861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10943774663434845244798481 8207830997576133933598861)
              ·
                refine ⟨3077936624091050225099573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8207830997576133933598861 3077936624091050225099573)
                ·
                  refine ⟨288556558508535958603085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3077936624091050225099573 288556558508535958603085)
                  ·
                    rfl

theorem cell23_5057657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 3, 5].length) (baseStart_5057657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057657 prefixEnd_5057657 := by exact prefixLift 5057657
  have htrace : WordTrace (prefixWord ++ tailWord_5057657) baseStart_5057657 baseEnd_5057657 := by
    simpa [prefixWord, tailWord_5057657, baseEnd_5057657] using wordTrace_append hprefix tailTrace_5057657
  have hstable : (prefixWord ++ tailWord_5057657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057657).length < 2 ^ (prefixWord ++ tailWord_5057657).sum := by decide
  have hdescent : baseEnd_5057657 < baseStart_5057657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057690 : List Nat := [3, 1, 1, 5, 1, 1, 1, 2, 1, 3, 4]
def baseStart_5057690 : Nat := 118140960795 + 5057690 * 2 ^ 59
def prefixEnd_5057690 : Nat := 4983230072969 + 3 ^ 40 * 5057690 * 2
def baseEnd_5057690 : Nat := 2597025971438421998315113

theorem tailTrace_5057690 : CollatzResearch.WordTrace tailWord_5057690 prefixEnd_5057690 2597025971438421998315113 := by
  unfold tailWord_5057690
  simp only [CollatzResearch.WordTrace]
  refine ⟨46117277261715097381924631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122979406031240259685132349 46117277261715097381924631)
  ·
    refine ⟨69175915892572646072886947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46117277261715097381924631 69175915892572646072886947)
    ·
      refine ⟨103763873838858969109330421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69175915892572646072886947 103763873838858969109330421)
      ·
        refine ⟨9727863172393028353999727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103763873838858969109330421 9727863172393028353999727)
        ·
          refine ⟨14591794758589542530999591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9727863172393028353999727 14591794758589542530999591)
          ·
            refine ⟨21887692137884313796499387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14591794758589542530999591 21887692137884313796499387)
            ·
              refine ⟨32831538206826470694749081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21887692137884313796499387 32831538206826470694749081)
              ·
                refine ⟨24623653655119853021061811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32831538206826470694749081 24623653655119853021061811)
                ·
                  refine ⟨36935480482679779531592717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24623653655119853021061811 36935480482679779531592717)
                  ·
                    refine ⟨13850805181004917324347269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36935480482679779531592717 13850805181004917324347269)
                    ·
                      refine ⟨2597025971438421998315113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13850805181004917324347269 2597025971438421998315113)
                      ·
                        rfl

theorem cell23_5057690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_5057690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057690 prefixEnd_5057690 := by exact prefixLift 5057690
  have htrace : WordTrace (prefixWord ++ tailWord_5057690) baseStart_5057690 baseEnd_5057690 := by
    simpa [prefixWord, tailWord_5057690, baseEnd_5057690] using wordTrace_append hprefix tailTrace_5057690
  have hstable : (prefixWord ++ tailWord_5057690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057690).length < 2 ^ (prefixWord ++ tailWord_5057690).sum := by decide
  have hdescent : baseEnd_5057690 < baseStart_5057690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057760 : List Nat := [2, 1, 1, 3, 1, 5, 1, 1, 3, 5]
def baseStart_5057760 : Nat := 118140960795 + 5057760 * 2 ^ 59
def prefixEnd_5057760 : Nat := 4983230072969 + 3 ^ 40 * 5057760 * 2
def baseEnd_5057760 : Nat := 865687305028078908146597

theorem tailTrace_5057760 : CollatzResearch.WordTrace tailWord_5057760 prefixEnd_5057760 865687305028078908146597 := by
  unfold tailWord_5057760
  simp only [CollatzResearch.WordTrace]
  refine ⟨92235831078303395741373367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122981108104404527655164489 92235831078303395741373367)
  ·
    refine ⟨138353746617455093612060051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92235831078303395741373367 138353746617455093612060051)
    ·
      refine ⟨207530619926182640418090077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138353746617455093612060051 207530619926182640418090077)
      ·
        refine ⟨77823982472318490156783779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207530619926182640418090077 77823982472318490156783779)
        ·
          refine ⟨116735973708477735235175669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77823982472318490156783779 116735973708477735235175669)
          ·
            refine ⟨10943997535169787678297719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 116735973708477735235175669 10943997535169787678297719)
            ·
              refine ⟨16415996302754681517446579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10943997535169787678297719 16415996302754681517446579)
              ·
                refine ⟨24623994454132022276169869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16415996302754681517446579 24623994454132022276169869)
                ·
                  refine ⟨9233997920299508353563701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24623994454132022276169869 9233997920299508353563701)
                  ·
                    refine ⟨865687305028078908146597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9233997920299508353563701 865687305028078908146597)
                    ·
                      rfl

theorem cell23_5057760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 3, 5].length) (baseStart_5057760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057760 prefixEnd_5057760 := by exact prefixLift 5057760
  have htrace : WordTrace (prefixWord ++ tailWord_5057760) baseStart_5057760 baseEnd_5057760 := by
    simpa [prefixWord, tailWord_5057760, baseEnd_5057760] using wordTrace_append hprefix tailTrace_5057760
  have hstable : (prefixWord ++ tailWord_5057760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057760).length < 2 ^ (prefixWord ++ tailWord_5057760).sum := by decide
  have hdescent : baseEnd_5057760 < baseStart_5057760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057791 : List Nat := [1, 1, 2, 2, 1, 5, 4, 2, 1, 1, 3]
def baseStart_5057791 : Nat := 118140960795 + 5057791 * 2 ^ 59
def prefixEnd_5057791 : Nat := 4983230072969 + 3 ^ 40 * 5057791 * 2
def baseEnd_5057791 : Nat := 2597077832984526103152149

theorem tailTrace_5057791 : CollatzResearch.WordTrace tailWord_5057791 prefixEnd_5057791 2597077832984526103152149 := by
  unfold tailWord_5057791
  simp only [CollatzResearch.WordTrace]
  refine ⟨184472792819494483777125227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122981861879662989184750151 184472792819494483777125227)
  ·
    refine ⟨276709189229241725665687841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184472792819494483777125227 276709189229241725665687841)
    ·
      refine ⟨207531891921931294249265881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276709189229241725665687841 207531891921931294249265881)
      ·
        refine ⟨155648918941448470686949411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207531891921931294249265881 155648918941448470686949411)
        ·
          refine ⟨233473378412172706030424117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155648918941448470686949411 233473378412172706030424117)
          ·
            refine ⟨21888129226141191190352261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 233473378412172706030424117 21888129226141191190352261)
            ·
              refine ⟨4104024229901473348191049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21888129226141191190352261 4104024229901473348191049)
              ·
                refine ⟨3078018172426105011143287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4104024229901473348191049 3078018172426105011143287)
                ·
                  refine ⟨4617027258639157516714931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3078018172426105011143287 4617027258639157516714931)
                  ·
                    refine ⟨6925540887958736275072397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4617027258639157516714931 6925540887958736275072397)
                    ·
                      refine ⟨2597077832984526103152149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6925540887958736275072397 2597077832984526103152149)
                      ·
                        rfl

theorem cell23_5057791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 2, 1, 1, 3].length) (baseStart_5057791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057791 prefixEnd_5057791 := by exact prefixLift 5057791
  have htrace : WordTrace (prefixWord ++ tailWord_5057791) baseStart_5057791 baseEnd_5057791 := by
    simpa [prefixWord, tailWord_5057791, baseEnd_5057791] using wordTrace_append hprefix tailTrace_5057791
  have hstable : (prefixWord ++ tailWord_5057791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057791).length < 2 ^ (prefixWord ++ tailWord_5057791).sum := by decide
  have hdescent : baseEnd_5057791 < baseStart_5057791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057837 : List Nat := [1, 5, 3, 1, 1, 2, 10]
def baseStart_5057837 : Nat := 118140960795 + 5057837 * 2 ^ 59
def prefixEnd_5057837 : Nat := 4983230072969 + 3 ^ 40 * 5057837 * 2
def baseEnd_5057837 : Nat := 32062980902402875594777

theorem tailTrace_5057837 : CollatzResearch.WordTrace tailWord_5057837 prefixEnd_5057837 32062980902402875594777 := by
  unfold tailWord_5057837
  simp only [CollatzResearch.WordTrace]
  refine ⟨184474470577327833633299765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122982980384885222422199843 184474470577327833633299765)
  ·
    refine ⟨17294481616624484403121853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 184474470577327833633299765 17294481616624484403121853)
    ·
      refine ⟨6485430606234181651170695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17294481616624484403121853 6485430606234181651170695)
      ·
        refine ⟨9728145909351272476756043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6485430606234181651170695 9728145909351272476756043)
        ·
          refine ⟨14592218864026908715134065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9728145909351272476756043 14592218864026908715134065)
          ·
            refine ⟨10944164148020181536350549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14592218864026908715134065 10944164148020181536350549)
            ·
              refine ⟨32062980902402875594777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10944164148020181536350549 32062980902402875594777)
              ·
                rfl

theorem cell23_5057837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 10].length) (baseStart_5057837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057837 prefixEnd_5057837 := by exact prefixLift 5057837
  have htrace : WordTrace (prefixWord ++ tailWord_5057837) baseStart_5057837 baseEnd_5057837 := by
    simpa [prefixWord, tailWord_5057837, baseEnd_5057837] using wordTrace_append hprefix tailTrace_5057837
  have hstable : (prefixWord ++ tailWord_5057837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057837).length < 2 ^ (prefixWord ++ tailWord_5057837).sum := by decide
  have hdescent : baseEnd_5057837 < baseStart_5057837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057887 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 3, 4, 2]
def baseStart_5057887 : Nat := 118140960795 + 5057887 * 2 ^ 59
def prefixEnd_5057887 : Nat := 4983230072969 + 3 ^ 40 * 5057887 * 2
def baseEnd_5057887 : Nat := 2597127127127357727551707

theorem tailTrace_5057887 : CollatzResearch.WordTrace tailWord_5057887 prefixEnd_5057887 2597127127127357727551707 := by
  unfold tailWord_5057887
  simp only [CollatzResearch.WordTrace]
  refine ⟨184476294227146692172619915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122984196151431128115079943 184476294227146692172619915)
  ·
    refine ⟨276714441340720038258929873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184476294227146692172619915 276714441340720038258929873)
    ·
      refine ⟨207535831005540028694197405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276714441340720038258929873 207535831005540028694197405)
      ·
        refine ⟨77825936627077510760324027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207535831005540028694197405 77825936627077510760324027)
        ·
          refine ⟨116738904940616266140486041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77825936627077510760324027 116738904940616266140486041)
          ·
            refine ⟨87554178705462199605364531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116738904940616266140486041 87554178705462199605364531)
            ·
              refine ⟨131331268058193299408046797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87554178705462199605364531 131331268058193299408046797)
              ·
                refine ⟨49249225521822487278017549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131331268058193299408046797 49249225521822487278017549)
                ·
                  refine ⟨18468459570683432729256581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49249225521822487278017549 18468459570683432729256581)
                  ·
                    refine ⟨3462836169503143636735609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18468459570683432729256581 3462836169503143636735609)
                    ·
                      refine ⟨2597127127127357727551707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3462836169503143636735609 2597127127127357727551707)
                      ·
                        rfl

theorem cell23_5057887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 4, 2].length) (baseStart_5057887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057887 prefixEnd_5057887 := by exact prefixLift 5057887
  have htrace : WordTrace (prefixWord ++ tailWord_5057887) baseStart_5057887 baseEnd_5057887 := by
    simpa [prefixWord, tailWord_5057887, baseEnd_5057887] using wordTrace_append hprefix tailTrace_5057887
  have hstable : (prefixWord ++ tailWord_5057887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057887).length < 2 ^ (prefixWord ++ tailWord_5057887).sum := by decide
  have hdescent : baseEnd_5057887 < baseStart_5057887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057904 : List Nat := [2, 1, 1, 1, 4, 2, 1, 3, 4, 2, 2]
def baseStart_5057904 : Nat := 118140960795 + 5057904 * 2 ^ 59
def prefixEnd_5057904 : Nat := 4983230072969 + 3 ^ 40 * 5057904 * 2
def baseEnd_5057904 : Nat := 2597135856298484161039129

theorem tailTrace_5057904 : CollatzResearch.WordTrace tailWord_5057904 prefixEnd_5057904 2597135856298484161039129 := by
  unfold tailWord_5057904
  simp only [CollatzResearch.WordTrace]
  refine ⟨92238457134042552037994383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122984609512056736050659177 92238457134042552037994383)
  ·
    refine ⟨138357685701063828056991575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92238457134042552037994383 138357685701063828056991575)
    ·
      refine ⟨207536528551595742085487363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138357685701063828056991575 207536528551595742085487363)
      ·
        refine ⟨311304792827393613128231045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207536528551595742085487363 311304792827393613128231045)
        ·
          refine ⟨58369648655136302461543321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 311304792827393613128231045 58369648655136302461543321)
          ·
            refine ⟨43777236491352226846157491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58369648655136302461543321 43777236491352226846157491)
            ·
              refine ⟨65665854737028340269236237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43777236491352226846157491 65665854737028340269236237)
              ·
                refine ⟨24624695526385627600963589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65665854737028340269236237 24624695526385627600963589)
                ·
                  refine ⟨4617130411197305175180673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24624695526385627600963589 4617130411197305175180673)
                  ·
                    refine ⟨3462847808397978881385505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4617130411197305175180673 3462847808397978881385505)
                    ·
                      refine ⟨2597135856298484161039129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3462847808397978881385505 2597135856298484161039129)
                      ·
                        rfl

theorem cell23_5057904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 4, 2, 2].length) (baseStart_5057904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057904 prefixEnd_5057904 := by exact prefixLift 5057904
  have htrace : WordTrace (prefixWord ++ tailWord_5057904) baseStart_5057904 baseEnd_5057904 := by
    simpa [prefixWord, tailWord_5057904, baseEnd_5057904] using wordTrace_append hprefix tailTrace_5057904
  have hstable : (prefixWord ++ tailWord_5057904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057904).length < 2 ^ (prefixWord ++ tailWord_5057904).sum := by decide
  have hdescent : baseEnd_5057904 < baseStart_5057904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057938 : List Nat := [3, 2, 3, 3, 1, 1, 1, 2, 1, 4, 2]
def baseStart_5057938 : Nat := 118140960795 + 5057938 * 2 ^ 59
def prefixEnd_5057938 : Nat := 4983230072969 + 3 ^ 40 * 5057938 * 2
def baseEnd_5057938 : Nat := 2597153314640737028013973

theorem tailTrace_5057938 : CollatzResearch.WordTrace tailWord_5057938 prefixEnd_5057938 2597153314640737028013973 := by
  unfold tailWord_5057938
  simp only [CollatzResearch.WordTrace]
  refine ⟨46119538587490481970681617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122985436233307951921817645 46119538587490481970681617)
  ·
    refine ⟨34589653940617861478011213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46119538587490481970681617 34589653940617861478011213)
    ·
      refine ⟨12971120227731698054254205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34589653940617861478011213 12971120227731698054254205)
      ·
        refine ⟨4864170085399386770345327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12971120227731698054254205 4864170085399386770345327)
        ·
          refine ⟨7296255128099080155517991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4864170085399386770345327 7296255128099080155517991)
          ·
            refine ⟨10944382692148620233276987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7296255128099080155517991 10944382692148620233276987)
            ·
              refine ⟨16416574038222930349915481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10944382692148620233276987 16416574038222930349915481)
              ·
                refine ⟨12312430528667197762436611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16416574038222930349915481 12312430528667197762436611)
                ·
                  refine ⟨18468645793000796643654917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12312430528667197762436611 18468645793000796643654917)
                  ·
                    refine ⟨3462871086187649370685297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18468645793000796643654917 3462871086187649370685297)
                    ·
                      refine ⟨2597153314640737028013973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3462871086187649370685297 2597153314640737028013973)
                      ·
                        rfl

theorem cell23_5057938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_5057938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057938 prefixEnd_5057938 := by exact prefixLift 5057938
  have htrace : WordTrace (prefixWord ++ tailWord_5057938) baseStart_5057938 baseEnd_5057938 := by
    simpa [prefixWord, tailWord_5057938, baseEnd_5057938] using wordTrace_append hprefix tailTrace_5057938
  have hstable : (prefixWord ++ tailWord_5057938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057938).length < 2 ^ (prefixWord ++ tailWord_5057938).sum := by decide
  have hdescent : baseEnd_5057938 < baseStart_5057938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057987 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 5, 4]
def baseStart_5057987 : Nat := 118140960795 + 5057987 * 2 ^ 59
def prefixEnd_5057987 : Nat := 4983230072969 + 3 ^ 40 * 5057987 * 2
def baseEnd_5057987 : Nat := 865726158397602445433749

theorem tailTrace_5057987 : CollatzResearch.WordTrace tailWord_5057987 prefixEnd_5057987 865726158397602445433749 := by
  unfold tailWord_5057987
  simp only [CollatzResearch.WordTrace]
  refine ⟨184479941526784409251260215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122986627684522939500840143 184479941526784409251260215)
  ·
    refine ⟨276719912290176613876890323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184479941526784409251260215 276719912290176613876890323)
    ·
      refine ⟨415079868435264920815335485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276719912290176613876890323 415079868435264920815335485)
      ·
        refine ⟨155654950663224345305750807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 415079868435264920815335485 155654950663224345305750807)
        ·
          refine ⟨233482425994836517958626211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155654950663224345305750807 233482425994836517958626211)
          ·
            refine ⟨350223638992254776937939317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233482425994836517958626211 350223638992254776937939317)
            ·
              refine ⟨32833466155523885337931811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 350223638992254776937939317 32833466155523885337931811)
              ·
                refine ⟨49250199233285828006897717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32833466155523885337931811 49250199233285828006897717)
                ·
                  refine ⟨4617206178120546375646661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49250199233285828006897717 4617206178120546375646661)
                  ·
                    refine ⟨865726158397602445433749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4617206178120546375646661 865726158397602445433749)
                    ·
                      rfl

theorem cell23_5057987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 5, 4].length) (baseStart_5057987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057987 prefixEnd_5057987 := by exact prefixLift 5057987
  have htrace : WordTrace (prefixWord ++ tailWord_5057987) baseStart_5057987 baseEnd_5057987 := by
    simpa [prefixWord, tailWord_5057987, baseEnd_5057987] using wordTrace_append hprefix tailTrace_5057987
  have hstable : (prefixWord ++ tailWord_5057987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057987).length < 2 ^ (prefixWord ++ tailWord_5057987).sum := by decide
  have hdescent : baseEnd_5057987 < baseStart_5057987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5057994 : List Nat := [3, 1, 2, 1, 2, 3, 3, 1, 2, 1, 4]
def baseStart_5057994 : Nat := 118140960795 + 5057994 * 2 ^ 59
def prefixEnd_5057994 : Nat := 4983230072969 + 3 ^ 40 * 5057994 * 2
def baseEnd_5057994 : Nat := 2597182069557388808913715

theorem tailTrace_5057994 : CollatzResearch.WordTrace tailWord_5057994 prefixEnd_5057994 2597182069557388808913715 := by
  unfold tailWord_5057994
  simp only [CollatzResearch.WordTrace]
  refine ⟨46120049209439762361691259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122986797891839366297843357 46120049209439762361691259)
  ·
    refine ⟨69180073814159643542536889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46120049209439762361691259 69180073814159643542536889)
    ·
      refine ⟨51885055360619732656902667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69180073814159643542536889 51885055360619732656902667)
      ·
        refine ⟨77827583040929598985354001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51885055360619732656902667 77827583040929598985354001)
        ·
          refine ⟨58370687280697199239015501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77827583040929598985354001 58370687280697199239015501)
          ·
            refine ⟨21889007730261449714630813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58370687280697199239015501 21889007730261449714630813)
            ·
              refine ⟨8208377898848043642986555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21889007730261449714630813 8208377898848043642986555)
              ·
                refine ⟨12312566848272065464479833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8208377898848043642986555 12312566848272065464479833)
                ·
                  refine ⟨9234425136204049098359875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12312566848272065464479833 9234425136204049098359875)
                  ·
                    refine ⟨13851637704306073647539813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9234425136204049098359875 13851637704306073647539813)
                    ·
                      refine ⟨2597182069557388808913715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13851637704306073647539813 2597182069557388808913715)
                      ·
                        rfl

theorem cell23_5057994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_5057994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5057994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5057994 prefixEnd_5057994 := by exact prefixLift 5057994
  have htrace : WordTrace (prefixWord ++ tailWord_5057994) baseStart_5057994 baseEnd_5057994 := by
    simpa [prefixWord, tailWord_5057994, baseEnd_5057994] using wordTrace_append hprefix tailTrace_5057994
  have hstable : (prefixWord ++ tailWord_5057994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5057994).length < 2 ^ (prefixWord ++ tailWord_5057994).sum := by decide
  have hdescent : baseEnd_5057994 < baseStart_5057994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5057994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058000 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 10]
def baseStart_5058000 : Nat := 118140960795 + 5058000 * 2 ^ 59
def prefixEnd_5058000 : Nat := 4983230072969 + 3 ^ 40 * 5058000 * 2
def baseEnd_5058000 : Nat := 288576127826812865048743

theorem tailTrace_5058000 : CollatzResearch.WordTrace tailWord_5058000 prefixEnd_5058000 288576127826812865048743 := by
  unfold tailWord_5058000
  simp only [CollatzResearch.WordTrace]
  refine ⟨92240207837868656235741727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122986943783824874980988969 92240207837868656235741727)
  ·
    refine ⟨138360311756802984353612591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92240207837868656235741727 138360311756802984353612591)
    ·
      refine ⟨207540467635204476530418887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138360311756802984353612591 207540467635204476530418887)
      ·
        refine ⟨311310701452806714795628331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207540467635204476530418887 311310701452806714795628331)
        ·
          refine ⟨466966052179210072193442497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311310701452806714795628331 466966052179210072193442497)
          ·
            refine ⟨350224539134407554145081873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 466966052179210072193442497 350224539134407554145081873)
            ·
              refine ⟨262668404350805665608811405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 350224539134407554145081873 262668404350805665608811405)
              ·
                refine ⟨98500651631552124603304277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 262668404350805665608811405 98500651631552124603304277)
                ·
                  refine ⟨288576127826812865048743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 98500651631552124603304277 288576127826812865048743)
                  ·
                    rfl

theorem cell23_5058000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 10].length) (baseStart_5058000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058000 prefixEnd_5058000 := by exact prefixLift 5058000
  have htrace : WordTrace (prefixWord ++ tailWord_5058000) baseStart_5058000 baseEnd_5058000 := by
    simpa [prefixWord, tailWord_5058000, baseEnd_5058000] using wordTrace_append hprefix tailTrace_5058000
  have hstable : (prefixWord ++ tailWord_5058000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058000).length < 2 ^ (prefixWord ++ tailWord_5058000).sum := by decide
  have hdescent : baseEnd_5058000 < baseStart_5058000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058017 : List Nat := [1, 2, 3, 1, 2, 4, 1, 1, 8]
def baseStart_5058017 : Nat := 118140960795 + 5058017 * 2 ^ 59
def prefixEnd_5058017 : Nat := 4983230072969 + 3 ^ 40 * 5058017 * 2
def baseEnd_5058017 : Nat := 288577097734715802102901

theorem tailTrace_5058017 : CollatzResearch.WordTrace tailWord_5058017 prefixEnd_5058017 288577097734715802102901 := by
  unfold tailWord_5058017
  simp only [CollatzResearch.WordTrace]
  refine ⟨184481035716675724374852305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122987357144450482916568203 184481035716675724374852305)
  ·
    refine ⟨138360776787506793281139229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184481035716675724374852305 138360776787506793281139229)
    ·
      refine ⟨51885291295315047480427211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138360776787506793281139229 51885291295315047480427211)
      ·
        refine ⟨77827936942972571220640817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51885291295315047480427211 77827936942972571220640817)
        ·
          refine ⟨58370952707229428415480613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77827936942972571220640817 58370952707229428415480613)
          ·
            refine ⟨10944553632605517827902615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58370952707229428415480613 10944553632605517827902615)
            ·
              refine ⟨16416830448908276741853923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10944553632605517827902615 16416830448908276741853923)
              ·
                refine ⟨24625245673362415112780885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16416830448908276741853923 24625245673362415112780885)
                ·
                  refine ⟨288577097734715802102901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24625245673362415112780885 288577097734715802102901)
                  ·
                    rfl

theorem cell23_5058017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 8].length) (baseStart_5058017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058017 prefixEnd_5058017 := by exact prefixLift 5058017
  have htrace : WordTrace (prefixWord ++ tailWord_5058017) baseStart_5058017 baseEnd_5058017 := by
    simpa [prefixWord, tailWord_5058017, baseEnd_5058017] using wordTrace_append hprefix tailTrace_5058017
  have hstable : (prefixWord ++ tailWord_5058017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058017).length < 2 ^ (prefixWord ++ tailWord_5058017).sum := by decide
  have hdescent : baseEnd_5058017 < baseStart_5058017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058021 : List Nat := [1, 3, 1, 5, 1, 2, 2, 1, 3, 4]
def baseStart_5058021 : Nat := 118140960795 + 5058021 * 2 ^ 59
def prefixEnd_5058021 : Nat := 4983230072969 + 3 ^ 40 * 5058021 * 2
def baseEnd_5058021 : Nat := 865731977845020067758697

theorem tailTrace_5058021 : CollatzResearch.WordTrace tailWord_5058021 prefixEnd_5058021 865731977845020067758697 := by
  unfold tailWord_5058021
  simp only [CollatzResearch.WordTrace]
  refine ⟨184481181608661233057997917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122987454405774155371998611 184481181608661233057997917)
  ·
    refine ⟨69180443103247962396749219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184481181608661233057997917 69180443103247962396749219)
    ·
      refine ⟨103770664654871943595123829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69180443103247962396749219 103770664654871943595123829)
      ·
        refine ⟨9728499811394244712042859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103770664654871943595123829 9728499811394244712042859)
        ·
          refine ⟨14592749717091367068064289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9728499811394244712042859 14592749717091367068064289)
          ·
            refine ⟨10944562287818525301048217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14592749717091367068064289 10944562287818525301048217)
            ·
              refine ⟨8208421715863893975786163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10944562287818525301048217 8208421715863893975786163)
              ·
                refine ⟨12312632573795840963679245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8208421715863893975786163 12312632573795840963679245)
                ·
                  refine ⟨4617237215173440361379717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12312632573795840963679245 4617237215173440361379717)
                  ·
                    refine ⟨865731977845020067758697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4617237215173440361379717 865731977845020067758697)
                    ·
                      rfl

theorem cell23_5058021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 3, 4].length) (baseStart_5058021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058021 prefixEnd_5058021 := by exact prefixLift 5058021
  have htrace : WordTrace (prefixWord ++ tailWord_5058021) baseStart_5058021 baseEnd_5058021 := by
    simpa [prefixWord, tailWord_5058021, baseEnd_5058021] using wordTrace_append hprefix tailTrace_5058021
  have hstable : (prefixWord ++ tailWord_5058021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058021).length < 2 ^ (prefixWord ++ tailWord_5058021).sum := by decide
  have hdescent : baseEnd_5058021 < baseStart_5058021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058101 : List Nat := [1, 3, 3, 1, 1, 3, 3, 2, 1, 1, 4]
def baseStart_5058101 : Nat := 118140960795 + 5058101 * 2 ^ 59
def prefixEnd_5058101 : Nat := 4983230072969 + 3 ^ 40 * 5058101 * 2
def baseEnd_5058101 : Nat := 2597237011987419890275723

theorem tailTrace_5058101 : CollatzResearch.WordTrace tailWord_5058101 prefixEnd_5058101 2597237011987419890275723 := by
  unfold tailWord_5058101
  simp only [CollatzResearch.WordTrace]
  refine ⟨184484099448371406720910157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122989399632247604480606771 184484099448371406720910157)
  ·
    refine ⟨69181537293139277520341309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184484099448371406720910157 69181537293139277520341309)
    ·
      refine ⟨25943076484927229070127991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69181537293139277520341309 25943076484927229070127991)
      ·
        refine ⟨38914614727390843605191987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25943076484927229070127991 38914614727390843605191987)
        ·
          refine ⟨58371922091086265407787981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38914614727390843605191987 58371922091086265407787981)
          ·
            refine ⟨21889470784157349527920493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58371922091086265407787981 21889470784157349527920493)
            ·
              refine ⟨8208551544059006072970185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21889470784157349527920493 8208551544059006072970185)
              ·
                refine ⟨6156413658044254554727639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8208551544059006072970185 6156413658044254554727639)
                ·
                  refine ⟨9234620487066381832091459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6156413658044254554727639 9234620487066381832091459)
                  ·
                    refine ⟨13851930730599572748137189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9234620487066381832091459 13851930730599572748137189)
                    ·
                      refine ⟨2597237011987419890275723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13851930730599572748137189 2597237011987419890275723)
                      ·
                        rfl

theorem cell23_5058101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_5058101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058101 prefixEnd_5058101 := by exact prefixLift 5058101
  have htrace : WordTrace (prefixWord ++ tailWord_5058101) baseStart_5058101 baseEnd_5058101 := by
    simpa [prefixWord, tailWord_5058101, baseEnd_5058101] using wordTrace_append hprefix tailTrace_5058101
  have hstable : (prefixWord ++ tailWord_5058101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058101).length < 2 ^ (prefixWord ++ tailWord_5058101).sum := by decide
  have hdescent : baseEnd_5058101 < baseStart_5058101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058135 : List Nat := [1, 1, 3, 2, 2, 4, 1, 4, 1, 2, 2]
def baseStart_5058135 : Nat := 118140960795 + 5058135 * 2 ^ 59
def prefixEnd_5058135 : Nat := 4983230072969 + 3 ^ 40 * 5058135 * 2
def baseEnd_5058135 : Nat := 2597254470329672757250567

theorem tailTrace_5058135 : CollatzResearch.WordTrace tailWord_5058135 prefixEnd_5058135 2597254470329672757250567 := by
  unfold tailWord_5058135
  simp only [CollatzResearch.WordTrace]
  refine ⟨184485339530248230527647859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122990226353498820351765239 184485339530248230527647859)
  ·
    refine ⟨276728009295372345791471789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184485339530248230527647859 276728009295372345791471789)
    ·
      refine ⟨103773003485764629671801921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 276728009295372345791471789 103773003485764629671801921)
      ·
        refine ⟨77829752614323472253851441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103773003485764629671801921 77829752614323472253851441)
        ·
          refine ⟨58372314460742604190388581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77829752614323472253851441 58372314460742604190388581)
          ·
            refine ⟨10944808961389238285697859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58372314460742604190388581 10944808961389238285697859)
            ·
              refine ⟨16417213442083857428546789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10944808961389238285697859 16417213442083857428546789)
              ·
                refine ⟨3078227520390723267852523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16417213442083857428546789 3078227520390723267852523)
                ·
                  refine ⟨4617341280586084901778785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3078227520390723267852523 4617341280586084901778785)
                  ·
                    refine ⟨3463005960439563676334089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4617341280586084901778785 3463005960439563676334089)
                    ·
                      refine ⟨2597254470329672757250567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3463005960439563676334089 2597254470329672757250567)
                      ·
                        rfl

theorem cell23_5058135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 4, 1, 2, 2].length) (baseStart_5058135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058135 prefixEnd_5058135 := by exact prefixLift 5058135
  have htrace : WordTrace (prefixWord ++ tailWord_5058135) baseStart_5058135 baseEnd_5058135 := by
    simpa [prefixWord, tailWord_5058135, baseEnd_5058135] using wordTrace_append hprefix tailTrace_5058135
  have hstable : (prefixWord ++ tailWord_5058135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058135).length < 2 ^ (prefixWord ++ tailWord_5058135).sum := by decide
  have hdescent : baseEnd_5058135 < baseStart_5058135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058167 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 3, 8]
def baseStart_5058167 : Nat := 118140960795 + 5058167 * 2 ^ 59
def prefixEnd_5058167 : Nat := 4983230072969 + 3 ^ 40 * 5058167 * 2
def baseEnd_5058167 : Nat := 865756967236872210683473

theorem tailTrace_5058167 : CollatzResearch.WordTrace tailWord_5058167 prefixEnd_5058167 865756967236872210683473 := by
  unfold tailWord_5058167
  simp only [CollatzResearch.WordTrace]
  refine ⟨184486506666132299992812755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122991004444088199995208503 184486506666132299992812755)
  ·
    refine ⟨276729759999198449989219133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184486506666132299992812755 276729759999198449989219133)
    ·
      refine ⟨103773659999699418745957175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 276729759999198449989219133 103773659999699418745957175)
      ·
        refine ⟨155660489999549128118935763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103773659999699418745957175 155660489999549128118935763)
        ·
          refine ⟨233490734999323692178403645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155660489999549128118935763 233490734999323692178403645)
          ·
            refine ⟨87559025624746384566901367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 233490734999323692178403645 87559025624746384566901367)
            ·
              refine ⟨131338538437119576850352051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87559025624746384566901367 131338538437119576850352051)
              ·
                refine ⟨197007807655679365275528077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131338538437119576850352051 197007807655679365275528077)
                ·
                  refine ⟨73877927870879761978323029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 197007807655679365275528077 73877927870879761978323029)
                  ·
                    refine ⟨865756967236872210683473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73877927870879761978323029 865756967236872210683473)
                    ·
                      rfl

theorem cell23_5058167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 8].length) (baseStart_5058167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058167 prefixEnd_5058167 := by exact prefixLift 5058167
  have htrace : WordTrace (prefixWord ++ tailWord_5058167) baseStart_5058167 baseEnd_5058167 := by
    simpa [prefixWord, tailWord_5058167, baseEnd_5058167] using wordTrace_append hprefix tailTrace_5058167
  have hstable : (prefixWord ++ tailWord_5058167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058167).length < 2 ^ (prefixWord ++ tailWord_5058167).sum := by decide
  have hdescent : baseEnd_5058167 < baseStart_5058167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058208 : List Nat := [2, 1, 1, 4, 3, 1, 3, 1, 1, 4, 2]
def baseStart_5058208 : Nat := 118140960795 + 5058208 * 2 ^ 59
def prefixEnd_5058208 : Nat := 4983230072969 + 3 ^ 40 * 5058208 * 2
def baseEnd_5058208 : Nat := 2597291954417450971637731

theorem tailTrace_5058208 : CollatzResearch.WordTrace tailWord_5058208 prefixEnd_5058208 2597291954417450971637731 := by
  unfold tailWord_5058208
  simp only [CollatzResearch.WordTrace]
  refine ⟨92244001029491881997527639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122992001372655842663370185 92244001029491881997527639)
  ·
    refine ⟨138366001544237822996291459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92244001029491881997527639 138366001544237822996291459)
    ·
      refine ⟨207549002316356734494437189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138366001544237822996291459 207549002316356734494437189)
      ·
        refine ⟨38915437934316887717706973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207549002316356734494437189 38915437934316887717706973)
        ·
          refine ⟨14593289225368832894140115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38915437934316887717706973 14593289225368832894140115)
          ·
            refine ⟨21889933838053249341210173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14593289225368832894140115 21889933838053249341210173)
            ·
              refine ⟨8208725189269968502953815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21889933838053249341210173 8208725189269968502953815)
              ·
                refine ⟨12313087783904952754430723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8208725189269968502953815 12313087783904952754430723)
                ·
                  refine ⟨18469631675857429131646085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12313087783904952754430723 18469631675857429131646085)
                  ·
                    refine ⟨3463055939223267962183641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18469631675857429131646085 3463055939223267962183641)
                    ·
                      refine ⟨2597291954417450971637731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3463055939223267962183641 2597291954417450971637731)
                      ·
                        rfl

theorem cell23_5058208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_5058208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058208 prefixEnd_5058208 := by exact prefixLift 5058208
  have htrace : WordTrace (prefixWord ++ tailWord_5058208) baseStart_5058208 baseEnd_5058208 := by
    simpa [prefixWord, tailWord_5058208, baseEnd_5058208] using wordTrace_append hprefix tailTrace_5058208
  have hstable : (prefixWord ++ tailWord_5058208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058208).length < 2 ^ (prefixWord ++ tailWord_5058208).sum := by decide
  have hdescent : baseEnd_5058208 < baseStart_5058208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058224 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 3]
def baseStart_5058224 : Nat := 118140960795 + 5058224 * 2 ^ 59
def prefixEnd_5058224 : Nat := 4983230072969 + 3 ^ 40 * 5058224 * 2
def baseEnd_5058224 : Nat := 2597300170107922909037657

theorem tailTrace_5058224 : CollatzResearch.WordTrace tailWord_5058224 prefixEnd_5058224 2597300170107922909037657 := by
  unfold tailWord_5058224
  simp only [CollatzResearch.WordTrace]
  refine ⟨92244292813462899363818863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122992390417950532485091817 92244292813462899363818863)
  ·
    refine ⟨138366439220194349045728295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92244292813462899363818863 138366439220194349045728295)
    ·
      refine ⟨207549658830291523568592443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138366439220194349045728295 207549658830291523568592443)
      ·
        refine ⟨311324488245437285352888665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207549658830291523568592443 311324488245437285352888665)
        ·
          refine ⟨233493366184077964014666499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311324488245437285352888665 233493366184077964014666499)
          ·
            refine ⟨350240049276116946021999749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233493366184077964014666499 350240049276116946021999749)
            ·
              refine ⟨65670009239271927379124953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 350240049276116946021999749 65670009239271927379124953)
              ·
                refine ⟨49252506929453945534343715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65670009239271927379124953 49252506929453945534343715)
                ·
                  refine ⟨73878760394180918301515573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49252506929453945534343715 73878760394180918301515573)
                  ·
                    refine ⟨6926133786954461090767085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73878760394180918301515573 6926133786954461090767085)
                    ·
                      refine ⟨2597300170107922909037657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6926133786954461090767085 2597300170107922909037657)
                      ·
                        rfl

theorem cell23_5058224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 3].length) (baseStart_5058224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058224 prefixEnd_5058224 := by exact prefixLift 5058224
  have htrace : WordTrace (prefixWord ++ tailWord_5058224) baseStart_5058224 baseEnd_5058224 := by
    simpa [prefixWord, tailWord_5058224, baseEnd_5058224] using wordTrace_append hprefix tailTrace_5058224
  have hstable : (prefixWord ++ tailWord_5058224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058224).length < 2 ^ (prefixWord ++ tailWord_5058224).sum := by decide
  have hdescent : baseEnd_5058224 < baseStart_5058224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058248 : List Nat := [2, 1, 3, 1, 2, 2, 5, 2, 5]
def baseStart_5058248 : Nat := 118140960795 + 5058248 * 2 ^ 59
def prefixEnd_5058248 : Nat := 4983230072969 + 3 ^ 40 * 5058248 * 2
def baseEnd_5058248 : Nat := 288590277071514535015283

theorem tailTrace_5058248 : CollatzResearch.WordTrace tailWord_5058248 prefixEnd_5058248 288590277071514535015283 := by
  unfold tailWord_5058248
  simp only [CollatzResearch.WordTrace]
  refine ⟨92244730489419425413255699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122992973985892567217674265 92244730489419425413255699)
  ·
    refine ⟨138367095734129138119883549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92244730489419425413255699 138367095734129138119883549)
    ·
      refine ⟨51887660900298426794956331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138367095734129138119883549 51887660900298426794956331)
      ·
        refine ⟨77831491350447640192434497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51887660900298426794956331 77831491350447640192434497)
        ·
          refine ⟨58373618512835730144325873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77831491350447640192434497 58373618512835730144325873)
          ·
            refine ⟨43780213884626797608244405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58373618512835730144325873 43780213884626797608244405)
            ·
              refine ⟨4104395051683762275772913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43780213884626797608244405 4104395051683762275772913)
              ·
                refine ⟨3078296288762821706829685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4104395051683762275772913 3078296288762821706829685)
                ·
                  refine ⟨288590277071514535015283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3078296288762821706829685 288590277071514535015283)
                  ·
                    rfl

theorem cell23_5058248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 2, 5].length) (baseStart_5058248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058248 prefixEnd_5058248 := by exact prefixLift 5058248
  have htrace : WordTrace (prefixWord ++ tailWord_5058248) baseStart_5058248 baseEnd_5058248 := by
    simpa [prefixWord, tailWord_5058248, baseEnd_5058248] using wordTrace_append hprefix tailTrace_5058248
  have hstable : (prefixWord ++ tailWord_5058248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058248).length < 2 ^ (prefixWord ++ tailWord_5058248).sum := by decide
  have hdescent : baseEnd_5058248 < baseStart_5058248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058281 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 4, 4, 2]
def baseStart_5058281 : Nat := 118140960795 + 5058281 * 2 ^ 59
def prefixEnd_5058281 : Nat := 4983230072969 + 3 ^ 40 * 5058281 * 2
def baseEnd_5058281 : Nat := 2597329438505229186024895

theorem tailTrace_5058281 : CollatzResearch.WordTrace tailWord_5058281 prefixEnd_5058281 2597329438505229186024895 := by
  unfold tailWord_5058281
  simp only [CollatzResearch.WordTrace]
  refine ⟨184490664587719297462462697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122993776391812864974975131 184490664587719297462462697)
  ·
    refine ⟨138367998440789473096847023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184490664587719297462462697 138367998440789473096847023)
    ·
      refine ⟨207551997661184209645270535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138367998440789473096847023 207551997661184209645270535)
      ·
        refine ⟨311327996491776314467905803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207551997661184209645270535 311327996491776314467905803)
        ·
          refine ⟨466991994737664471701858705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311327996491776314467905803 466991994737664471701858705)
          ·
            refine ⟨350243996053248353776394029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 466991994737664471701858705 350243996053248353776394029)
            ·
              refine ⟨131341498519968132666147761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 350243996053248353776394029 131341498519968132666147761)
              ·
                refine ⟨98506123889976099499610821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131341498519968132666147761 98506123889976099499610821)
                ·
                  refine ⟨18469898229370518656177029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98506123889976099499610821 18469898229370518656177029)
                  ·
                    refine ⟨3463105918006972248033193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18469898229370518656177029 3463105918006972248033193)
                    ·
                      refine ⟨2597329438505229186024895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3463105918006972248033193 2597329438505229186024895)
                      ·
                        rfl

theorem cell23_5058281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 4, 2].length) (baseStart_5058281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058281 prefixEnd_5058281 := by exact prefixLift 5058281
  have htrace : WordTrace (prefixWord ++ tailWord_5058281) baseStart_5058281 baseEnd_5058281 := by
    simpa [prefixWord, tailWord_5058281, baseEnd_5058281] using wordTrace_append hprefix tailTrace_5058281
  have hstable : (prefixWord ++ tailWord_5058281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058281).length < 2 ^ (prefixWord ++ tailWord_5058281).sum := by decide
  have hdescent : baseEnd_5058281 < baseStart_5058281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058301 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 4, 2, 3]
def baseStart_5058301 : Nat := 118140960795 + 5058301 * 2 ^ 59
def prefixEnd_5058301 : Nat := 4983230072969 + 3 ^ 40 * 5058301 * 2
def baseEnd_5058301 : Nat := 2597339708118319107774803

theorem tailTrace_5058301 : CollatzResearch.WordTrace tailWord_5058301 prefixEnd_5058301 2597339708118319107774803 := by
  unfold tailWord_5058301
  simp only [CollatzResearch.WordTrace]
  refine ⟨184491394047646840878190757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122994262698431227252127171 184491394047646840878190757)
  ·
    refine ⟨34592136383933782664660767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184491394047646840878190757 34592136383933782664660767)
    ·
      refine ⟨51888204575900673996991151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34592136383933782664660767 51888204575900673996991151)
      ·
        refine ⟨77832306863851010995486727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51888204575900673996991151 77832306863851010995486727)
        ·
          refine ⟨116748460295776516493230091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77832306863851010995486727 116748460295776516493230091)
          ·
            refine ⟨175122690443664774739845137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116748460295776516493230091 175122690443664774739845137)
            ·
              refine ⟨131342017832748581054883853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175122690443664774739845137 131342017832748581054883853)
              ·
                refine ⟨49253256687280717895581445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131342017832748581054883853 49253256687280717895581445)
                ·
                  refine ⟨9234985628865134605421521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49253256687280717895581445 9234985628865134605421521)
                  ·
                    refine ⟨6926239221648850954066141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9234985628865134605421521 6926239221648850954066141)
                    ·
                      refine ⟨2597339708118319107774803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6926239221648850954066141 2597339708118319107774803)
                      ·
                        rfl

theorem cell23_5058301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_5058301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058301 prefixEnd_5058301 := by exact prefixLift 5058301
  have htrace : WordTrace (prefixWord ++ tailWord_5058301) baseStart_5058301 baseEnd_5058301 := by
    simpa [prefixWord, tailWord_5058301, baseEnd_5058301] using wordTrace_append hprefix tailTrace_5058301
  have hstable : (prefixWord ++ tailWord_5058301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058301).length < 2 ^ (prefixWord ++ tailWord_5058301).sum := by decide
  have hdescent : baseEnd_5058301 < baseStart_5058301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058351 : List Nat := [1, 1, 2, 1, 2, 1, 2, 7, 1, 5]
def baseStart_5058351 : Nat := 118140960795 + 5058351 * 2 ^ 59
def prefixEnd_5058351 : Nat := 4983230072969 + 3 ^ 40 * 5058351 * 2
def baseEnd_5058351 : Nat := 865788460717014637383191

theorem tailTrace_5058351 : CollatzResearch.WordTrace tailWord_5058351 prefixEnd_5058351 865788460717014637383191 := by
  unfold tailWord_5058351
  simp only [CollatzResearch.WordTrace]
  refine ⟨184493217697465699417510907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122995478464977132945007271 184493217697465699417510907)
  ·
    refine ⟨276739826546198549126266361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184493217697465699417510907 276739826546198549126266361)
    ·
      refine ⟨207554869909648911844699771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276739826546198549126266361 207554869909648911844699771)
      ·
        refine ⟨311332304864473367767049657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207554869909648911844699771 311332304864473367767049657)
        ·
          refine ⟨233499228648355025825287243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311332304864473367767049657 233499228648355025825287243)
          ·
            refine ⟨350248842972532538737930865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233499228648355025825287243 350248842972532538737930865)
            ·
              refine ⟨262686632229399404053448149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 350248842972532538737930865 262686632229399404053448149)
              ·
                refine ⟨6156717942876548532502691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 262686632229399404053448149 6156717942876548532502691)
                ·
                  refine ⟨9235076914314822798754037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6156717942876548532502691 9235076914314822798754037)
                  ·
                    refine ⟨865788460717014637383191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9235076914314822798754037 865788460717014637383191)
                    ·
                      rfl

theorem cell23_5058351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 5].length) (baseStart_5058351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058351 prefixEnd_5058351 := by exact prefixLift 5058351
  have htrace : WordTrace (prefixWord ++ tailWord_5058351) baseStart_5058351 baseEnd_5058351 := by
    simpa [prefixWord, tailWord_5058351, baseEnd_5058351] using wordTrace_append hprefix tailTrace_5058351
  have hstable : (prefixWord ++ tailWord_5058351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058351).length < 2 ^ (prefixWord ++ tailWord_5058351).sum := by decide
  have hdescent : baseEnd_5058351 < baseStart_5058351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058355 : List Nat := [1, 1, 1, 2, 8, 1, 1, 2, 6]
def baseStart_5058355 : Nat := 118140960795 + 5058355 * 2 ^ 59
def prefixEnd_5058355 : Nat := 4983230072969 + 3 ^ 40 * 5058355 * 2
def baseEnd_5058355 : Nat := 288596381785962432944395

theorem tailTrace_5058355 : CollatzResearch.WordTrace tailWord_5058355 prefixEnd_5058355 288596381785962432944395 := by
  unfold tailWord_5058355
  simp only [CollatzResearch.WordTrace]
  refine ⟨184493363589451208100656519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122995575726300805400437679 184493363589451208100656519)
  ·
    refine ⟨276740045384176812150984779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184493363589451208100656519 276740045384176812150984779)
    ·
      refine ⟨415110068076265218226477169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276740045384176812150984779 415110068076265218226477169)
      ·
        refine ⟨311332551057198913669857877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 415110068076265218226477169 311332551057198913669857877)
        ·
          refine ⟨3648428332701549769568647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 311332551057198913669857877 3648428332701549769568647)
          ·
            refine ⟨5472642499052324654352971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3648428332701549769568647 5472642499052324654352971)
            ·
              refine ⟨8208963748578486981529457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5472642499052324654352971 8208963748578486981529457)
              ·
                refine ⟨6156722811433865236147093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8208963748578486981529457 6156722811433865236147093)
                ·
                  refine ⟨288596381785962432944395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6156722811433865236147093 288596381785962432944395)
                  ·
                    rfl

theorem cell23_5058355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 6].length) (baseStart_5058355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058355 prefixEnd_5058355 := by exact prefixLift 5058355
  have htrace : WordTrace (prefixWord ++ tailWord_5058355) baseStart_5058355 baseEnd_5058355 := by
    simpa [prefixWord, tailWord_5058355, baseEnd_5058355] using wordTrace_append hprefix tailTrace_5058355
  have hstable : (prefixWord ++ tailWord_5058355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058355).length < 2 ^ (prefixWord ++ tailWord_5058355).sum := by decide
  have hdescent : baseEnd_5058355 < baseStart_5058355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058358 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_5058358 : Nat := 118140960795 + 5058358 * 2 ^ 59
def prefixEnd_5058358 : Nat := 4983230072969 + 3 ^ 40 * 5058358 * 2
def baseEnd_5058358 : Nat := 2597368976515625384762041

theorem tailTrace_5058358 : CollatzResearch.WordTrace tailWord_5058358 prefixEnd_5058358 2597368976515625384762041 := by
  unfold tailWord_5058358
  simp only [CollatzResearch.WordTrace]
  refine ⟨11530842063027521225813483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122995648672293559742010485 11530842063027521225813483)
  ·
    refine ⟨17296263094541281838720225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11530842063027521225813483 17296263094541281838720225)
    ·
      refine ⟨12972197320905961379040169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17296263094541281838720225 12972197320905961379040169)
      ·
        refine ⟨9729147990679471034280127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12972197320905961379040169 9729147990679471034280127)
        ·
          refine ⟨14593721986019206551420191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9729147990679471034280127 14593721986019206551420191)
          ·
            refine ⟨21890582979028809827130287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14593721986019206551420191 21890582979028809827130287)
            ·
              refine ⟨32835874468543214740695431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21890582979028809827130287 32835874468543214740695431)
              ·
                refine ⟨49253811702814822111043147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32835874468543214740695431 49253811702814822111043147)
                ·
                  refine ⟨73880717554222233166564721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49253811702814822111043147 73880717554222233166564721)
                  ·
                    refine ⟨55410538165666674874923541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73880717554222233166564721 55410538165666674874923541)
                    ·
                      refine ⟨2597368976515625384762041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55410538165666674874923541 2597368976515625384762041)
                      ·
                        rfl

theorem cell23_5058358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_5058358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058358 prefixEnd_5058358 := by exact prefixLift 5058358
  have htrace : WordTrace (prefixWord ++ tailWord_5058358) baseStart_5058358 baseEnd_5058358 := by
    simpa [prefixWord, tailWord_5058358, baseEnd_5058358] using wordTrace_append hprefix tailTrace_5058358
  have hstable : (prefixWord ++ tailWord_5058358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058358).length < 2 ^ (prefixWord ++ tailWord_5058358).sum := by decide
  have hdescent : baseEnd_5058358 < baseStart_5058358 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058365 : List Nat := [1, 4, 1, 4, 1, 1, 1, 3, 3, 1, 3]
def baseStart_5058365 : Nat := 118140960795 + 5058365 * 2 ^ 59
def prefixEnd_5058365 : Nat := 4983230072969 + 3 ^ 40 * 5058365 * 2
def baseEnd_5058365 : Nat := 2597372570880206857374509

theorem tailTrace_5058365 : CollatzResearch.WordTrace tailWord_5058365 prefixEnd_5058365 2597372570880206857374509 := by
  unfold tailWord_5058365
  simp only [CollatzResearch.WordTrace]
  refine ⟨184493728319414979808520549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122995818879609986539013699 184493728319414979808520549)
  ·
    refine ⟨34592574059890308714097603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184493728319414979808520549 34592574059890308714097603)
    ·
      refine ⟨51888861089835463071146405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34592574059890308714097603 51888861089835463071146405)
      ·
        refine ⟨9729161454344149325839951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51888861089835463071146405 9729161454344149325839951)
        ·
          refine ⟨14593742181516223988759927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9729161454344149325839951 14593742181516223988759927)
          ·
            refine ⟨21890613272274335983139891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14593742181516223988759927 21890613272274335983139891)
            ·
              refine ⟨32835919908411503974709837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21890613272274335983139891 32835919908411503974709837)
              ·
                refine ⟨12313469965654313990516189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32835919908411503974709837 12313469965654313990516189)
                ·
                  refine ⟨4617551237120367746443571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12313469965654313990516189 4617551237120367746443571)
                  ·
                    refine ⟨6926326855680551619665357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4617551237120367746443571 6926326855680551619665357)
                    ·
                      refine ⟨2597372570880206857374509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6926326855680551619665357 2597372570880206857374509)
                      ·
                        rfl

theorem cell23_5058365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_5058365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058365 prefixEnd_5058365 := by exact prefixLift 5058365
  have htrace : WordTrace (prefixWord ++ tailWord_5058365) baseStart_5058365 baseEnd_5058365 := by
    simpa [prefixWord, tailWord_5058365, baseEnd_5058365] using wordTrace_append hprefix tailTrace_5058365
  have hstable : (prefixWord ++ tailWord_5058365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058365).length < 2 ^ (prefixWord ++ tailWord_5058365).sum := by decide
  have hdescent : baseEnd_5058365 < baseStart_5058365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058401 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 3, 2, 4]
def baseStart_5058401 : Nat := 118140960795 + 5058401 * 2 ^ 59
def prefixEnd_5058401 : Nat := 4983230072969 + 3 ^ 40 * 5058401 * 2
def baseEnd_5058401 : Nat := 2597391056183768716524343

theorem tailTrace_5058401 : CollatzResearch.WordTrace tailWord_5058401 prefixEnd_5058401 2597391056183768716524343 := by
  unfold tailWord_5058401
  simp only [CollatzResearch.WordTrace]
  refine ⟨184495041347284557956831057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122996694231523038637887371 184495041347284557956831057)
  ·
    refine ⟨138371281010463418467623293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184495041347284557956831057 138371281010463418467623293)
    ·
      refine ⟨51889230378923781925358735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138371281010463418467623293 51889230378923781925358735)
      ·
        refine ⟨77833845568385672888038103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51889230378923781925358735 77833845568385672888038103)
        ·
          refine ⟨116750768352578509332057155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77833845568385672888038103 116750768352578509332057155)
          ·
            refine ⟨175126152528867763998085733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116750768352578509332057155 175126152528867763998085733)
            ·
              refine ⟨32836153599162705749641075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175126152528867763998085733 32836153599162705749641075)
              ·
                refine ⟨49254230398744058624461613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32836153599162705749641075 49254230398744058624461613)
                ·
                  refine ⟨18470336399529021984173105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49254230398744058624461613 18470336399529021984173105)
                  ·
                    refine ⟨13852752299646766488129829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18470336399529021984173105 13852752299646766488129829)
                    ·
                      refine ⟨2597391056183768716524343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13852752299646766488129829 2597391056183768716524343)
                      ·
                        rfl

theorem cell23_5058401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_5058401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058401 prefixEnd_5058401 := by exact prefixLift 5058401
  have htrace : WordTrace (prefixWord ++ tailWord_5058401) baseStart_5058401 baseEnd_5058401 := by
    simpa [prefixWord, tailWord_5058401, baseEnd_5058401] using wordTrace_append hprefix tailTrace_5058401
  have hstable : (prefixWord ++ tailWord_5058401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058401).length < 2 ^ (prefixWord ++ tailWord_5058401).sum := by decide
  have hdescent : baseEnd_5058401 < baseStart_5058401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058408 : List Nat := [2, 1, 4, 2, 1, 1, 4, 1, 1, 1, 5]
def baseStart_5058408 : Nat := 118140960795 + 5058408 * 2 ^ 59
def prefixEnd_5058408 : Nat := 4983230072969 + 3 ^ 40 * 5058408 * 2
def baseEnd_5058408 : Nat := 2597394650548350189136811

theorem tailTrace_5058408 : CollatzResearch.WordTrace tailWord_5058408 prefixEnd_5058408 2597394650548350189136811 := by
  unfold tailWord_5058408
  simp only [CollatzResearch.WordTrace]
  refine ⟨92247648329129599076167939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122996864438839465434890585 92247648329129599076167939)
  ·
    refine ⟨138371472493694398614251909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92247648329129599076167939 138371472493694398614251909)
    ·
      refine ⟨25944651092567699740172233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138371472493694398614251909 25944651092567699740172233)
      ·
        refine ⟨19458488319425774805129175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25944651092567699740172233 19458488319425774805129175)
        ·
          refine ⟨29187732479138662207693763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19458488319425774805129175 29187732479138662207693763)
          ·
            refine ⟨43781598718707993311540645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29187732479138662207693763 43781598718707993311540645)
            ·
              refine ⟨8209049759757748745913871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43781598718707993311540645 8209049759757748745913871)
              ·
                refine ⟨12313574639636623118870807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8209049759757748745913871 12313574639636623118870807)
                ·
                  refine ⟨18470361959454934678306211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12313574639636623118870807 18470361959454934678306211)
                  ·
                    refine ⟨27705542939182402017459317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18470361959454934678306211 27705542939182402017459317)
                    ·
                      refine ⟨2597394650548350189136811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27705542939182402017459317 2597394650548350189136811)
                      ·
                        rfl

theorem cell23_5058408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_5058408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058408 prefixEnd_5058408 := by exact prefixLift 5058408
  have htrace : WordTrace (prefixWord ++ tailWord_5058408) baseStart_5058408 baseEnd_5058408 := by
    simpa [prefixWord, tailWord_5058408, baseEnd_5058408] using wordTrace_append hprefix tailTrace_5058408
  have hstable : (prefixWord ++ tailWord_5058408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058408).length < 2 ^ (prefixWord ++ tailWord_5058408).sum := by decide
  have hdescent : baseEnd_5058408 < baseStart_5058408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058491 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 4]
def baseStart_5058491 : Nat := 118140960795 + 5058491 * 2 ^ 59
def prefixEnd_5058491 : Nat := 4983230072969 + 3 ^ 40 * 5058491 * 2
def baseEnd_5058491 : Nat := 2597437269442673364398929

theorem tailTrace_5058491 : CollatzResearch.WordTrace tailWord_5058491 prefixEnd_5058491 2597437269442673364398929 := by
  unfold tailWord_5058491
  simp only [CollatzResearch.WordTrace]
  refine ⟨184498323916958503327607327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122998882611305668885071551 184498323916958503327607327)
  ·
    refine ⟨276747485875437754991410991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184498323916958503327607327 276747485875437754991410991)
    ·
      refine ⟨415121228813156632487116487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276747485875437754991410991 415121228813156632487116487)
      ·
        refine ⟨622681843219734948730674731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415121228813156632487116487 622681843219734948730674731)
        ·
          refine ⟨934022764829602423096012097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 622681843219734948730674731 934022764829602423096012097)
          ·
            refine ⟨700517073622201817322009073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 934022764829602423096012097 700517073622201817322009073)
            ·
              refine ⟨525387805216651362991506805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 700517073622201817322009073 525387805216651362991506805)
              ·
                refine ⟨49255106739061065280453763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 525387805216651362991506805 49255106739061065280453763)
                ·
                  refine ⟨73882660108591597920680645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49255106739061065280453763 73882660108591597920680645)
                  ·
                    refine ⟨13852998770360924610127621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73882660108591597920680645 13852998770360924610127621)
                    ·
                      refine ⟨2597437269442673364398929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13852998770360924610127621 2597437269442673364398929)
                      ·
                        rfl

theorem cell23_5058491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 4].length) (baseStart_5058491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058491 prefixEnd_5058491 := by exact prefixLift 5058491
  have htrace : WordTrace (prefixWord ++ tailWord_5058491) baseStart_5058491 baseEnd_5058491 := by
    simpa [prefixWord, tailWord_5058491, baseEnd_5058491] using wordTrace_append hprefix tailTrace_5058491
  have hstable : (prefixWord ++ tailWord_5058491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058491).length < 2 ^ (prefixWord ++ tailWord_5058491).sum := by decide
  have hdescent : baseEnd_5058491 < baseStart_5058491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058495 : List Nat := [1, 1, 2, 2, 2, 1, 6, 1, 1, 4, 2]
def baseStart_5058495 : Nat := 118140960795 + 5058495 * 2 ^ 59
def prefixEnd_5058495 : Nat := 4983230072969 + 3 ^ 40 * 5058495 * 2
def baseEnd_5058495 : Nat := 2597439323365291348748911

theorem tailTrace_5058495 : CollatzResearch.WordTrace tailWord_5058495 prefixEnd_5058495 2597439323365291348748911 := by
  unfold tailWord_5058495
  simp only [CollatzResearch.WordTrace]
  refine ⟨184498469808944012010752939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122998979872629341340501959 184498469808944012010752939)
  ·
    refine ⟨276747704713416018016129409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184498469808944012010752939 276747704713416018016129409)
    ·
      refine ⟨207560778535062013512097057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276747704713416018016129409 207560778535062013512097057)
      ·
        refine ⟨155670583901296510134072793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207560778535062013512097057 155670583901296510134072793)
        ·
          refine ⟨116752937925972382600554595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155670583901296510134072793 116752937925972382600554595)
          ·
            refine ⟨175129406888958573900831893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116752937925972382600554595 175129406888958573900831893)
            ·
              refine ⟨8209190947919933151601495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 175129406888958573900831893 8209190947919933151601495)
              ·
                refine ⟨12313786421879899727402243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8209190947919933151601495 12313786421879899727402243)
                ·
                  refine ⟨18470679632819849591103365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12313786421879899727402243 18470679632819849591103365)
                  ·
                    refine ⟨3463252431153721798331881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18470679632819849591103365 3463252431153721798331881)
                    ·
                      refine ⟨2597439323365291348748911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3463252431153721798331881 2597439323365291348748911)
                      ·
                        rfl

theorem cell23_5058495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 4, 2].length) (baseStart_5058495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058495 prefixEnd_5058495 := by exact prefixLift 5058495
  have htrace : WordTrace (prefixWord ++ tailWord_5058495) baseStart_5058495 baseEnd_5058495 := by
    simpa [prefixWord, tailWord_5058495, baseEnd_5058495] using wordTrace_append hprefix tailTrace_5058495
  have hstable : (prefixWord ++ tailWord_5058495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058495).length < 2 ^ (prefixWord ++ tailWord_5058495).sum := by decide
  have hdescent : baseEnd_5058495 < baseStart_5058495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058535 : List Nat := [1, 1, 5, 2, 3, 1, 2, 1, 7]
def baseStart_5058535 : Nat := 118140960795 + 5058535 * 2 ^ 59
def prefixEnd_5058535 : Nat := 4983230072969 + 3 ^ 40 * 5058535 * 2
def baseEnd_5058535 : Nat := 288606651399052354694303

theorem tailTrace_5058535 : CollatzResearch.WordTrace tailWord_5058535 prefixEnd_5058535 288606651399052354694303 := by
  unfold tailWord_5058535
  simp only [CollatzResearch.WordTrace]
  refine ⟨184499928728799098842209059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122999952485866065894806039 184499928728799098842209059)
  ·
    refine ⟨276749893093198648263313589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184499928728799098842209059 276749893093198648263313589)
    ·
      refine ⟨25945302477487373274685649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 276749893093198648263313589 25945302477487373274685649)
      ·
        refine ⟨19458976858115529956014237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25945302477487373274685649 19458976858115529956014237)
        ·
          refine ⟨7297116321793323733505339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19458976858115529956014237 7297116321793323733505339)
          ·
            refine ⟨10945674482689985600258009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7297116321793323733505339 10945674482689985600258009)
            ·
              refine ⟨8209255862017489200193507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10945674482689985600258009 8209255862017489200193507)
              ·
                refine ⟨12313883793026233800290261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8209255862017489200193507 12313883793026233800290261)
                ·
                  refine ⟨288606651399052354694303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12313883793026233800290261 288606651399052354694303)
                  ·
                    rfl

theorem cell23_5058535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 7].length) (baseStart_5058535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058535 prefixEnd_5058535 := by exact prefixLift 5058535
  have htrace : WordTrace (prefixWord ++ tailWord_5058535) baseStart_5058535 baseEnd_5058535 := by
    simpa [prefixWord, tailWord_5058535, baseEnd_5058535] using wordTrace_append hprefix tailTrace_5058535
  have hstable : (prefixWord ++ tailWord_5058535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058535).length < 2 ^ (prefixWord ++ tailWord_5058535).sum := by decide
  have hdescent : baseEnd_5058535 < baseStart_5058535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058566 : List Nat := [6, 2, 1, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_5058566 : Nat := 118140960795 + 5058566 * 2 ^ 59
def prefixEnd_5058566 : Nat := 4983230072969 + 3 ^ 40 * 5058566 * 2
def baseEnd_5058566 : Nat := 2597475780491760570961085

theorem tailTrace_5058566 : CollatzResearch.WordTrace tailWord_5058566 prefixEnd_5058566 2597475780491760570961085 := by
  unfold tailWord_5058566
  simp only [CollatzResearch.WordTrace]
  refine ⟨5765658105990212223018361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 123000706261124527424391701 5765658105990212223018361)
  ·
    refine ⟨4324243579492659167263771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5765658105990212223018361 4324243579492659167263771)
    ·
      refine ⟨6486365369238988750895657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4324243579492659167263771 6486365369238988750895657)
      ·
        refine ⟨4864774026929241563171743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6486365369238988750895657 4864774026929241563171743)
        ·
          refine ⟨7297161040393862344757615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4864774026929241563171743 7297161040393862344757615)
          ·
            refine ⟨10945741560590793517136423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7297161040393862344757615 10945741560590793517136423)
            ·
              refine ⟨16418612340886190275704635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10945741560590793517136423 16418612340886190275704635)
              ·
                refine ⟨24627918511329285413556953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16418612340886190275704635 24627918511329285413556953)
                ·
                  refine ⟨18470938883496964060167715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24627918511329285413556953 18470938883496964060167715)
                  ·
                    refine ⟨27706408325245446090251573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18470938883496964060167715 27706408325245446090251573)
                    ·
                      refine ⟨2597475780491760570961085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27706408325245446090251573 2597475780491760570961085)
                      ·
                        rfl

theorem cell23_5058566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_5058566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058566 prefixEnd_5058566 := by exact prefixLift 5058566
  have htrace : WordTrace (prefixWord ++ tailWord_5058566) baseStart_5058566 baseEnd_5058566 := by
    simpa [prefixWord, tailWord_5058566, baseEnd_5058566] using wordTrace_append hprefix tailTrace_5058566
  have hstable : (prefixWord ++ tailWord_5058566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058566).length < 2 ^ (prefixWord ++ tailWord_5058566).sum := by decide
  have hdescent : baseEnd_5058566 < baseStart_5058566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058568 : List Nat := [2, 1, 3, 2, 1, 2, 1, 3, 1, 3, 4]
def baseStart_5058568 : Nat := 118140960795 + 5058568 * 2 ^ 59
def prefixEnd_5058568 : Nat := 4983230072969 + 3 ^ 40 * 5058568 * 2
def baseEnd_5058568 : Nat := 2597476807453069563136075

theorem tailTrace_5058568 : CollatzResearch.WordTrace tailWord_5058568 prefixEnd_5058568 2597476807453069563136075 := by
  unfold tailWord_5058568
  simp only [CollatzResearch.WordTrace]
  refine ⟨92250566168839772739080179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123000754891786363652106905 92250566168839772739080179)
  ·
    refine ⟨138375849253259659108620269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92250566168839772739080179 138375849253259659108620269)
    ·
      refine ⟨51890943469972372165732601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138375849253259659108620269 51890943469972372165732601)
      ·
        refine ⟨38918207602479279124299451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51890943469972372165732601 38918207602479279124299451)
        ·
          refine ⟨58377311403718918686449177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38918207602479279124299451 58377311403718918686449177)
          ·
            refine ⟨43782983552789189014836883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58377311403718918686449177 43782983552789189014836883)
            ·
              refine ⟨65674475329183783522255325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43782983552789189014836883 65674475329183783522255325)
              ·
                refine ⟨24627928248443918820845747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65674475329183783522255325 24627928248443918820845747)
                ·
                  refine ⟨36941892372665878231268621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24627928248443918820845747 36941892372665878231268621)
                  ·
                    refine ⟨13853209639749704336725733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36941892372665878231268621 13853209639749704336725733)
                    ·
                      refine ⟨2597476807453069563136075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13853209639749704336725733 2597476807453069563136075)
                      ·
                        rfl

theorem cell23_5058568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_5058568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058568 prefixEnd_5058568 := by exact prefixLift 5058568
  have htrace : WordTrace (prefixWord ++ tailWord_5058568) baseStart_5058568 baseEnd_5058568 := by
    simpa [prefixWord, tailWord_5058568, baseEnd_5058568] using wordTrace_append hprefix tailTrace_5058568
  have hstable : (prefixWord ++ tailWord_5058568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058568).length < 2 ^ (prefixWord ++ tailWord_5058568).sum := by decide
  have hdescent : baseEnd_5058568 < baseStart_5058568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058635 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 5, 1, 3]
def baseStart_5058635 : Nat := 118140960795 + 5058635 * 2 ^ 59
def prefixEnd_5058635 : Nat := 4983230072969 + 3 ^ 40 * 5058635 * 2
def baseEnd_5058635 : Nat := 2597511210656920800998267

theorem tailTrace_5058635 : CollatzResearch.WordTrace tailWord_5058635 prefixEnd_5058635 2597511210656920800998267 := by
  unfold tailWord_5058635
  simp only [CollatzResearch.WordTrace]
  refine ⟨184503576028436815920849359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123002384018957877280566239 184503576028436815920849359)
  ·
    refine ⟨276755364042655223881274039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184503576028436815920849359 276755364042655223881274039)
    ·
      refine ⟨415133046063982835821911059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276755364042655223881274039 415133046063982835821911059)
      ·
        refine ⟨622699569095974253732866589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415133046063982835821911059 622699569095974253732866589)
        ·
          refine ⟨233512338410990345149824971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 622699569095974253732866589 233512338410990345149824971)
          ·
            refine ⟨350268507616485517724737457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233512338410990345149824971 350268507616485517724737457)
            ·
              refine ⟨262701380712364138293553093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 350268507616485517724737457 262701380712364138293553093)
              ·
                refine ⟨49256508883568275930041205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 262701380712364138293553093 49256508883568275930041205)
                ·
                  refine ⟨4617797707834525868441363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49256508883568275930041205 4617797707834525868441363)
                  ·
                    refine ⟨6926696561751788802662045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4617797707834525868441363 6926696561751788802662045)
                    ·
                      refine ⟨2597511210656920800998267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6926696561751788802662045 2597511210656920800998267)
                      ·
                        rfl

theorem cell23_5058635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 5, 1, 3].length) (baseStart_5058635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058635 prefixEnd_5058635 := by exact prefixLift 5058635
  have htrace : WordTrace (prefixWord ++ tailWord_5058635) baseStart_5058635 baseEnd_5058635 := by
    simpa [prefixWord, tailWord_5058635, baseEnd_5058635] using wordTrace_append hprefix tailTrace_5058635
  have hstable : (prefixWord ++ tailWord_5058635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058635).length < 2 ^ (prefixWord ++ tailWord_5058635).sum := by decide
  have hdescent : baseEnd_5058635 < baseStart_5058635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058642 : List Nat := [3, 2, 2, 1, 4, 1, 2, 2, 6]
def baseStart_5058642 : Nat := 118140960795 + 5058642 * 2 ^ 59
def prefixEnd_5058642 : Nat := 4983230072969 + 3 ^ 40 * 5058642 * 2
def baseEnd_5058642 : Nat := 288612756113500252623415

theorem tailTrace_5058642 : CollatzResearch.WordTrace tailWord_5058642 prefixEnd_5058642 288612756113500252623415 := by
  unfold tailWord_5058642
  simp only [CollatzResearch.WordTrace]
  refine ⟨46125957834852864029088545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123002554226274304077569453 46125957834852864029088545)
  ·
    refine ⟨34594468376139648021816409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46125957834852864029088545 34594468376139648021816409)
    ·
      refine ⟨25945851282104736016362307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34594468376139648021816409 25945851282104736016362307)
      ·
        refine ⟨38918776923157104024543461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25945851282104736016362307 38918776923157104024543461)
        ·
          refine ⟨7297270673091957004601899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38918776923157104024543461 7297270673091957004601899)
          ·
            refine ⟨10945906009637935506902849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7297270673091957004601899 10945906009637935506902849)
            ·
              refine ⟨8209429507228451630177137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10945906009637935506902849 8209429507228451630177137)
              ·
                refine ⟨6157072130421338722632853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8209429507228451630177137 6157072130421338722632853)
                ·
                  refine ⟨288612756113500252623415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6157072130421338722632853 288612756113500252623415)
                  ·
                    rfl

theorem cell23_5058642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 6].length) (baseStart_5058642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058642 prefixEnd_5058642 := by exact prefixLift 5058642
  have htrace : WordTrace (prefixWord ++ tailWord_5058642) baseStart_5058642 baseEnd_5058642 := by
    simpa [prefixWord, tailWord_5058642, baseEnd_5058642] using wordTrace_append hprefix tailTrace_5058642
  have hstable : (prefixWord ++ tailWord_5058642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058642).length < 2 ^ (prefixWord ++ tailWord_5058642).sum := by decide
  have hdescent : baseEnd_5058642 < baseStart_5058642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058679 : List Nat := [1, 1, 3, 1, 1, 7, 1, 1, 2, 3, 2]
def baseStart_5058679 : Nat := 118140960795 + 5058679 * 2 ^ 59
def prefixEnd_5058679 : Nat := 4983230072969 + 3 ^ 40 * 5058679 * 2
def baseEnd_5058679 : Nat := 2597533803805718628848065

theorem tailTrace_5058679 : CollatzResearch.WordTrace tailWord_5058679 prefixEnd_5058679 2597533803805718628848065 := by
  unfold tailWord_5058679
  simp only [CollatzResearch.WordTrace]
  refine ⟨184505180840277411435451091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123003453893518274290300727 184505180840277411435451091)
  ·
    refine ⟨276757771260416117153176637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184505180840277411435451091 276757771260416117153176637)
    ·
      refine ⟨103784164222656043932441239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 276757771260416117153176637 103784164222656043932441239)
      ·
        refine ⟨155676246333984065898661859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103784164222656043932441239 155676246333984065898661859)
        ·
          refine ⟨233514369500976098847992789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155676246333984065898661859 233514369500976098847992789)
          ·
            refine ⟨5472993035179127316749831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 233514369500976098847992789 5472993035179127316749831)
            ·
              refine ⟨8209489552768690975124747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5472993035179127316749831 8209489552768690975124747)
              ·
                refine ⟨12314234329153036462687121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8209489552768690975124747 12314234329153036462687121)
                ·
                  refine ⟨9235675746864777347015341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12314234329153036462687121 9235675746864777347015341)
                  ·
                    refine ⟨3463378405074291505130753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9235675746864777347015341 3463378405074291505130753)
                    ·
                      refine ⟨2597533803805718628848065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3463378405074291505130753 2597533803805718628848065)
                      ·
                        rfl

theorem cell23_5058679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 3, 2].length) (baseStart_5058679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058679 prefixEnd_5058679 := by exact prefixLift 5058679
  have htrace : WordTrace (prefixWord ++ tailWord_5058679) baseStart_5058679 baseEnd_5058679 := by
    simpa [prefixWord, tailWord_5058679, baseEnd_5058679] using wordTrace_append hprefix tailTrace_5058679
  have hstable : (prefixWord ++ tailWord_5058679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058679).length < 2 ^ (prefixWord ++ tailWord_5058679).sum := by decide
  have hdescent : baseEnd_5058679 < baseStart_5058679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058685 : List Nat := [1, 4, 1, 1, 3, 2, 2, 2, 1, 6]
def baseStart_5058685 : Nat := 118140960795 + 5058685 * 2 ^ 59
def prefixEnd_5058685 : Nat := 4983230072969 + 3 ^ 40 * 5058685 * 2
def baseEnd_5058685 : Nat := 865845628229881868457679

theorem tailTrace_5058685 : CollatzResearch.WordTrace tailWord_5058685 prefixEnd_5058685 865845628229881868457679 := by
  unfold tailWord_5058685
  simp only [CollatzResearch.WordTrace]
  refine ⟨184505399678255674460169509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123003599785503782973446339 184505399678255674460169509)
  ·
    refine ⟨34594762439672938961281783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184505399678255674460169509 34594762439672938961281783)
    ·
      refine ⟨51892143659509408441922675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34594762439672938961281783 51892143659509408441922675)
      ·
        refine ⟨77838215489264112662884013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51892143659509408441922675 77838215489264112662884013)
        ·
          refine ⟨29189330808474042248581505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77838215489264112662884013 29189330808474042248581505)
          ·
            refine ⟨21891998106355531686436129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29189330808474042248581505 21891998106355531686436129)
            ·
              refine ⟨16418998579766648764827097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21891998106355531686436129 16418998579766648764827097)
              ·
                refine ⟨12314248934824986573620323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16418998579766648764827097 12314248934824986573620323)
                ·
                  refine ⟨18471373402237479860430485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12314248934824986573620323 18471373402237479860430485)
                  ·
                    refine ⟨865845628229881868457679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18471373402237479860430485 865845628229881868457679)
                    ·
                      rfl

theorem cell23_5058685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_5058685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058685 prefixEnd_5058685 := by exact prefixLift 5058685
  have htrace : WordTrace (prefixWord ++ tailWord_5058685) baseStart_5058685 baseEnd_5058685 := by
    simpa [prefixWord, tailWord_5058685, baseEnd_5058685] using wordTrace_append hprefix tailTrace_5058685
  have hstable : (prefixWord ++ tailWord_5058685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058685).length < 2 ^ (prefixWord ++ tailWord_5058685).sum := by decide
  have hdescent : baseEnd_5058685 < baseStart_5058685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058688 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 6]
def baseStart_5058688 : Nat := 118140960795 + 5058688 * 2 ^ 59
def prefixEnd_5058688 : Nat := 4983230072969 + 3 ^ 40 * 5058688 * 2
def baseEnd_5058688 : Nat := 2597538425131609093635523

theorem tailTrace_5058688 : CollatzResearch.WordTrace tailWord_5058688 prefixEnd_5058688 2597538425131609093635523 := by
  unfold tailWord_5058688
  simp only [CollatzResearch.WordTrace]
  refine ⟨92252754548622402986264359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123003672731496537315019145 92252754548622402986264359)
  ·
    refine ⟨138379131822933604479396539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92252754548622402986264359 138379131822933604479396539)
    ·
      refine ⟨207568697734400406719094809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138379131822933604479396539 207568697734400406719094809)
      ·
        refine ⟨155676523300800305039321107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207568697734400406719094809 155676523300800305039321107)
        ·
          refine ⟨233514784951200457558981661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155676523300800305039321107 233514784951200457558981661)
          ·
            refine ⟨87568044356700171584618123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 233514784951200457558981661 87568044356700171584618123)
            ·
              refine ⟨131352066535050257376927185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87568044356700171584618123 131352066535050257376927185)
              ·
                refine ⟨98514049901287693032695389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131352066535050257376927185 98514049901287693032695389)
                ·
                  refine ⟨36942768712982884887260771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98514049901287693032695389 36942768712982884887260771)
                  ·
                    refine ⟨55414153069474327330891157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36942768712982884887260771 55414153069474327330891157)
                    ·
                      refine ⟨2597538425131609093635523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55414153069474327330891157 2597538425131609093635523)
                      ·
                        rfl

theorem cell23_5058688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_5058688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058688 prefixEnd_5058688 := by exact prefixLift 5058688
  have htrace : WordTrace (prefixWord ++ tailWord_5058688) baseStart_5058688 baseEnd_5058688 := by
    simpa [prefixWord, tailWord_5058688, baseEnd_5058688] using wordTrace_append hprefix tailTrace_5058688
  have hstable : (prefixWord ++ tailWord_5058688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058688).length < 2 ^ (prefixWord ++ tailWord_5058688).sum := by decide
  have hdescent : baseEnd_5058688 < baseStart_5058688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058692 : List Nat := [2, 3, 2, 1, 2, 1, 3, 3, 1, 1, 4]
def baseStart_5058692 : Nat := 118140960795 + 5058692 * 2 ^ 59
def prefixEnd_5058692 : Nat := 4983230072969 + 3 ^ 40 * 5058692 * 2
def baseEnd_5058692 : Nat := 2597540479054227077985505

theorem tailTrace_5058692 : CollatzResearch.WordTrace tailWord_5058692 prefixEnd_5058692 2597540479054227077985505 := by
  unfold tailWord_5058692
  simp only [CollatzResearch.WordTrace]
  refine ⟨92252827494615157327837165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123003769992820209770449553 92252827494615157327837165)
  ·
    refine ⟨34594810310480683997938937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92252827494615157327837165 34594810310480683997938937)
    ·
      refine ⟨25946107732860512998454203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34594810310480683997938937 25946107732860512998454203)
      ·
        refine ⟨38919161599290769497681305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25946107732860512998454203 38919161599290769497681305)
        ·
          refine ⟨29189371199468077123260979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38919161599290769497681305 29189371199468077123260979)
          ·
            refine ⟨43784056799202115684891469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29189371199468077123260979 43784056799202115684891469)
            ·
              refine ⟨16419021299700793381834301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43784056799202115684891469 16419021299700793381834301)
              ·
                refine ⟨6157132987387797518187863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16419021299700793381834301 6157132987387797518187863)
                ·
                  refine ⟨9235699481081696277281795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6157132987387797518187863 9235699481081696277281795)
                  ·
                    refine ⟨13853549221622544415922693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9235699481081696277281795 13853549221622544415922693)
                    ·
                      refine ⟨2597540479054227077985505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13853549221622544415922693 2597540479054227077985505)
                      ·
                        rfl

theorem cell23_5058692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_5058692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058692 prefixEnd_5058692 := by exact prefixLift 5058692
  have htrace : WordTrace (prefixWord ++ tailWord_5058692) baseStart_5058692 baseEnd_5058692 := by
    simpa [prefixWord, tailWord_5058692, baseEnd_5058692] using wordTrace_append hprefix tailTrace_5058692
  have hstable : (prefixWord ++ tailWord_5058692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058692).length < 2 ^ (prefixWord ++ tailWord_5058692).sum := by decide
  have hdescent : baseEnd_5058692 < baseStart_5058692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058709 : List Nat := [1, 3, 2, 1, 1, 1, 6, 1, 3, 2, 2]
def baseStart_5058709 : Nat := 118140960795 + 5058709 * 2 ^ 59
def prefixEnd_5058709 : Nat := 4983230072969 + 3 ^ 40 * 5058709 * 2
def baseEnd_5058709 : Nat := 2597549208225353511472927

theorem tailTrace_5058709 : CollatzResearch.WordTrace tailWord_5058709 prefixEnd_5058709 2597549208225353511472927 := by
  unfold tailWord_5058709
  simp only [CollatzResearch.WordTrace]
  refine ⟨184506275030168726559043181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123004183353445817706028787 184506275030168726559043181)
  ·
    refine ⟨69189853136313272459641193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184506275030168726559043181 69189853136313272459641193)
    ·
      refine ⟨51892389852234954344730895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69189853136313272459641193 51892389852234954344730895)
      ·
        refine ⟨77838584778352431517096343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51892389852234954344730895 77838584778352431517096343)
        ·
          refine ⟨116757877167528647275644515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77838584778352431517096343 116757877167528647275644515)
          ·
            refine ⟨175136815751292970913466773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116757877167528647275644515 175136815751292970913466773)
            ·
              refine ⟨8209538238341858011568755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 175136815751292970913466773 8209538238341858011568755)
              ·
                refine ⟨12314307357512787017353133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8209538238341858011568755 12314307357512787017353133)
                ·
                  refine ⟨4617865259067295131507425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12314307357512787017353133 4617865259067295131507425)
                  ·
                    refine ⟨3463398944300471348630569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4617865259067295131507425 3463398944300471348630569)
                    ·
                      refine ⟨2597549208225353511472927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3463398944300471348630569 2597549208225353511472927)
                      ·
                        rfl

theorem cell23_5058709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 3, 2, 2].length) (baseStart_5058709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058709 prefixEnd_5058709 := by exact prefixLift 5058709
  have htrace : WordTrace (prefixWord ++ tailWord_5058709) baseStart_5058709 baseEnd_5058709 := by
    simpa [prefixWord, tailWord_5058709, baseEnd_5058709] using wordTrace_append hprefix tailTrace_5058709
  have hstable : (prefixWord ++ tailWord_5058709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058709).length < 2 ^ (prefixWord ++ tailWord_5058709).sum := by decide
  have hdescent : baseEnd_5058709 < baseStart_5058709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058710 : List Nat := [5, 3, 2, 1, 1, 1, 3, 1, 6]
def baseStart_5058710 : Nat := 118140960795 + 5058710 * 2 ^ 59
def prefixEnd_5058710 : Nat := 4983230072969 + 3 ^ 40 * 5058710 * 2
def baseEnd_5058710 : Nat := 288616635745112000840047

theorem tailTrace_5058710 : CollatzResearch.WordTrace tailWord_5058710 prefixEnd_5058710 288616635745112000840047 := by
  unfold tailWord_5058710
  simp only [CollatzResearch.WordTrace]
  refine ⟨11531644468947818983114349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123004207668776735819886389 11531644468947818983114349)
  ·
    refine ⟨4324366675855432118667881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11531644468947818983114349 4324366675855432118667881)
    ·
      refine ⟨3243275006891574089000911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4324366675855432118667881 3243275006891574089000911)
      ·
        refine ⟨4864912510337361133501367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3243275006891574089000911 4864912510337361133501367)
        ·
          refine ⟨7297368765506041700252051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4864912510337361133501367 7297368765506041700252051)
          ·
            refine ⟨10946053148259062550378077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7297368765506041700252051 10946053148259062550378077)
            ·
              refine ⟨4104769930597148456391779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10946053148259062550378077 4104769930597148456391779)
              ·
                refine ⟨6157154895895722684587669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4104769930597148456391779 6157154895895722684587669)
                ·
                  refine ⟨288616635745112000840047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6157154895895722684587669 288616635745112000840047)
                  ·
                    rfl

theorem cell23_5058710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_5058710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058710 prefixEnd_5058710 := by exact prefixLift 5058710
  have htrace : WordTrace (prefixWord ++ tailWord_5058710) baseStart_5058710 baseEnd_5058710 := by
    simpa [prefixWord, tailWord_5058710, baseEnd_5058710] using wordTrace_append hprefix tailTrace_5058710
  have hstable : (prefixWord ++ tailWord_5058710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058710).length < 2 ^ (prefixWord ++ tailWord_5058710).sum := by decide
  have hdescent : baseEnd_5058710 < baseStart_5058710 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058712 : List Nat := [2, 1, 2, 4, 3, 1, 1, 2, 1, 1, 5]
def baseStart_5058712 : Nat := 118140960795 + 5058712 * 2 ^ 59
def prefixEnd_5058712 : Nat := 4983230072969 + 3 ^ 40 * 5058712 * 2
def baseEnd_5058712 : Nat := 2597550748667316999735413

theorem tailTrace_5058712 : CollatzResearch.WordTrace tailWord_5058712 prefixEnd_5058712 2597550748667316999735413 := by
  unfold tailWord_5058712
  simp only [CollatzResearch.WordTrace]
  refine ⟨92253192224578929035701195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123004256299438572047601593 92253192224578929035701195)
  ·
    refine ⟨138379788336868393553551793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92253192224578929035701195 138379788336868393553551793)
    ·
      refine ⟨103784841252651295165163845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138379788336868393553551793 103784841252651295165163845)
      ·
        refine ⟨19459657734872117843468221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103784841252651295165163845 19459657734872117843468221)
        ·
          refine ⟨7297371650577044191300583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19459657734872117843468221 7297371650577044191300583)
          ·
            refine ⟨10946057475865566286950875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7297371650577044191300583 10946057475865566286950875)
            ·
              refine ⟨16419086213798349430426313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10946057475865566286950875 16419086213798349430426313)
              ·
                refine ⟨12314314660348762072819735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16419086213798349430426313 12314314660348762072819735)
                ·
                  refine ⟨18471471990523143109229603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12314314660348762072819735 18471471990523143109229603)
                  ·
                    refine ⟨27707207985784714663844405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18471471990523143109229603 27707207985784714663844405)
                    ·
                      refine ⟨2597550748667316999735413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27707207985784714663844405 2597550748667316999735413)
                      ·
                        rfl

theorem cell23_5058712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_5058712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058712 prefixEnd_5058712 := by exact prefixLift 5058712
  have htrace : WordTrace (prefixWord ++ tailWord_5058712) baseStart_5058712 baseEnd_5058712 := by
    simpa [prefixWord, tailWord_5058712, baseEnd_5058712] using wordTrace_append hprefix tailTrace_5058712
  have hstable : (prefixWord ++ tailWord_5058712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058712).length < 2 ^ (prefixWord ++ tailWord_5058712).sum := by decide
  have hdescent : baseEnd_5058712 < baseStart_5058712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058722 : List Nat := [3, 3, 1, 3, 1, 2, 1, 1, 1, 1, 6]
def baseStart_5058722 : Nat := 118140960795 + 5058722 * 2 ^ 59
def prefixEnd_5058722 : Nat := 4983230072969 + 3 ^ 40 * 5058722 * 2
def baseEnd_5058722 : Nat := 2597555883473861960610367

theorem tailTrace_5058722 : CollatzResearch.WordTrace tailWord_5058722 prefixEnd_5058722 2597555883473861960610367 := by
  unfold tailWord_5058722
  simp only [CollatzResearch.WordTrace]
  refine ⟨46126687294780407444816605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123004499452747753186177613 46126687294780407444816605)
  ·
    refine ⟨17297507735542652791806227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46126687294780407444816605 17297507735542652791806227)
    ·
      refine ⟨25946261603313979187709341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17297507735542652791806227 25946261603313979187709341)
      ·
        refine ⟨9729848101242742195391003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25946261603313979187709341 9729848101242742195391003)
        ·
          refine ⟨14594772151864113293086505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9729848101242742195391003 14594772151864113293086505)
          ·
            refine ⟨10946079113898084969814879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14594772151864113293086505 10946079113898084969814879)
            ·
              refine ⟨16419118670847127454722319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10946079113898084969814879 16419118670847127454722319)
              ·
                refine ⟨24628678006270691182083479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16419118670847127454722319 24628678006270691182083479)
                ·
                  refine ⟨36943017009406036773125219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24628678006270691182083479 36943017009406036773125219)
                  ·
                    refine ⟨55414525514109055159687829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36943017009406036773125219 55414525514109055159687829)
                    ·
                      refine ⟨2597555883473861960610367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55414525514109055159687829 2597555883473861960610367)
                      ·
                        rfl

theorem cell23_5058722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_5058722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058722 prefixEnd_5058722 := by exact prefixLift 5058722
  have htrace : WordTrace (prefixWord ++ tailWord_5058722) baseStart_5058722 baseEnd_5058722 := by
    simpa [prefixWord, tailWord_5058722, baseEnd_5058722] using wordTrace_append hprefix tailTrace_5058722
  have hstable : (prefixWord ++ tailWord_5058722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058722).length < 2 ^ (prefixWord ++ tailWord_5058722).sum := by decide
  have hdescent : baseEnd_5058722 < baseStart_5058722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058743 : List Nat := [1, 1, 3, 1, 4, 4, 1, 3, 1, 2, 2]
def baseStart_5058743 : Nat := 118140960795 + 5058743 * 2 ^ 59
def prefixEnd_5058743 : Nat := 4983230072969 + 3 ^ 40 * 5058743 * 2
def baseEnd_5058743 : Nat := 2597566666567606378447771

theorem tailTrace_5058743 : CollatzResearch.WordTrace tailWord_5058743 prefixEnd_5058743 2597566666567606378447771 := by
  unfold tailWord_5058743
  simp only [CollatzResearch.WordTrace]
  refine ⟨184507515112045550365780883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123005010074697033577187255 184507515112045550365780883)
  ·
    refine ⟨276761272668068325548671325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184507515112045550365780883 276761272668068325548671325)
    ·
      refine ⟨103785477250525622080751747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 276761272668068325548671325 103785477250525622080751747)
      ·
        refine ⟨155678215875788433121127621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103785477250525622080751747 155678215875788433121127621)
        ·
          refine ⟨29189665476710331210211429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 155678215875788433121127621 29189665476710331210211429)
          ·
            refine ⟨5473062276883187101914643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29189665476710331210211429 5473062276883187101914643)
            ·
              refine ⟨8209593415324780652871965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5473062276883187101914643 8209593415324780652871965)
              ·
                refine ⟨3078597530746792744826987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8209593415324780652871965 3078597530746792744826987)
                ·
                  refine ⟨4617896296120189117240481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3078597530746792744826987 4617896296120189117240481)
                  ·
                    refine ⟨3463422222090141837930361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4617896296120189117240481 3463422222090141837930361)
                    ·
                      refine ⟨2597566666567606378447771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3463422222090141837930361 2597566666567606378447771)
                      ·
                        rfl

theorem cell23_5058743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 3, 1, 2, 2].length) (baseStart_5058743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058743 prefixEnd_5058743 := by exact prefixLift 5058743
  have htrace : WordTrace (prefixWord ++ tailWord_5058743) baseStart_5058743 baseEnd_5058743 := by
    simpa [prefixWord, tailWord_5058743, baseEnd_5058743] using wordTrace_append hprefix tailTrace_5058743
  have hstable : (prefixWord ++ tailWord_5058743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058743).length < 2 ^ (prefixWord ++ tailWord_5058743).sum := by decide
  have hdescent : baseEnd_5058743 < baseStart_5058743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058776 : List Nat := [2, 1, 2, 2, 4, 1, 4, 1, 2, 1, 3]
def baseStart_5058776 : Nat := 118140960795 + 5058776 * 2 ^ 59
def prefixEnd_5058776 : Nat := 4983230072969 + 3 ^ 40 * 5058776 * 2
def baseEnd_5058776 : Nat := 2597583611429204749335119

theorem tailTrace_5058776 : CollatzResearch.WordTrace tailWord_5058776 prefixEnd_5058776 2597583611429204749335119 := by
  unfold tailWord_5058776
  simp only [CollatzResearch.WordTrace]
  refine ⟨92254359360462998500866091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123005812480617331334488121 92254359360462998500866091)
  ·
    refine ⟨138381539040694497751299137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92254359360462998500866091 138381539040694497751299137)
    ·
      refine ⟨103786154280520873313474353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138381539040694497751299137 103786154280520873313474353)
      ·
        refine ⟨77839615710390654985105765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103786154280520873313474353 77839615710390654985105765)
        ·
          refine ⟨14594927945698247809707331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77839615710390654985105765 14594927945698247809707331)
          ·
            refine ⟨21892391918547371714560997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14594927945698247809707331 21892391918547371714560997)
            ·
              refine ⟨4104823484727632196480187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21892391918547371714560997 4104823484727632196480187)
              ·
                refine ⟨6157235227091448294720281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4104823484727632196480187 6157235227091448294720281)
                ·
                  refine ⟨4617926420318586221040211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6157235227091448294720281 4617926420318586221040211)
                  ·
                    refine ⟨6926889630477879331560317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4617926420318586221040211 6926889630477879331560317)
                    ·
                      refine ⟨2597583611429204749335119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6926889630477879331560317 2597583611429204749335119)
                      ·
                        rfl

theorem cell23_5058776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 2, 1, 3].length) (baseStart_5058776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058776 prefixEnd_5058776 := by exact prefixLift 5058776
  have htrace : WordTrace (prefixWord ++ tailWord_5058776) baseStart_5058776 baseEnd_5058776 := by
    simpa [prefixWord, tailWord_5058776, baseEnd_5058776] using wordTrace_append hprefix tailTrace_5058776
  have hstable : (prefixWord ++ tailWord_5058776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058776).length < 2 ^ (prefixWord ++ tailWord_5058776).sum := by decide
  have hdescent : baseEnd_5058776 < baseStart_5058776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058780 : List Nat := [2, 2, 5, 2, 2, 1, 1, 2, 1, 2, 3]
def baseStart_5058780 : Nat := 118140960795 + 5058780 * 2 ^ 59
def prefixEnd_5058780 : Nat := 4983230072969 + 3 ^ 40 * 5058780 * 2
def baseEnd_5058780 : Nat := 2597585665351822733685101

theorem tailTrace_5058780 : CollatzResearch.WordTrace tailWord_5058780 prefixEnd_5058780 2597585665351822733685101 := by
  unfold tailWord_5058780
  simp only [CollatzResearch.WordTrace]
  refine ⟨92254432306455752842438897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123005909741941003789918529 92254432306455752842438897)
  ·
    refine ⟨69190824229841814631829173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92254432306455752842438897 69190824229841814631829173)
    ·
      refine ⟨6486639771547670121733985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69190824229841814631829173 6486639771547670121733985)
      ·
        refine ⟨4864979828660752591300489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6486639771547670121733985 4864979828660752591300489)
        ·
          refine ⟨3648734871495564443475367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4864979828660752591300489 3648734871495564443475367)
          ·
            refine ⟨5473102307243346665213051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3648734871495564443475367 5473102307243346665213051)
            ·
              refine ⟨8209653460865019997819577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5473102307243346665213051 8209653460865019997819577)
              ·
                refine ⟨6157240095648764998364683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8209653460865019997819577 6157240095648764998364683)
                ·
                  refine ⟨9235860143473147497547025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6157240095648764998364683 9235860143473147497547025)
                  ·
                    refine ⟨6926895107604860623160269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9235860143473147497547025 6926895107604860623160269)
                    ·
                      refine ⟨2597585665351822733685101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6926895107604860623160269 2597585665351822733685101)
                      ·
                        rfl

theorem cell23_5058780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_5058780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058780 prefixEnd_5058780 := by exact prefixLift 5058780
  have htrace : WordTrace (prefixWord ++ tailWord_5058780) baseStart_5058780 baseEnd_5058780 := by
    simpa [prefixWord, tailWord_5058780, baseEnd_5058780] using wordTrace_append hprefix tailTrace_5058780
  have hstable : (prefixWord ++ tailWord_5058780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058780).length < 2 ^ (prefixWord ++ tailWord_5058780).sum := by decide
  have hdescent : baseEnd_5058780 < baseStart_5058780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058785 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 4, 1, 5]
def baseStart_5058785 : Nat := 118140960795 + 5058785 * 2 ^ 59
def prefixEnd_5058785 : Nat := 4983230072969 + 3 ^ 40 * 5058785 * 2
def baseEnd_5058785 : Nat := 2597588232755095214122577

theorem tailTrace_5058785 : CollatzResearch.WordTrace tailWord_5058785 prefixEnd_5058785 2597588232755095214122577 := by
  unfold tailWord_5058785
  simp only [CollatzResearch.WordTrace]
  refine ⟨184509046977893391538809809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123006031318595594359206539 184509046977893391538809809)
  ·
    refine ⟨138381785233420043654107357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184509046977893391538809809 138381785233420043654107357)
    ·
      refine ⟨51893169462532516370290259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138381785233420043654107357 51893169462532516370290259)
      ·
        refine ⟨77839754193798774555435389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51893169462532516370290259 77839754193798774555435389)
        ·
          refine ⟨29189907822674540458288271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77839754193798774555435389 29189907822674540458288271)
          ·
            refine ⟨43784861734011810687432407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29189907822674540458288271 43784861734011810687432407)
            ·
              refine ⟨65677292601017716031148611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43784861734011810687432407 65677292601017716031148611)
              ·
                refine ⟨98515938901526574046722917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65677292601017716031148611 98515938901526574046722917)
                ·
                  refine ⟨18471738544036232633760547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98515938901526574046722917 18471738544036232633760547)
                  ·
                    refine ⟨27707607816054348950640821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18471738544036232633760547 27707607816054348950640821)
                    ·
                      refine ⟨2597588232755095214122577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27707607816054348950640821 2597588232755095214122577)
                      ·
                        rfl

theorem cell23_5058785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_5058785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058785 prefixEnd_5058785 := by exact prefixLift 5058785
  have htrace : WordTrace (prefixWord ++ tailWord_5058785) baseStart_5058785 baseEnd_5058785 := by
    simpa [prefixWord, tailWord_5058785, baseEnd_5058785] using wordTrace_append hprefix tailTrace_5058785
  have hstable : (prefixWord ++ tailWord_5058785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058785).length < 2 ^ (prefixWord ++ tailWord_5058785).sum := by decide
  have hdescent : baseEnd_5058785 < baseStart_5058785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058799 : List Nat := [1, 1, 2, 1, 6, 2, 1, 2, 1, 4, 2]
def baseStart_5058799 : Nat := 118140960795 + 5058799 * 2 ^ 59
def prefixEnd_5058799 : Nat := 4983230072969 + 3 ^ 40 * 5058799 * 2
def baseEnd_5058799 : Nat := 2597595421484258159347513

theorem tailTrace_5058799 : CollatzResearch.WordTrace tailWord_5058799 prefixEnd_5058799 2597595421484258159347513 := by
  unfold tailWord_5058799
  simp only [CollatzResearch.WordTrace]
  refine ⟨184509557599842671929819451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123006371733228447953212967 184509557599842671929819451)
  ·
    refine ⟨276764336399764007894729177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184509557599842671929819451 276764336399764007894729177)
    ·
      refine ⟨207573252299823005921046883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276764336399764007894729177 207573252299823005921046883)
      ·
        refine ⟨311359878449734508881570325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207573252299823005921046883 311359878449734508881570325)
        ·
          refine ⟨14594994302331305103823609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 311359878449734508881570325 14594994302331305103823609)
          ·
            refine ⟨10946245726748478827867707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14594994302331305103823609 10946245726748478827867707)
            ·
              refine ⟨16419368590122718241801561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10946245726748478827867707 16419368590122718241801561)
              ·
                refine ⟨12314526442592038681351171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16419368590122718241801561 12314526442592038681351171)
                ·
                  refine ⟨18471789663888058022026757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12314526442592038681351171 18471789663888058022026757)
                  ·
                    refine ⟨3463460561979010879130017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18471789663888058022026757 3463460561979010879130017)
                    ·
                      refine ⟨2597595421484258159347513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3463460561979010879130017 2597595421484258159347513)
                      ·
                        rfl

theorem cell23_5058799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 4, 2].length) (baseStart_5058799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058799 prefixEnd_5058799 := by exact prefixLift 5058799
  have htrace : WordTrace (prefixWord ++ tailWord_5058799) baseStart_5058799 baseEnd_5058799 := by
    simpa [prefixWord, tailWord_5058799, baseEnd_5058799] using wordTrace_append hprefix tailTrace_5058799
  have hstable : (prefixWord ++ tailWord_5058799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058799).length < 2 ^ (prefixWord ++ tailWord_5058799).sum := by decide
  have hdescent : baseEnd_5058799 < baseStart_5058799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058802 : List Nat := [3, 2, 1, 3, 2, 1, 2, 1, 2, 1, 5]
def baseStart_5058802 : Nat := 118140960795 + 5058802 * 2 ^ 59
def prefixEnd_5058802 : Nat := 4983230072969 + 3 ^ 40 * 5058802 * 2
def baseEnd_5058802 : Nat := 2597596961926221647609999

theorem tailTrace_5058802 : CollatzResearch.WordTrace tailWord_5058802 prefixEnd_5058802 2597596961926221647609999 := by
  unfold tailWord_5058802
  simp only [CollatzResearch.WordTrace]
  refine ⟨46127416754707950860544665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123006444679221202294785773 46127416754707950860544665)
  ·
    refine ⟨34595562566030963145408499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46127416754707950860544665 34595562566030963145408499)
    ·
      refine ⟨51893343849046444718112749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34595562566030963145408499 51893343849046444718112749)
      ·
        refine ⟨19460003943392416769292281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51893343849046444718112749 19460003943392416769292281)
        ·
          refine ⟨14595002957544312576969211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19460003943392416769292281 14595002957544312576969211)
          ·
            refine ⟨21892504436316468865453817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14595002957544312576969211 21892504436316468865453817)
            ·
              refine ⟨16419378327237351649090363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21892504436316468865453817 16419378327237351649090363)
              ·
                refine ⟨24629067490856027473635545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16419378327237351649090363 24629067490856027473635545)
                ·
                  refine ⟨18471800618142020605226659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24629067490856027473635545 18471800618142020605226659)
                  ·
                    refine ⟨27707700927213030907839989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18471800618142020605226659 27707700927213030907839989)
                    ·
                      refine ⟨2597596961926221647609999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27707700927213030907839989 2597596961926221647609999)
                      ·
                        rfl

theorem cell23_5058802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_5058802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058802 prefixEnd_5058802 := by exact prefixLift 5058802
  have htrace : WordTrace (prefixWord ++ tailWord_5058802) baseStart_5058802 baseEnd_5058802 := by
    simpa [prefixWord, tailWord_5058802, baseEnd_5058802] using wordTrace_append hprefix tailTrace_5058802
  have hstable : (prefixWord ++ tailWord_5058802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058802).length < 2 ^ (prefixWord ++ tailWord_5058802).sum := by decide
  have hdescent : baseEnd_5058802 < baseStart_5058802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058835 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 4, 5]
def baseStart_5058835 : Nat := 118140960795 + 5058835 * 2 ^ 59
def prefixEnd_5058835 : Nat := 4983230072969 + 3 ^ 40 * 5058835 * 2
def baseEnd_5058835 : Nat := 865871302262606672832449

theorem tailTrace_5058835 : CollatzResearch.WordTrace tailWord_5058835 prefixEnd_5058835 865871302262606672832449 := by
  unfold tailWord_5058835
  simp only [CollatzResearch.WordTrace]
  refine ⟨184510870627712250078129959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123007247085141500052086639 184510870627712250078129959)
  ·
    refine ⟨276766305941568375117194939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184510870627712250078129959 276766305941568375117194939)
    ·
      refine ⟨415149458912352562675792409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276766305941568375117194939 415149458912352562675792409)
      ·
        refine ⟨311362094184264422006844307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 415149458912352562675792409 311362094184264422006844307)
        ·
          refine ⟨467043141276396633010266461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311362094184264422006844307 467043141276396633010266461)
          ·
            refine ⟨175141177978648737378849923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 467043141276396633010266461 175141177978648737378849923)
            ·
              refine ⟨262711766967973106068274885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175141177978648737378849923 262711766967973106068274885)
              ·
                refine ⟨49258456306494957387801541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 262711766967973106068274885 49258456306494957387801541)
                ·
                  refine ⟨9235960557467804510212789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49258456306494957387801541 9235960557467804510212789)
                  ·
                    refine ⟨865871302262606672832449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9235960557467804510212789 865871302262606672832449)
                    ·
                      rfl

theorem cell23_5058835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 5].length) (baseStart_5058835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058835 prefixEnd_5058835 := by exact prefixLift 5058835
  have htrace : WordTrace (prefixWord ++ tailWord_5058835) baseStart_5058835 baseEnd_5058835 := by
    simpa [prefixWord, tailWord_5058835, baseEnd_5058835] using wordTrace_append hprefix tailTrace_5058835
  have hstable : (prefixWord ++ tailWord_5058835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058835).length < 2 ^ (prefixWord ++ tailWord_5058835).sum := by decide
  have hdescent : baseEnd_5058835 < baseStart_5058835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058852 : List Nat := [2, 3, 1, 3, 1, 3, 1, 1, 1, 7]
def baseStart_5058852 : Nat := 118140960795 + 5058852 * 2 ^ 59
def prefixEnd_5058852 : Nat := 4983230072969 + 3 ^ 40 * 5058852 * 2
def baseEnd_5058852 : Nat := 865874211986315483994923

theorem tailTrace_5058852 : CollatzResearch.WordTrace tailWord_5058852 prefixEnd_5058852 865874211986315483994923 := by
  unfold tailWord_5058852
  simp only [CollatzResearch.WordTrace]
  refine ⟨92255745334325330990749405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123007660445767107987665873 92255745334325330990749405)
  ·
    refine ⟨34595904500371999121531027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92255745334325330990749405 34595904500371999121531027)
    ·
      refine ⟨51893856750557998682296541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34595904500371999121531027 51893856750557998682296541)
      ·
        refine ⟨19460196281459249505861203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51893856750557998682296541 19460196281459249505861203)
        ·
          refine ⟨29190294422188874258791805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19460196281459249505861203 29190294422188874258791805)
          ·
            refine ⟨10946360408320827847046927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29190294422188874258791805 10946360408320827847046927)
            ·
              refine ⟨16419540612481241770570391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10946360408320827847046927 16419540612481241770570391)
              ·
                refine ⟨24629310918721862655855587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16419540612481241770570391 24629310918721862655855587)
                ·
                  refine ⟨36943966378082793983783381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24629310918721862655855587 36943966378082793983783381)
                  ·
                    refine ⟨865874211986315483994923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36943966378082793983783381 865874211986315483994923)
                    ·
                      rfl

theorem cell23_5058852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_5058852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058852 prefixEnd_5058852 := by exact prefixLift 5058852
  have htrace : WordTrace (prefixWord ++ tailWord_5058852) baseStart_5058852 baseEnd_5058852 := by
    simpa [prefixWord, tailWord_5058852, baseEnd_5058852] using wordTrace_append hprefix tailTrace_5058852
  have hstable : (prefixWord ++ tailWord_5058852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058852).length < 2 ^ (prefixWord ++ tailWord_5058852).sum := by decide
  have hdescent : baseEnd_5058852 < baseStart_5058852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058856 : List Nat := [2, 1, 5, 1, 3, 1, 2, 3, 5]
def baseStart_5058856 : Nat := 118140960795 + 5058856 * 2 ^ 59
def prefixEnd_5058856 : Nat := 4983230072969 + 3 ^ 40 * 5058856 * 2
def baseEnd_5058856 : Nat := 288624965542396048481639

theorem tailTrace_5058856 : CollatzResearch.WordTrace tailWord_5058856 prefixEnd_5058856 288624965542396048481639 := by
  unfold tailWord_5058856
  simp only [CollatzResearch.WordTrace]
  refine ⟨92255818280318085332322211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123007757707090780443096281 92255818280318085332322211)
  ·
    refine ⟨138383727420477127998483317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92255818280318085332322211 138383727420477127998483317)
    ·
      refine ⟨12973474445669730749857811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138383727420477127998483317 12973474445669730749857811)
      ·
        refine ⟨19460211668504596124786717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12973474445669730749857811 19460211668504596124786717)
        ·
          refine ⟨7297579375689223546795019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19460211668504596124786717 7297579375689223546795019)
          ·
            refine ⟨10946369063533835320192529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7297579375689223546795019 10946369063533835320192529)
            ·
              refine ⟨8209776797650376490144397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10946369063533835320192529 8209776797650376490144397)
              ·
                refine ⟨3078666299118891183804149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8209776797650376490144397 3078666299118891183804149)
                ·
                  refine ⟨288624965542396048481639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3078666299118891183804149 288624965542396048481639)
                  ·
                    rfl

theorem cell23_5058856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 3, 5].length) (baseStart_5058856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058856 prefixEnd_5058856 := by exact prefixLift 5058856
  have htrace : WordTrace (prefixWord ++ tailWord_5058856) baseStart_5058856 baseEnd_5058856 := by
    simpa [prefixWord, tailWord_5058856, baseEnd_5058856] using wordTrace_append hprefix tailTrace_5058856
  have hstable : (prefixWord ++ tailWord_5058856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058856).length < 2 ^ (prefixWord ++ tailWord_5058856).sum := by decide
  have hdescent : baseEnd_5058856 < baseStart_5058856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058872 : List Nat := [2, 1, 2, 1, 3, 1, 2, 4, 2, 1, 4]
def baseStart_5058872 : Nat := 118140960795 + 5058872 * 2 ^ 59
def prefixEnd_5058872 : Nat := 4983230072969 + 3 ^ 40 * 5058872 * 2
def baseEnd_5058872 : Nat := 2597632905572036373734677

theorem tailTrace_5058872 : CollatzResearch.WordTrace tailWord_5058872 prefixEnd_5058872 2597632905572036373734677 := by
  unfold tailWord_5058872
  simp only [CollatzResearch.WordTrace]
  refine ⟨92256110064289102698613435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123008146752385470264817913 92256110064289102698613435)
  ·
    refine ⟨138384165096433654047920153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92256110064289102698613435 138384165096433654047920153)
    ·
      refine ⟨103788123822325240535940115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138384165096433654047920153 103788123822325240535940115)
      ·
        refine ⟨155682185733487860803910173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103788123822325240535940115 155682185733487860803910173)
        ·
          refine ⟨58380819650057947801466315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155682185733487860803910173 58380819650057947801466315)
          ·
            refine ⟨87571229475086921702199473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58380819650057947801466315 87571229475086921702199473)
            ·
              refine ⟨65678422106315191276649605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87571229475086921702199473 65678422106315191276649605)
              ·
                refine ⟨12314704144934098364371801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65678422106315191276649605 12314704144934098364371801)
                ·
                  refine ⟨9236028108700573773278851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12314704144934098364371801 9236028108700573773278851)
                  ·
                    refine ⟨13854042163050860659918277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9236028108700573773278851 13854042163050860659918277)
                    ·
                      refine ⟨2597632905572036373734677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13854042163050860659918277 2597632905572036373734677)
                      ·
                        rfl

theorem cell23_5058872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_5058872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058872 prefixEnd_5058872 := by exact prefixLift 5058872
  have htrace : WordTrace (prefixWord ++ tailWord_5058872) baseStart_5058872 baseEnd_5058872 := by
    simpa [prefixWord, tailWord_5058872, baseEnd_5058872] using wordTrace_append hprefix tailTrace_5058872
  have hstable : (prefixWord ++ tailWord_5058872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058872).length < 2 ^ (prefixWord ++ tailWord_5058872).sum := by decide
  have hdescent : baseEnd_5058872 < baseStart_5058872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058892 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 3, 4, 3]
def baseStart_5058892 : Nat := 118140960795 + 5058892 * 2 ^ 59
def prefixEnd_5058892 : Nat := 4983230072969 + 3 ^ 40 * 5058892 * 2
def baseEnd_5058892 : Nat := 2597643175185126295484585

theorem tailTrace_5058892 : CollatzResearch.WordTrace tailWord_5058892 prefixEnd_5058892 2597643175185126295484585 := by
  unfold tailWord_5058892
  simp only [CollatzResearch.WordTrace]
  refine ⟨92256474794252874406477465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123008633059003832541969953 92256474794252874406477465)
  ·
    refine ⟨69192356095689655804858099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92256474794252874406477465 69192356095689655804858099)
    ·
      refine ⟨103788534143534483707287149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69192356095689655804858099 103788534143534483707287149)
      ·
        refine ⟨38920700303825431390232681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103788534143534483707287149 38920700303825431390232681)
        ·
          refine ⟨29190525227869073542674511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38920700303825431390232681 29190525227869073542674511)
          ·
            refine ⟨43785787841803610314011767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29190525227869073542674511 43785787841803610314011767)
            ·
              refine ⟨65678681762705415471017651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43785787841803610314011767 65678681762705415471017651)
              ·
                refine ⟨98518022644058123206526477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65678681762705415471017651 98518022644058123206526477)
                ·
                  refine ⟨36944258491521796202447429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98518022644058123206526477 36944258491521796202447429)
                  ·
                    refine ⟨6927048467160336787958893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36944258491521796202447429 6927048467160336787958893)
                    ·
                      refine ⟨2597643175185126295484585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6927048467160336787958893 2597643175185126295484585)
                      ·
                        rfl

theorem cell23_5058892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_5058892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058892 prefixEnd_5058892 := by exact prefixLift 5058892
  have htrace : WordTrace (prefixWord ++ tailWord_5058892) baseStart_5058892 baseEnd_5058892 := by
    simpa [prefixWord, tailWord_5058892, baseEnd_5058892] using wordTrace_append hprefix tailTrace_5058892
  have hstable : (prefixWord ++ tailWord_5058892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058892).length < 2 ^ (prefixWord ++ tailWord_5058892).sum := by decide
  have hdescent : baseEnd_5058892 < baseStart_5058892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058949 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 6, 3, 2]
def baseStart_5058949 : Nat := 118140960795 + 5058949 * 2 ^ 59
def prefixEnd_5058949 : Nat := 4983230072969 + 3 ^ 40 * 5058949 * 2
def baseEnd_5058949 : Nat := 2597672443582432572471823

theorem tailTrace_5058949 : CollatzResearch.WordTrace tailWord_5058949 prefixEnd_5058949 2597672443582432572471823 := by
  unfold tailWord_5058949
  simp only [CollatzResearch.WordTrace]
  refine ⟨184515028549299247547779901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123010019032866165031853267 184515028549299247547779901)
  ·
    refine ⟨69193135705987217830417463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184515028549299247547779901 69193135705987217830417463)
    ·
      refine ⟨103789703558980826745626195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69193135705987217830417463 103789703558980826745626195)
      ·
        refine ⟨155684555338471240118439293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103789703558980826745626195 155684555338471240118439293)
        ·
          refine ⟨58381708251926715044414735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155684555338471240118439293 58381708251926715044414735)
          ·
            refine ⟨87572562377890072566622103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58381708251926715044414735 87572562377890072566622103)
            ·
              refine ⟨131358843566835108849933155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87572562377890072566622103 131358843566835108849933155)
              ·
                refine ⟨197038265350252663274899733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131358843566835108849933155 197038265350252663274899733)
                ·
                  refine ⟨9236168688293093591010925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 197038265350252663274899733 9236168688293093591010925)
                  ·
                    refine ⟨3463563258109910096629097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9236168688293093591010925 3463563258109910096629097)
                    ·
                      refine ⟨2597672443582432572471823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3463563258109910096629097 2597672443582432572471823)
                      ·
                        rfl

theorem cell23_5058949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 3, 2].length) (baseStart_5058949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058949 prefixEnd_5058949 := by exact prefixLift 5058949
  have htrace : WordTrace (prefixWord ++ tailWord_5058949) baseStart_5058949 baseEnd_5058949 := by
    simpa [prefixWord, tailWord_5058949, baseEnd_5058949] using wordTrace_append hprefix tailTrace_5058949
  have hstable : (prefixWord ++ tailWord_5058949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058949).length < 2 ^ (prefixWord ++ tailWord_5058949).sum := by decide
  have hdescent : baseEnd_5058949 < baseStart_5058949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058976 : List Nat := [2, 1, 1, 4, 1, 4, 3, 1, 1, 5]
def baseStart_5058976 : Nat := 118140960795 + 5058976 * 2 ^ 59
def prefixEnd_5058976 : Nat := 4983230072969 + 3 ^ 40 * 5058976 * 2
def baseEnd_5058976 : Nat := 865895435853367988944733

theorem tailTrace_5058976 : CollatzResearch.WordTrace tailWord_5058976 prefixEnd_5058976 865895435853367988944733 := by
  unfold tailWord_5058976
  simp only [CollatzResearch.WordTrace]
  refine ⟨92258006660100715579506391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123010675546800954106008521 92258006660100715579506391)
  ·
    refine ⟨138387009990151073369259587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92258006660100715579506391 138387009990151073369259587)
    ·
      refine ⟨207580514985226610053889381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138387009990151073369259587 207580514985226610053889381)
      ·
        refine ⟨38921346559729989385104259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207580514985226610053889381 38921346559729989385104259)
        ·
          refine ⟨58382019839594984077656389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38921346559729989385104259 58382019839594984077656389)
          ·
            refine ⟨10946628719924059514560573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58382019839594984077656389 10946628719924059514560573)
            ·
              refine ⟨4104985769971522317960215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10946628719924059514560573 4104985769971522317960215)
              ·
                refine ⟨6157478654957283476940323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4104985769971522317960215 6157478654957283476940323)
                ·
                  refine ⟨9236217982435925215410485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6157478654957283476940323 9236217982435925215410485)
                  ·
                    refine ⟨865895435853367988944733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9236217982435925215410485 865895435853367988944733)
                    ·
                      rfl

theorem cell23_5058976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 1, 5].length) (baseStart_5058976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058976 prefixEnd_5058976 := by exact prefixLift 5058976
  have htrace : WordTrace (prefixWord ++ tailWord_5058976) baseStart_5058976 baseEnd_5058976 := by
    simpa [prefixWord, tailWord_5058976, baseEnd_5058976] using wordTrace_append hprefix tailTrace_5058976
  have hstable : (prefixWord ++ tailWord_5058976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058976).length < 2 ^ (prefixWord ++ tailWord_5058976).sum := by decide
  have hdescent : baseEnd_5058976 < baseStart_5058976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5058999 : List Nat := [1, 1, 3, 1, 3, 3, 1, 2, 3, 2, 3]
def baseStart_5058999 : Nat := 118140960795 + 5058999 * 2 ^ 59
def prefixEnd_5058999 : Nat := 4983230072969 + 3 ^ 40 * 5058999 * 2
def baseEnd_5058999 : Nat := 2597698117615157376846593

theorem tailTrace_5058999 : CollatzResearch.WordTrace tailWord_5058999 prefixEnd_5058999 2597698117615157376846593 := by
  unfold tailWord_5058999
  simp only [CollatzResearch.WordTrace]
  refine ⟨184516852199118106087100051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123011234799412070724733367 184516852199118106087100051)
  ·
    refine ⟨276775278298677159130650077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184516852199118106087100051 276775278298677159130650077)
    ·
      refine ⟨103790729362003934673993779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 276775278298677159130650077 103790729362003934673993779)
      ·
        refine ⟨155686094043005902010990669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103790729362003934673993779 155686094043005902010990669)
        ·
          refine ⟨58382285266127213254121501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155686094043005902010990669 58382285266127213254121501)
          ·
            refine ⟨21893356974797704970295563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58382285266127213254121501 21893356974797704970295563)
            ·
              refine ⟨32840035462196557455443345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21893356974797704970295563 32840035462196557455443345)
              ·
                refine ⟨24630026596647418091582509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32840035462196557455443345 24630026596647418091582509)
                ·
                  refine ⟨9236259973742781784343441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24630026596647418091582509 9236259973742781784343441)
                  ·
                    refine ⟨6927194980307086338257581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9236259973742781784343441 6927194980307086338257581)
                    ·
                      refine ⟨2597698117615157376846593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6927194980307086338257581 2597698117615157376846593)
                      ·
                        rfl

theorem cell23_5058999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 2, 3].length) (baseStart_5058999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5058999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5058999 prefixEnd_5058999 := by exact prefixLift 5058999
  have htrace : WordTrace (prefixWord ++ tailWord_5058999) baseStart_5058999 baseEnd_5058999 := by
    simpa [prefixWord, tailWord_5058999, baseEnd_5058999] using wordTrace_append hprefix tailTrace_5058999
  have hstable : (prefixWord ++ tailWord_5058999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5058999).length < 2 ^ (prefixWord ++ tailWord_5058999).sum := by decide
  have hdescent : baseEnd_5058999 < baseStart_5058999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5058999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059006 : List Nat := [4, 2, 1, 1, 1, 1, 4, 3, 2, 4]
def baseStart_5059006 : Nat := 118140960795 + 5059006 * 2 ^ 59
def prefixEnd_5059006 : Nat := 4983230072969 + 3 ^ 40 * 5059006 * 2
def baseEnd_5059006 : Nat := 865900570659912949819687

theorem tailTrace_5059006 : CollatzResearch.WordTrace tailWord_5059006 prefixEnd_5059006 865900570659912949819687 := by
  unfold tailWord_5059006
  simp only [CollatzResearch.WordTrace]
  refine ⟨23064638438761593285325609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123011405006728497521736581 23064638438761593285325609)
  ·
    refine ⟨17298478829071194963994207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23064638438761593285325609 17298478829071194963994207)
    ·
      refine ⟨25947718243606792445991311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17298478829071194963994207 25947718243606792445991311)
      ·
        refine ⟨38921577365410188668986967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25947718243606792445991311 38921577365410188668986967)
        ·
          refine ⟨58382366048115283003480451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38921577365410188668986967 58382366048115283003480451)
          ·
            refine ⟨87573549072172924505220677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58382366048115283003480451 87573549072172924505220677)
            ·
              refine ⟨16420040451032423344728877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87573549072172924505220677 16420040451032423344728877)
              ·
                refine ⟨6157515169137158754273329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16420040451032423344728877 6157515169137158754273329)
                ·
                  refine ⟨4618136376852869065704997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6157515169137158754273329 4618136376852869065704997)
                  ·
                    refine ⟨865900570659912949819687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4618136376852869065704997 865900570659912949819687)
                    ·
                      rfl

theorem cell23_5059006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_5059006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059006 prefixEnd_5059006 := by exact prefixLift 5059006
  have htrace : WordTrace (prefixWord ++ tailWord_5059006) baseStart_5059006 baseEnd_5059006 := by
    simpa [prefixWord, tailWord_5059006, baseEnd_5059006] using wordTrace_append hprefix tailTrace_5059006
  have hstable : (prefixWord ++ tailWord_5059006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059006).length < 2 ^ (prefixWord ++ tailWord_5059006).sum := by decide
  have hdescent : baseEnd_5059006 < baseStart_5059006 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059072 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 5]
def baseStart_5059072 : Nat := 118140960795 + 5059072 * 2 ^ 59
def prefixEnd_5059072 : Nat := 4983230072969 + 3 ^ 40 * 5059072 * 2
def baseEnd_5059072 : Nat := 2597735601702935591233757

theorem tailTrace_5059072 : CollatzResearch.WordTrace tailWord_5059072 prefixEnd_5059072 2597735601702935591233757 := by
  unfold tailWord_5059072
  simp only [CollatzResearch.WordTrace]
  refine ⟨92259757363926819777253735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123013009818569093036338313 92259757363926819777253735)
  ·
    refine ⟨138389636045890229665880603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92259757363926819777253735 138389636045890229665880603)
    ·
      refine ⟨207584454068835344498820905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138389636045890229665880603 207584454068835344498820905)
      ·
        refine ⟨155688340551626508374115679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207584454068835344498820905 155688340551626508374115679)
        ·
          refine ⟨233532510827439762561173519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155688340551626508374115679 233532510827439762561173519)
          ·
            refine ⟨350298766241159643841760279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233532510827439762561173519 350298766241159643841760279)
            ·
              refine ⟨525448149361739465762640419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350298766241159643841760279 525448149361739465762640419)
              ·
                refine ⟨788172224042609198643960629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 525448149361739465762640419 788172224042609198643960629)
                ·
                  refine ⟨73891146003994612372871309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 788172224042609198643960629 73891146003994612372871309)
                  ·
                    refine ⟨27709179751497979639826741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73891146003994612372871309 27709179751497979639826741)
                    ·
                      refine ⟨2597735601702935591233757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27709179751497979639826741 2597735601702935591233757)
                      ·
                        rfl

theorem cell23_5059072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_5059072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059072 prefixEnd_5059072 := by exact prefixLift 5059072
  have htrace : WordTrace (prefixWord ++ tailWord_5059072) baseStart_5059072 baseEnd_5059072 := by
    simpa [prefixWord, tailWord_5059072, baseEnd_5059072] using wordTrace_append hprefix tailTrace_5059072
  have hstable : (prefixWord ++ tailWord_5059072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059072).length < 2 ^ (prefixWord ++ tailWord_5059072).sum := by decide
  have hdescent : baseEnd_5059072 < baseStart_5059072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059073 : List Nat := [1, 2, 4, 1, 3, 1, 1, 4, 1, 3, 2]
def baseStart_5059073 : Nat := 118140960795 + 5059073 * 2 ^ 59
def prefixEnd_5059073 : Nat := 4983230072969 + 3 ^ 40 * 5059073 * 2
def baseEnd_5059073 : Nat := 2597736115183590087321253

theorem tailTrace_5059073 : CollatzResearch.WordTrace tailWord_5059073 prefixEnd_5059073 2597736115183590087321253 := by
  unfold tailWord_5059073
  simp only [CollatzResearch.WordTrace]
  refine ⟨184519551200850016725293873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123013034133900011150195915 184519551200850016725293873)
  ·
    refine ⟨138389663400637512543970405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184519551200850016725293873 138389663400637512543970405)
    ·
      refine ⟨25948061887619533601994451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138389663400637512543970405 25948061887619533601994451)
      ·
        refine ⟨38922092831429300402991677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25948061887619533601994451 38922092831429300402991677)
        ·
          refine ⟨14595784811785987651121879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38922092831429300402991677 14595784811785987651121879)
          ·
            refine ⟨21893677217678981476682819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14595784811785987651121879 21893677217678981476682819)
            ·
              refine ⟨32840515826518472215024229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21893677217678981476682819 32840515826518472215024229)
              ·
                refine ⟨6157596717472213540317043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32840515826518472215024229 6157596717472213540317043)
                ·
                  refine ⟨9236395076208320310475565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6157596717472213540317043 9236395076208320310475565)
                  ·
                    refine ⟨3463648153578120116428337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9236395076208320310475565 3463648153578120116428337)
                    ·
                      refine ⟨2597736115183590087321253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3463648153578120116428337 2597736115183590087321253)
                      ·
                        rfl

theorem cell23_5059073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_5059073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059073 prefixEnd_5059073 := by exact prefixLift 5059073
  have htrace : WordTrace (prefixWord ++ tailWord_5059073) baseStart_5059073 baseEnd_5059073 := by
    simpa [prefixWord, tailWord_5059073, baseEnd_5059073] using wordTrace_append hprefix tailTrace_5059073
  have hstable : (prefixWord ++ tailWord_5059073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059073).length < 2 ^ (prefixWord ++ tailWord_5059073).sum := by decide
  have hdescent : baseEnd_5059073 < baseStart_5059073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059103 : List Nat := [1, 1, 2, 4, 1, 1, 1, 6, 2, 2, 2]
def baseStart_5059103 : Nat := 118140960795 + 5059103 * 2 ^ 59
def prefixEnd_5059103 : Nat := 4983230072969 + 3 ^ 40 * 5059103 * 2
def baseEnd_5059103 : Nat := 2597751519603224969946115

theorem tailTrace_5059103 : CollatzResearch.WordTrace tailWord_5059103 prefixEnd_5059103 2597751519603224969946115 := by
  unfold tailWord_5059103
  simp only [CollatzResearch.WordTrace]
  refine ⟨184520645390741331848885963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123013763593827554565923975 184520645390741331848885963)
  ·
    refine ⟨276780968086111997773328945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184520645390741331848885963 276780968086111997773328945)
    ·
      refine ⟨207585726064583998329996709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276780968086111997773328945 207585726064583998329996709)
      ·
        refine ⟨38922323637109499686874383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207585726064583998329996709 38922323637109499686874383)
        ·
          refine ⟨58383485455664249530311575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38922323637109499686874383 58383485455664249530311575)
          ·
            refine ⟨87575228183496374295467363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58383485455664249530311575 87575228183496374295467363)
            ·
              refine ⟨131362842275244561443201045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87575228183496374295467363 131362842275244561443201045)
              ·
                refine ⟨6157633231652088817650049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 131362842275244561443201045 6157633231652088817650049)
                ·
                  refine ⟨4618224923739066613237537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6157633231652088817650049 4618224923739066613237537)
                  ·
                    refine ⟨3463668692804299959928153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4618224923739066613237537 3463668692804299959928153)
                    ·
                      refine ⟨2597751519603224969946115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3463668692804299959928153 2597751519603224969946115)
                      ·
                        rfl

theorem cell23_5059103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_5059103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059103 prefixEnd_5059103 := by exact prefixLift 5059103
  have htrace : WordTrace (prefixWord ++ tailWord_5059103) baseStart_5059103 baseEnd_5059103 := by
    simpa [prefixWord, tailWord_5059103, baseEnd_5059103] using wordTrace_append hprefix tailTrace_5059103
  have hstable : (prefixWord ++ tailWord_5059103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059103).length < 2 ^ (prefixWord ++ tailWord_5059103).sum := by decide
  have hdescent : baseEnd_5059103 < baseStart_5059103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059109 : List Nat := [1, 3, 1, 2, 2, 1, 5, 1, 7]
def baseStart_5059109 : Nat := 118140960795 + 5059109 * 2 ^ 59
def prefixEnd_5059109 : Nat := 4983230072969 + 3 ^ 40 * 5059109 * 2
def baseEnd_5059109 : Nat := 288639400054127994052343

theorem tailTrace_5059109 : CollatzResearch.WordTrace tailWord_5059109 prefixEnd_5059109 288639400054127994052343 := by
  unfold tailWord_5059109
  simp only [CollatzResearch.WordTrace]
  refine ⟨184520864228719594873604381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123013909485813063249069587 184520864228719594873604381)
  ·
    refine ⟨69195324085769848077601643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184520864228719594873604381 69195324085769848077601643)
    ·
      refine ⟨103792986128654772116402465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69195324085769848077601643 103792986128654772116402465)
      ·
        refine ⟨77844739596491079087301849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103792986128654772116402465 77844739596491079087301849)
        ·
          refine ⟨58383554697368309315476387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77844739596491079087301849 58383554697368309315476387)
          ·
            refine ⟨87575332046052463973214581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58383554697368309315476387 87575332046052463973214581)
            ·
              refine ⟨8210187379317418497488867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87575332046052463973214581 8210187379317418497488867)
              ·
                refine ⟨12315281068976127746233301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8210187379317418497488867 12315281068976127746233301)
                ·
                  refine ⟨288639400054127994052343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12315281068976127746233301 288639400054127994052343)
                  ·
                    rfl

theorem cell23_5059109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 7].length) (baseStart_5059109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059109 prefixEnd_5059109 := by exact prefixLift 5059109
  have htrace : WordTrace (prefixWord ++ tailWord_5059109) baseStart_5059109 baseEnd_5059109 := by
    simpa [prefixWord, tailWord_5059109, baseEnd_5059109] using wordTrace_append hprefix tailTrace_5059109
  have hstable : (prefixWord ++ tailWord_5059109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059109).length < 2 ^ (prefixWord ++ tailWord_5059109).sum := by decide
  have hdescent : baseEnd_5059109 < baseStart_5059109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059120 : List Nat := [2, 1, 1, 1, 2, 3, 6, 1, 2, 2, 2]
def baseStart_5059120 : Nat := 118140960795 + 5059120 * 2 ^ 59
def prefixEnd_5059120 : Nat := 4983230072969 + 3 ^ 40 * 5059120 * 2
def baseEnd_5059120 : Nat := 2597760248774351403433537

theorem tailTrace_5059120 : CollatzResearch.WordTrace tailWord_5059120 prefixEnd_5059120 2597760248774351403433537 := by
  unfold tailWord_5059120
  simp only [CollatzResearch.WordTrace]
  refine ⟨92260632715839871876127407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123014176954453162501503209 92260632715839871876127407)
  ·
    refine ⟨138390949073759807814191111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92260632715839871876127407 138390949073759807814191111)
    ·
      refine ⟨207586423610639711721286667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138390949073759807814191111 207586423610639711721286667)
      ·
        refine ⟨311379635415959567581930001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207586423610639711721286667 311379635415959567581930001)
        ·
          refine ⟨233534726561969675686447501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311379635415959567581930001 233534726561969675686447501)
          ·
            refine ⟨87575522460738628382417813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 233534726561969675686447501 87575522460738628382417813)
            ·
              refine ⟨4105102615347123205425835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 87575522460738628382417813 4105102615347123205425835)
              ·
                refine ⟨6157653923020684808138753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4105102615347123205425835 6157653923020684808138753)
                ·
                  refine ⟨4618240442265513606104065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6157653923020684808138753 4618240442265513606104065)
                  ·
                    refine ⟨3463680331699135204578049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4618240442265513606104065 3463680331699135204578049)
                    ·
                      refine ⟨2597760248774351403433537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3463680331699135204578049 2597760248774351403433537)
                      ·
                        rfl

theorem cell23_5059120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 2, 2, 2].length) (baseStart_5059120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059120 prefixEnd_5059120 := by exact prefixLift 5059120
  have htrace : WordTrace (prefixWord ++ tailWord_5059120) baseStart_5059120 baseEnd_5059120 := by
    simpa [prefixWord, tailWord_5059120, baseEnd_5059120] using wordTrace_append hprefix tailTrace_5059120
  have hstable : (prefixWord ++ tailWord_5059120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059120).length < 2 ^ (prefixWord ++ tailWord_5059120).sum := by decide
  have hdescent : baseEnd_5059120 < baseStart_5059120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059124 : List Nat := [2, 5, 1, 3, 1, 2, 1, 2, 1, 3, 2]
def baseStart_5059124 : Nat := 118140960795 + 5059124 * 2 ^ 59
def prefixEnd_5059124 : Nat := 4983230072969 + 3 ^ 40 * 5059124 * 2
def baseEnd_5059124 : Nat := 2597762302696969387783519

theorem tailTrace_5059124 : CollatzResearch.WordTrace tailWord_5059124 prefixEnd_5059124 2597762302696969387783519 := by
  unfold tailWord_5059124
  simp only [CollatzResearch.WordTrace]
  refine ⟨92260705661832626217700213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123014274215776834956933617 92260705661832626217700213)
  ·
    refine ⟨8649441155796808707909395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92260705661832626217700213 8649441155796808707909395)
    ·
      refine ⟨12974161733695213061864093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8649441155796808707909395 12974161733695213061864093)
      ·
        refine ⟨4865310650135704898199035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12974161733695213061864093 4865310650135704898199035)
        ·
          refine ⟨7297965975203557347298553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4865310650135704898199035 7297965975203557347298553)
          ·
            refine ⟨5473474481402668010473915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7297965975203557347298553 5473474481402668010473915)
            ·
              refine ⟨8210211722104002015710873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5473474481402668010473915 8210211722104002015710873)
              ·
                refine ⟨6157658791578001511783155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8210211722104002015710873 6157658791578001511783155)
                ·
                  refine ⟨9236488187367002267674733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6157658791578001511783155 9236488187367002267674733)
                  ·
                    refine ⟨3463683070262625850378025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9236488187367002267674733 3463683070262625850378025)
                    ·
                      refine ⟨2597762302696969387783519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3463683070262625850378025 2597762302696969387783519)
                      ·
                        rfl

theorem cell23_5059124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_5059124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059124 prefixEnd_5059124 := by exact prefixLift 5059124
  have htrace : WordTrace (prefixWord ++ tailWord_5059124) baseStart_5059124 baseEnd_5059124 := by
    simpa [prefixWord, tailWord_5059124, baseEnd_5059124] using wordTrace_append hprefix tailTrace_5059124
  have hstable : (prefixWord ++ tailWord_5059124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059124).length < 2 ^ (prefixWord ++ tailWord_5059124).sum := by decide
  have hdescent : baseEnd_5059124 < baseStart_5059124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059156 : List Nat := [2, 4, 1, 1, 1, 3, 2, 2, 2, 5]
def baseStart_5059156 : Nat := 118140960795 + 5059156 * 2 ^ 59
def prefixEnd_5059156 : Nat := 4983230072969 + 3 ^ 40 * 5059156 * 2
def baseEnd_5059156 : Nat := 865926244692637754194457

theorem tailTrace_5059156 : CollatzResearch.WordTrace tailWord_5059156 prefixEnd_5059156 865926244692637754194457 := by
  unfold tailWord_5059156
  simp only [CollatzResearch.WordTrace]
  refine ⟨92261289229774660950282661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123015052306366214600376881 92261289229774660950282661)
  ·
    refine ⟨17298991730582748928177999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92261289229774660950282661 17298991730582748928177999)
    ·
      refine ⟨25948487595874123392266999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17298991730582748928177999 25948487595874123392266999)
      ·
        refine ⟨38922731393811185088400499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25948487595874123392266999 38922731393811185088400499)
        ·
          refine ⟨58384097090716777632600749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38922731393811185088400499 58384097090716777632600749)
          ·
            refine ⟨21894036409018791612225281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58384097090716777632600749 21894036409018791612225281)
            ·
              refine ⟨16420527306764093709168961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21894036409018791612225281 16420527306764093709168961)
              ·
                refine ⟨12315395480073070281876721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16420527306764093709168961 12315395480073070281876721)
                ·
                  refine ⟨9236546610054802711407541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12315395480073070281876721 9236546610054802711407541)
                  ·
                    refine ⟨865926244692637754194457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9236546610054802711407541 865926244692637754194457)
                    ·
                      rfl

theorem cell23_5059156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_5059156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059156 prefixEnd_5059156 := by exact prefixLift 5059156
  have htrace : WordTrace (prefixWord ++ tailWord_5059156) baseStart_5059156 baseEnd_5059156 := by
    simpa [prefixWord, tailWord_5059156, baseEnd_5059156] using wordTrace_append hprefix tailTrace_5059156
  have hstable : (prefixWord ++ tailWord_5059156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059156).length < 2 ^ (prefixWord ++ tailWord_5059156).sum := by decide
  have hdescent : baseEnd_5059156 < baseStart_5059156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059170 : List Nat := [3, 3, 2, 3, 1, 1, 1, 1, 2, 3, 3]
def baseStart_5059170 : Nat := 118140960795 + 5059170 * 2 ^ 59
def prefixEnd_5059170 : Nat := 4983230072969 + 3 ^ 40 * 5059170 * 2
def baseEnd_5059170 : Nat := 2597785922807076207808307

theorem tailTrace_5059170 : CollatzResearch.WordTrace tailWord_5059170 prefixEnd_5059170 2597785922807076207808307 := by
  unfold tailWord_5059170
  simp only [CollatzResearch.WordTrace]
  refine ⟨46130772270374650572893741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123015392720999068194383309 46130772270374650572893741)
  ·
    refine ⟨17299039601390493964835153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46130772270374650572893741 17299039601390493964835153)
    ·
      refine ⟨12974279701042870473626365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17299039601390493964835153 12974279701042870473626365)
      ·
        refine ⟨4865354887891076427609887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12974279701042870473626365 4865354887891076427609887)
        ·
          refine ⟨7298032331836614641414831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4865354887891076427609887 7298032331836614641414831)
          ·
            refine ⟨10947048497754921962122247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7298032331836614641414831 10947048497754921962122247)
            ·
              refine ⟨16420572746632382943183371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10947048497754921962122247 16420572746632382943183371)
              ·
                refine ⟨24630859119948574414775057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16420572746632382943183371 24630859119948574414775057)
                ·
                  refine ⟨18473144339961430811081293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24630859119948574414775057 18473144339961430811081293)
                  ·
                    refine ⟨6927429127485536554155485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18473144339961430811081293 6927429127485536554155485)
                    ·
                      refine ⟨2597785922807076207808307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6927429127485536554155485 2597785922807076207808307)
                      ·
                        rfl

theorem cell23_5059170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_5059170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059170 prefixEnd_5059170 := by exact prefixLift 5059170
  have htrace : WordTrace (prefixWord ++ tailWord_5059170) baseStart_5059170 baseEnd_5059170 := by
    simpa [prefixWord, tailWord_5059170, baseEnd_5059170] using wordTrace_append hprefix tailTrace_5059170
  have hstable : (prefixWord ++ tailWord_5059170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059170).length < 2 ^ (prefixWord ++ tailWord_5059170).sum := by decide
  have hdescent : baseEnd_5059170 < baseStart_5059170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059190 : List Nat := [5, 1, 1, 2, 3, 2, 1, 1, 2, 5]
def baseStart_5059190 : Nat := 118140960795 + 5059190 * 2 ^ 59
def prefixEnd_5059190 : Nat := 4983230072969 + 3 ^ 40 * 5059190 * 2
def baseEnd_5059190 : Nat := 865932064140055376519405

theorem tailTrace_5059190 : CollatzResearch.WordTrace tailWord_5059190 prefixEnd_5059190 865932064140055376519405 := by
  unfold tailWord_5059190
  simp only [CollatzResearch.WordTrace]
  refine ⟨11532738658839134106706439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123015879027617430471535349 11532738658839134106706439)
  ·
    refine ⟨17299107988258701160059659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11532738658839134106706439 17299107988258701160059659)
    ·
      refine ⟨25948661982388051740089489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17299107988258701160059659 25948661982388051740089489)
      ·
        refine ⟨19461496486791038805067117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25948661982388051740089489 19461496486791038805067117)
        ·
          refine ⟨7298061182546639551900169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19461496486791038805067117 7298061182546639551900169)
          ·
            refine ⟨5473545886909979663925127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7298061182546639551900169 5473545886909979663925127)
            ·
              refine ⟨8210318830364969495887691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5473545886909979663925127 8210318830364969495887691)
              ·
                refine ⟨12315478245547454243831537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8210318830364969495887691 12315478245547454243831537)
                ·
                  refine ⟨9236608684160590682873653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12315478245547454243831537 9236608684160590682873653)
                  ·
                    refine ⟨865932064140055376519405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9236608684160590682873653 865932064140055376519405)
                    ·
                      rfl

theorem cell23_5059190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_5059190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059190 prefixEnd_5059190 := by exact prefixLift 5059190
  have htrace : WordTrace (prefixWord ++ tailWord_5059190) baseStart_5059190 baseEnd_5059190 := by
    simpa [prefixWord, tailWord_5059190, baseEnd_5059190] using wordTrace_append hprefix tailTrace_5059190
  have hstable : (prefixWord ++ tailWord_5059190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059190).length < 2 ^ (prefixWord ++ tailWord_5059190).sum := by decide
  have hdescent : baseEnd_5059190 < baseStart_5059190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059193 : List Nat := [1, 2, 1, 3, 3, 4, 1, 1, 2, 1, 4]
def baseStart_5059193 : Nat := 118140960795 + 5059193 * 2 ^ 59
def prefixEnd_5059193 : Nat := 4983230072969 + 3 ^ 40 * 5059193 * 2
def baseEnd_5059193 : Nat := 2597797732862129617820701

theorem tailTrace_5059193 : CollatzResearch.WordTrace tailWord_5059193 prefixEnd_5059193 2597797732862129617820701 := by
  unfold tailWord_5059193
  simp only [CollatzResearch.WordTrace]
  refine ⟨184523927960415277219662233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123015951973610184813108155 184523927960415277219662233)
  ·
    refine ⟨138392945970311457914746675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184523927960415277219662233 138392945970311457914746675)
    ·
      refine ⟨207589418955467186872120013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138392945970311457914746675 207589418955467186872120013)
      ·
        refine ⟨77846032108300195077045005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207589418955467186872120013 77846032108300195077045005)
        ·
          refine ⟨29192262040612573153891877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77846032108300195077045005 29192262040612573153891877)
          ·
            refine ⟨5473549132614857466354727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29192262040612573153891877 5473549132614857466354727)
            ·
              refine ⟨8210323698922286199532091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5473549132614857466354727 8210323698922286199532091)
              ·
                refine ⟨12315485548383429299298137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8210323698922286199532091 12315485548383429299298137)
                ·
                  refine ⟨9236614161287571974473603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12315485548383429299298137 9236614161287571974473603)
                  ·
                    refine ⟨13854921241931357961710405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9236614161287571974473603 13854921241931357961710405)
                    ·
                      refine ⟨2597797732862129617820701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13854921241931357961710405 2597797732862129617820701)
                      ·
                        rfl

theorem cell23_5059193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_5059193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059193 prefixEnd_5059193 := by exact prefixLift 5059193
  have htrace : WordTrace (prefixWord ++ tailWord_5059193) baseStart_5059193 baseEnd_5059193 := by
    simpa [prefixWord, tailWord_5059193, baseEnd_5059193] using wordTrace_append hprefix tailTrace_5059193
  have hstable : (prefixWord ++ tailWord_5059193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059193).length < 2 ^ (prefixWord ++ tailWord_5059193).sum := by decide
  have hdescent : baseEnd_5059193 < baseStart_5059193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059203 : List Nat := [1, 1, 1, 3, 3, 1, 3, 5, 1, 4]
def baseStart_5059203 : Nat := 118140960795 + 5059203 * 2 ^ 59
def prefixEnd_5059203 : Nat := 4983230072969 + 3 ^ 40 * 5059203 * 2
def baseEnd_5059203 : Nat := 865934289222891526231885

theorem tailTrace_5059203 : CollatzResearch.WordTrace tailWord_5059203 prefixEnd_5059203 865934289222891526231885 := by
  unfold tailWord_5059203
  simp only [CollatzResearch.WordTrace]
  refine ⟨184524292690379048927526263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123016195126919365951684175 184524292690379048927526263)
  ·
    refine ⟨276786439035568573391289395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184524292690379048927526263 276786439035568573391289395)
    ·
      refine ⟨415179658553352860086934093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276786439035568573391289395 415179658553352860086934093)
      ·
        refine ⟨155692371957507322532600285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 415179658553352860086934093 155692371957507322532600285)
        ·
          refine ⟨58384639484065245949725107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155692371957507322532600285 58384639484065245949725107)
          ·
            refine ⟨87576959226097868924587661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58384639484065245949725107 87576959226097868924587661)
            ·
              refine ⟨32841359709786700846720373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87576959226097868924587661 32841359709786700846720373)
              ·
                refine ⟨3078877472792503204380035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32841359709786700846720373 3078877472792503204380035)
                ·
                  refine ⟨4618316209188754806570053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3078877472792503204380035 4618316209188754806570053)
                  ·
                    refine ⟨865934289222891526231885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4618316209188754806570053 865934289222891526231885)
                    ·
                      rfl

theorem cell23_5059203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 5, 1, 4].length) (baseStart_5059203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059203 prefixEnd_5059203 := by exact prefixLift 5059203
  have htrace : WordTrace (prefixWord ++ tailWord_5059203) baseStart_5059203 baseEnd_5059203 := by
    simpa [prefixWord, tailWord_5059203, baseEnd_5059203] using wordTrace_append hprefix tailTrace_5059203
  have hstable : (prefixWord ++ tailWord_5059203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059203).length < 2 ^ (prefixWord ++ tailWord_5059203).sum := by decide
  have hdescent : baseEnd_5059203 < baseStart_5059203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059220 : List Nat := [2, 4, 2, 2, 1, 2, 2, 1, 3, 4]
def baseStart_5059220 : Nat := 118140960795 + 5059220 * 2 ^ 59
def prefixEnd_5059220 : Nat := 4983230072969 + 3 ^ 40 * 5059220 * 2
def baseEnd_5059220 : Nat := 865937198946600337394359

theorem tailTrace_5059220 : CollatzResearch.WordTrace tailWord_5059220 prefixEnd_5059220 865937198946600337394359 := by
  unfold tailWord_5059220
  simp only [CollatzResearch.WordTrace]
  refine ⟨92262456365658730415447557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123016608487544973887263409 92262456365658730415447557)
  ·
    refine ⟨17299210568561011952896417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92262456365658730415447557 17299210568561011952896417)
    ·
      refine ⟨12974407926420758964672313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17299210568561011952896417 12974407926420758964672313)
      ·
        refine ⟨9730805944815569223504235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12974407926420758964672313 9730805944815569223504235)
        ·
          refine ⟨14596208917223353835256353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9730805944815569223504235 14596208917223353835256353)
          ·
            refine ⟨10947156687917515376442265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14596208917223353835256353 10947156687917515376442265)
            ·
              refine ⟨8210367515938136532331699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10947156687917515376442265 8210367515938136532331699)
              ·
                refine ⟨12315551273907204798497549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8210367515938136532331699 12315551273907204798497549)
                ·
                  refine ⟨4618331727715201799436581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12315551273907204798497549 4618331727715201799436581)
                  ·
                    refine ⟨865937198946600337394359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4618331727715201799436581 865937198946600337394359)
                    ·
                      rfl

theorem cell23_5059220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_5059220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059220 prefixEnd_5059220 := by exact prefixLift 5059220
  have htrace : WordTrace (prefixWord ++ tailWord_5059220) baseStart_5059220 baseEnd_5059220 := by
    simpa [prefixWord, tailWord_5059220, baseEnd_5059220] using wordTrace_append hprefix tailTrace_5059220
  have hstable : (prefixWord ++ tailWord_5059220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059220).length < 2 ^ (prefixWord ++ tailWord_5059220).sum := by decide
  have hdescent : baseEnd_5059220 < baseStart_5059220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059296 : List Nat := [2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 4]
def baseStart_5059296 : Nat := 118140960795 + 5059296 * 2 ^ 59
def prefixEnd_5059296 : Nat := 4983230072969 + 3 ^ 40 * 5059296 * 2
def baseEnd_5059296 : Nat := 2597850621369542714832727

theorem tailTrace_5059296 : CollatzResearch.WordTrace tailWord_5059296 prefixEnd_5059296 2597850621369542714832727 := by
  unfold tailWord_5059296
  simp only [CollatzResearch.WordTrace]
  refine ⟨92263842339521062905330871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123018456452694750540441161 92263842339521062905330871)
  ·
    refine ⟨138395763509281594357996307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92263842339521062905330871 138395763509281594357996307)
    ·
      refine ⟨207593645263922391536994461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138395763509281594357996307 207593645263922391536994461)
      ·
        refine ⟨77847616973970896826372923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207593645263922391536994461 77847616973970896826372923)
        ·
          refine ⟨116771425460956345239559385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77847616973970896826372923 116771425460956345239559385)
          ·
            refine ⟨87578569095717258929669539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116771425460956345239559385 87578569095717258929669539)
            ·
              refine ⟨131367853643575888394504309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87578569095717258929669539 131367853643575888394504309)
              ·
                refine ⟨12315736279085239536984779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 131367853643575888394504309 12315736279085239536984779)
                ·
                  refine ⟨18473604418627859305477169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12315736279085239536984779 18473604418627859305477169)
                  ·
                    refine ⟨13855203313970894479107877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18473604418627859305477169 13855203313970894479107877)
                    ·
                      refine ⟨2597850621369542714832727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13855203313970894479107877 2597850621369542714832727)
                      ·
                        rfl

theorem cell23_5059296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_5059296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059296 prefixEnd_5059296 := by exact prefixLift 5059296
  have htrace : WordTrace (prefixWord ++ tailWord_5059296) baseStart_5059296 baseEnd_5059296 := by
    simpa [prefixWord, tailWord_5059296, baseEnd_5059296] using wordTrace_append hprefix tailTrace_5059296
  have hstable : (prefixWord ++ tailWord_5059296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059296).length < 2 ^ (prefixWord ++ tailWord_5059296).sum := by decide
  have hdescent : baseEnd_5059296 < baseStart_5059296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059300 : List Nat := [2, 3, 1, 1, 1, 6, 1, 2, 1, 1, 4]
def baseStart_5059300 : Nat := 118140960795 + 5059300 * 2 ^ 59
def prefixEnd_5059300 : Nat := 4983230072969 + 3 ^ 40 * 5059300 * 2
def baseEnd_5059300 : Nat := 2597852675292160699182709

theorem tailTrace_5059300 : CollatzResearch.WordTrace tailWord_5059300 prefixEnd_5059300 2597852675292160699182709 := by
  unfold tailWord_5059300
  simp only [CollatzResearch.WordTrace]
  refine ⟨92263915285513817246903677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123018553714018422995871569 92263915285513817246903677)
  ·
    refine ⟨34598968232067681467588879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92263915285513817246903677 34598968232067681467588879)
    ·
      refine ⟨51898452348101522201383319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34598968232067681467588879 51898452348101522201383319)
      ·
        refine ⟨77847678522152283302074979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51898452348101522201383319 77847678522152283302074979)
        ·
          refine ⟨116771517783228424953112469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77847678522152283302074979 116771517783228424953112469)
          ·
            refine ⟨5473664896088832419677147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 116771517783228424953112469 5473664896088832419677147)
            ·
              refine ⟨8210497344133248629515721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5473664896088832419677147 8210497344133248629515721)
              ·
                refine ⟨6157873008099936472136791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8210497344133248629515721 6157873008099936472136791)
                ·
                  refine ⟨9236809512149904708205187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6157873008099936472136791 9236809512149904708205187)
                  ·
                    refine ⟨13855214268224857062307781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9236809512149904708205187 13855214268224857062307781)
                    ·
                      refine ⟨2597852675292160699182709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13855214268224857062307781 2597852675292160699182709)
                      ·
                        rfl

theorem cell23_5059300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_5059300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059300 prefixEnd_5059300 := by exact prefixLift 5059300
  have htrace : WordTrace (prefixWord ++ tailWord_5059300) baseStart_5059300 baseEnd_5059300 := by
    simpa [prefixWord, tailWord_5059300, baseEnd_5059300] using wordTrace_append hprefix tailTrace_5059300
  have hstable : (prefixWord ++ tailWord_5059300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059300).length < 2 ^ (prefixWord ++ tailWord_5059300).sum := by decide
  have hdescent : baseEnd_5059300 < baseStart_5059300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059320 : List Nat := [2, 1, 2, 1, 1, 2, 7, 1, 1, 2, 3]
def baseStart_5059320 : Nat := 118140960795 + 5059320 * 2 ^ 59
def prefixEnd_5059320 : Nat := 4983230072969 + 3 ^ 40 * 5059320 * 2
def baseEnd_5059320 : Nat := 2597862944905250620932617

theorem tailTrace_5059320 : CollatzResearch.WordTrace tailWord_5059320 prefixEnd_5059320 2597862944905250620932617 := by
  unfold tailWord_5059320
  simp only [CollatzResearch.WordTrace]
  refine ⟨92264280015477588954767707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123019040020636785273023609 92264280015477588954767707)
  ·
    refine ⟨138396420023216383432151561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92264280015477588954767707 138396420023216383432151561)
    ·
      refine ⟨103797315017412287574113671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138396420023216383432151561 103797315017412287574113671)
      ·
        refine ⟨155695972526118431361170507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103797315017412287574113671 155695972526118431361170507)
        ·
          refine ⟨233543958789177647041755761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155695972526118431361170507 233543958789177647041755761)
          ·
            refine ⟨175157969091883235281316821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233543958789177647041755761 175157969091883235281316821)
            ·
              refine ⟨4105264900591013326905863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 175157969091883235281316821 4105264900591013326905863)
              ·
                refine ⟨6157897350886519990358795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4105264900591013326905863 6157897350886519990358795)
                ·
                  refine ⟨9236846026329779985538193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6157897350886519990358795 9236846026329779985538193)
                  ·
                    refine ⟨6927634519747334989153645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9236846026329779985538193 6927634519747334989153645)
                    ·
                      refine ⟨2597862944905250620932617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6927634519747334989153645 2597862944905250620932617)
                      ·
                        rfl

theorem cell23_5059320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 1, 2, 3].length) (baseStart_5059320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059320 prefixEnd_5059320 := by exact prefixLift 5059320
  have htrace : WordTrace (prefixWord ++ tailWord_5059320) baseStart_5059320 baseEnd_5059320 := by
    simpa [prefixWord, tailWord_5059320, baseEnd_5059320] using wordTrace_append hprefix tailTrace_5059320
  have hstable : (prefixWord ++ tailWord_5059320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059320).length < 2 ^ (prefixWord ++ tailWord_5059320).sum := by decide
  have hdescent : baseEnd_5059320 < baseStart_5059320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059333 : List Nat := [1, 3, 1, 1, 2, 1, 1, 5, 4, 1, 3]
def baseStart_5059333 : Nat := 118140960795 + 5059333 * 2 ^ 59
def prefixEnd_5059333 : Nat := 4983230072969 + 3 ^ 40 * 5059333 * 2
def baseEnd_5059333 : Nat := 2597869620153759070070057

theorem tailTrace_5059333 : CollatzResearch.WordTrace tailWord_5059333 prefixEnd_5059333 2597869620153759070070057 := by
  unfold tailWord_5059333
  simp only [CollatzResearch.WordTrace]
  refine ⟨184529034179908081129758653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123019356119938720753172435 184529034179908081129758653)
  ·
    refine ⟨69198387817465530423659495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184529034179908081129758653 69198387817465530423659495)
    ·
      refine ⟨103797581726198295635489243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69198387817465530423659495 103797581726198295635489243)
      ·
        refine ⟨155696372589297443453233865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103797581726198295635489243 155696372589297443453233865)
        ·
          refine ⟨116772279441973082589925399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155696372589297443453233865 116772279441973082589925399)
          ·
            refine ⟨175158419162959623884888099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116772279441973082589925399 175158419162959623884888099)
            ·
              refine ⟨262737628744439435827332149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175158419162959623884888099 262737628744439435827332149)
              ·
                refine ⟨24631652694791197108812389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 262737628744439435827332149 24631652694791197108812389)
                ·
                  refine ⟨4618434880273349457902323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24631652694791197108812389 4618434880273349457902323)
                  ·
                    refine ⟨6927652320410024186853485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4618434880273349457902323 6927652320410024186853485)
                    ·
                      refine ⟨2597869620153759070070057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6927652320410024186853485 2597869620153759070070057)
                      ·
                        rfl

theorem cell23_5059333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 4, 1, 3].length) (baseStart_5059333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059333 prefixEnd_5059333 := by exact prefixLift 5059333
  have htrace : WordTrace (prefixWord ++ tailWord_5059333) baseStart_5059333 baseEnd_5059333 := by
    simpa [prefixWord, tailWord_5059333, baseEnd_5059333] using wordTrace_append hprefix tailTrace_5059333
  have hstable : (prefixWord ++ tailWord_5059333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059333).length < 2 ^ (prefixWord ++ tailWord_5059333).sum := by decide
  have hdescent : baseEnd_5059333 < baseStart_5059333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059336 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 2, 7]
def baseStart_5059336 : Nat := 118140960795 + 5059336 * 2 ^ 59
def prefixEnd_5059336 : Nat := 4983230072969 + 3 ^ 40 * 5059336 * 2
def baseEnd_5059336 : Nat := 865957053531907519444181

theorem tailTrace_5059336 : CollatzResearch.WordTrace tailWord_5059336 prefixEnd_5059336 865957053531907519444181 := by
  unfold tailWord_5059336
  simp only [CollatzResearch.WordTrace]
  refine ⟨92264571799448606321058931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123019429065931475094745241 92264571799448606321058931)
  ·
    refine ⟨138396857699172909481588397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92264571799448606321058931 138396857699172909481588397)
    ·
      refine ⟨51898821637189841055595649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138396857699172909481588397 51898821637189841055595649)
      ·
        refine ⟨38924116227892380791696737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51898821637189841055595649 38924116227892380791696737)
        ·
          refine ⟨29193087170919285593772553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38924116227892380791696737 29193087170919285593772553)
          ·
            refine ⟨21894815378189464195329415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29193087170919285593772553 21894815378189464195329415)
            ·
              refine ⟨32842223067284196292994123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21894815378189464195329415 32842223067284196292994123)
              ·
                refine ⟨49263334600926294439491185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32842223067284196292994123 49263334600926294439491185)
                ·
                  refine ⟨36947500950694720829618389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49263334600926294439491185 36947500950694720829618389)
                  ·
                    refine ⟨865957053531907519444181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36947500950694720829618389 865957053531907519444181)
                    ·
                      rfl

theorem cell23_5059336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_5059336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059336 prefixEnd_5059336 := by exact prefixLift 5059336
  have htrace : WordTrace (prefixWord ++ tailWord_5059336) baseStart_5059336 baseEnd_5059336 := by
    simpa [prefixWord, tailWord_5059336, baseEnd_5059336] using wordTrace_append hprefix tailTrace_5059336
  have hstable : (prefixWord ++ tailWord_5059336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059336).length < 2 ^ (prefixWord ++ tailWord_5059336).sum := by decide
  have hdescent : baseEnd_5059336 < baseStart_5059336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059343 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 5, 3, 2]
def baseStart_5059343 : Nat := 118140960795 + 5059343 * 2 ^ 59
def prefixEnd_5059343 : Nat := 4983230072969 + 3 ^ 40 * 5059343 * 2
def baseEnd_5059343 : Nat := 2597874754960304030945011

theorem tailTrace_5059343 : CollatzResearch.WordTrace tailWord_5059343 prefixEnd_5059343 2597874754960304030945011 := by
  unfold tailWord_5059343
  simp only [CollatzResearch.WordTrace]
  refine ⟨184529398909871852837622683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123019599273247901891748455 184529398909871852837622683)
  ·
    refine ⟨276794098364807779256434025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184529398909871852837622683 276794098364807779256434025)
    ·
      refine ⟨207595573773605834442325519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276794098364807779256434025 207595573773605834442325519)
      ·
        refine ⟨311393360660408751663488279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207595573773605834442325519 311393360660408751663488279)
        ·
          refine ⟨467090040990613127495232419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311393360660408751663488279 467090040990613127495232419)
          ·
            refine ⟨700635061485919691242848629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467090040990613127495232419 700635061485919691242848629)
            ·
              refine ⟨65684537014304971054017059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 700635061485919691242848629 65684537014304971054017059)
              ·
                refine ⟨98526805521457456581025589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65684537014304971054017059 98526805521457456581025589)
                ·
                  refine ⟨9236888017636636554471149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98526805521457456581025589 9236888017636636554471149)
                  ·
                    refine ⟨3463833006613738707926681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9236888017636636554471149 3463833006613738707926681)
                    ·
                      refine ⟨2597874754960304030945011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3463833006613738707926681 2597874754960304030945011)
                      ·
                        rfl

theorem cell23_5059343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 3, 2].length) (baseStart_5059343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059343 prefixEnd_5059343 := by exact prefixLift 5059343
  have htrace : WordTrace (prefixWord ++ tailWord_5059343) baseStart_5059343 baseEnd_5059343 := by
    simpa [prefixWord, tailWord_5059343, baseEnd_5059343] using wordTrace_append hprefix tailTrace_5059343
  have hstable : (prefixWord ++ tailWord_5059343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059343).length < 2 ^ (prefixWord ++ tailWord_5059343).sum := by decide
  have hdescent : baseEnd_5059343 < baseStart_5059343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059360 : List Nat := [2, 1, 1, 5, 1, 2, 2, 1, 3, 3, 2]
def baseStart_5059360 : Nat := 118140960795 + 5059360 * 2 ^ 59
def prefixEnd_5059360 : Nat := 4983230072969 + 3 ^ 40 * 5059360 * 2
def baseEnd_5059360 : Nat := 2597883484131430464432433

theorem tailTrace_5059360 : CollatzResearch.WordTrace tailWord_5059360 prefixEnd_5059360 2597883484131430464432433 := by
  unfold tailWord_5059360
  simp only [CollatzResearch.WordTrace]
  refine ⟨92265009475405132370495767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123020012633873509827327689 92265009475405132370495767)
  ·
    refine ⟨138397514213107698555743651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92265009475405132370495767 138397514213107698555743651)
    ·
      refine ⟨207596271319661547833615477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138397514213107698555743651 207596271319661547833615477)
      ·
        refine ⟨19462150436218270109401451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 207596271319661547833615477 19462150436218270109401451)
        ·
          refine ⟨29193225654327405164102177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19462150436218270109401451 29193225654327405164102177)
          ·
            refine ⟨21894919240745553873076633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29193225654327405164102177 21894919240745553873076633)
            ·
              refine ⟨16421189430559165404807475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21894919240745553873076633 16421189430559165404807475)
              ·
                refine ⟨24631784145838748107211213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16421189430559165404807475 24631784145838748107211213)
                ·
                  refine ⟨9236919054689530540204205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24631784145838748107211213 9236919054689530540204205)
                  ·
                    refine ⟨3463844645508573952576577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9236919054689530540204205 3463844645508573952576577)
                    ·
                      refine ⟨2597883484131430464432433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3463844645508573952576577 2597883484131430464432433)
                      ·
                        rfl

theorem cell23_5059360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_5059360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059360 prefixEnd_5059360 := by exact prefixLift 5059360
  have htrace : WordTrace (prefixWord ++ tailWord_5059360) baseStart_5059360 baseEnd_5059360 := by
    simpa [prefixWord, tailWord_5059360, baseEnd_5059360] using wordTrace_append hprefix tailTrace_5059360
  have hstable : (prefixWord ++ tailWord_5059360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059360).length < 2 ^ (prefixWord ++ tailWord_5059360).sum := by decide
  have hdescent : baseEnd_5059360 < baseStart_5059360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059376 : List Nat := [2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 5]
def baseStart_5059376 : Nat := 118140960795 + 5059376 * 2 ^ 59
def prefixEnd_5059376 : Nat := 4983230072969 + 3 ^ 40 * 5059376 * 2
def baseEnd_5059376 : Nat := 2597891699821902401832359

theorem tailTrace_5059376 : CollatzResearch.WordTrace tailWord_5059376 prefixEnd_5059376 2597891699821902401832359 := by
  unfold tailWord_5059376
  simp only [CollatzResearch.WordTrace]
  refine ⟨92265301259376149736786991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123020401679168199649049321 92265301259376149736786991)
  ·
    refine ⟨138397951889064224605180487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92265301259376149736786991 138397951889064224605180487)
    ·
      refine ⟨207596927833596336907770731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138397951889064224605180487 207596927833596336907770731)
      ·
        refine ⟨311395391750394505361656097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207596927833596336907770731 311395391750394505361656097)
        ·
          refine ⟨233546543812795879021242073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311395391750394505361656097 233546543812795879021242073)
          ·
            refine ⟨175159907859596909265931555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233546543812795879021242073 175159907859596909265931555)
            ·
              refine ⟨262739861789395363898897333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175159907859596909265931555 262739861789395363898897333)
              ·
                refine ⟨24631862042755815365521625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 262739861789395363898897333 24631862042755815365521625)
                ·
                  refine ⟨18473896532066861524141219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24631862042755815365521625 18473896532066861524141219)
                  ·
                    refine ⟨27710844798100292286211829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18473896532066861524141219 27710844798100292286211829)
                    ·
                      refine ⟨2597891699821902401832359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27710844798100292286211829 2597891699821902401832359)
                      ·
                        rfl

theorem cell23_5059376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 5].length) (baseStart_5059376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059376 prefixEnd_5059376 := by exact prefixLift 5059376
  have htrace : WordTrace (prefixWord ++ tailWord_5059376) baseStart_5059376 baseEnd_5059376 := by
    simpa [prefixWord, tailWord_5059376, baseEnd_5059376] using wordTrace_append hprefix tailTrace_5059376
  have hstable : (prefixWord ++ tailWord_5059376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059376).length < 2 ^ (prefixWord ++ tailWord_5059376).sum := by decide
  have hdescent : baseEnd_5059376 < baseStart_5059376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059406 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9]
def baseStart_5059406 : Nat := 118140960795 + 5059406 * 2 ^ 59
def prefixEnd_5059406 : Nat := 4983230072969 + 3 ^ 40 * 5059406 * 2
def baseEnd_5059406 : Nat := 2597907104241537284457221

theorem tailTrace_5059406 : CollatzResearch.WordTrace tailWord_5059406 prefixEnd_5059406 2597907104241537284457221 := by
  unfold tailWord_5059406
  simp only [CollatzResearch.WordTrace]
  refine ⟨23066462088580451824645759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123021131139095743064777381 23066462088580451824645759)
  ·
    refine ⟨34599693132870677736968639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23066462088580451824645759 34599693132870677736968639)
    ·
      refine ⟨51899539699306016605452959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34599693132870677736968639 51899539699306016605452959)
      ·
        refine ⟨77849309548959024908179439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51899539699306016605452959 77849309548959024908179439)
        ·
          refine ⟨116773964323438537362269159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77849309548959024908179439 116773964323438537362269159)
          ·
            refine ⟨175160946485157806043403739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116773964323438537362269159 175160946485157806043403739)
            ·
              refine ⟨262741419727736709065105609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175160946485157806043403739 262741419727736709065105609)
              ·
                refine ⟨197056064795802531798829207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262741419727736709065105609 197056064795802531798829207)
                ·
                  refine ⟨295584097193703797698243811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197056064795802531798829207 295584097193703797698243811)
                  ·
                    refine ⟨443376145790555696547365717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 295584097193703797698243811 443376145790555696547365717)
                    ·
                      refine ⟨2597907104241537284457221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 443376145790555696547365717 2597907104241537284457221)
                      ·
                        rfl

theorem cell23_5059406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_5059406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059406 prefixEnd_5059406 := by exact prefixLift 5059406
  have htrace : WordTrace (prefixWord ++ tailWord_5059406) baseStart_5059406 baseEnd_5059406 := by
    simpa [prefixWord, tailWord_5059406, baseEnd_5059406] using wordTrace_append hprefix tailTrace_5059406
  have hstable : (prefixWord ++ tailWord_5059406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059406).length < 2 ^ (prefixWord ++ tailWord_5059406).sum := by decide
  have hdescent : baseEnd_5059406 < baseStart_5059406 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059433 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 3, 7, 2]
def baseStart_5059433 : Nat := 118140960795 + 5059433 * 2 ^ 59
def prefixEnd_5059433 : Nat := 4983230072969 + 3 ^ 40 * 5059433 * 2
def baseEnd_5059433 : Nat := 2597920968219208678819597

theorem tailTrace_5059433 : CollatzResearch.WordTrace tailWord_5059433 prefixEnd_5059433 2597920968219208678819597 := by
  unfold tailWord_5059433
  simp only [CollatzResearch.WordTrace]
  refine ⟨184532681479545798208398953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123021787653030532138932635 184532681479545798208398953)
  ·
    refine ⟨138399511109659348656299215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184532681479545798208398953 138399511109659348656299215)
    ·
      refine ⟨207599266664489022984448823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138399511109659348656299215 207599266664489022984448823)
      ·
        refine ⟨311398899996733534476673235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207599266664489022984448823 311398899996733534476673235)
        ·
          refine ⟨467098349995100301715009853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311398899996733534476673235 467098349995100301715009853)
          ·
            refine ⟨175161881248162613143128695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 467098349995100301715009853 175161881248162613143128695)
            ·
              refine ⟨262742821872243919714693043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175161881248162613143128695 262742821872243919714693043)
              ·
                refine ⟨394114232808365879572039565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262742821872243919714693043 394114232808365879572039565)
                ·
                  refine ⟨147792837303137204839514837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 394114232808365879572039565 147792837303137204839514837)
                  ·
                    refine ⟨3463894624292278238426129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 147792837303137204839514837 3463894624292278238426129)
                    ·
                      refine ⟨2597920968219208678819597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3463894624292278238426129 2597920968219208678819597)
                      ·
                        rfl

theorem cell23_5059433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 7, 2].length) (baseStart_5059433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059433 prefixEnd_5059433 := by exact prefixLift 5059433
  have htrace : WordTrace (prefixWord ++ tailWord_5059433) baseStart_5059433 baseEnd_5059433 := by
    simpa [prefixWord, tailWord_5059433, baseEnd_5059433] using wordTrace_append hprefix tailTrace_5059433
  have hstable : (prefixWord ++ tailWord_5059433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059433).length < 2 ^ (prefixWord ++ tailWord_5059433).sum := by decide
  have hdescent : baseEnd_5059433 < baseStart_5059433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059456 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 2, 8]
def baseStart_5059456 : Nat := 118140960795 + 5059456 * 2 ^ 59
def prefixEnd_5059456 : Nat := 4983230072969 + 3 ^ 40 * 5059456 * 2
def baseEnd_5059456 : Nat := 865977592758087362943997

theorem tailTrace_5059456 : CollatzResearch.WordTrace tailWord_5059456 prefixEnd_5059456 865977592758087362943997 := by
  unfold tailWord_5059456
  simp only [CollatzResearch.WordTrace]
  refine ⟨92266760179231236568243111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123022346905641648757657481 92266760179231236568243111)
  ·
    refine ⟨138400140268846854852364667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92266760179231236568243111 138400140268846854852364667)
    ·
      refine ⟨207600210403270282278547001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138400140268846854852364667 207600210403270282278547001)
      ·
        refine ⟨155700157802452711708910251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207600210403270282278547001 155700157802452711708910251)
        ·
          refine ⟨233550236703679067563365377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155700157802452711708910251 233550236703679067563365377)
          ·
            refine ⟨175162677527759300672524033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233550236703679067563365377 175162677527759300672524033)
            ·
              refine ⟨131372008145819475504393025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175162677527759300672524033 131372008145819475504393025)
              ·
                refine ⟨98529006109364606628294769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131372008145819475504393025 98529006109364606628294769)
                ·
                  refine ⟨73896754582023454971221077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98529006109364606628294769 73896754582023454971221077)
                  ·
                    refine ⟨865977592758087362943997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73896754582023454971221077 865977592758087362943997)
                    ·
                      rfl

theorem cell23_5059456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 8].length) (baseStart_5059456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059456 prefixEnd_5059456 := by exact prefixLift 5059456
  have htrace : WordTrace (prefixWord ++ tailWord_5059456) baseStart_5059456 baseEnd_5059456 := by
    simpa [prefixWord, tailWord_5059456, baseEnd_5059456] using wordTrace_append hprefix tailTrace_5059456
  have hstable : (prefixWord ++ tailWord_5059456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059456).length < 2 ^ (prefixWord ++ tailWord_5059456).sum := by decide
  have hdescent : baseEnd_5059456 < baseStart_5059456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059458 : List Nat := [3, 4, 2, 2, 1, 1, 1, 3, 2, 2, 2]
def baseStart_5059458 : Nat := 118140960795 + 5059458 * 2 ^ 59
def prefixEnd_5059458 : Nat := 4983230072969 + 3 ^ 40 * 5059458 * 2
def baseEnd_5059458 : Nat := 2597933805235571081006983

theorem tailTrace_5059458 : CollatzResearch.WordTrace tailWord_5059458 prefixEnd_5059458 2597933805235571081006983 := by
  unfold tailWord_5059458
  simp only [CollatzResearch.WordTrace]
  refine ⟨46133398326113806869514757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123022395536303484985372685 46133398326113806869514757)
  ·
    refine ⟨8650012186146338788034017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46133398326113806869514757 8650012186146338788034017)
    ·
      refine ⟨6487509139609754091025513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8650012186146338788034017 6487509139609754091025513)
      ·
        refine ⟨4865631854707315568269135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6487509139609754091025513 4865631854707315568269135)
        ·
          refine ⟨7298447782060973352403703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4865631854707315568269135 7298447782060973352403703)
          ·
            refine ⟨10947671673091460028605555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7298447782060973352403703 10947671673091460028605555)
            ·
              refine ⟨16421507509637190042908333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10947671673091460028605555 16421507509637190042908333)
              ·
                refine ⟨6158065316113946266090625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16421507509637190042908333 6158065316113946266090625)
                ·
                  refine ⟨4618548987085459699567969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6158065316113946266090625 4618548987085459699567969)
                  ·
                    refine ⟨3463911740314094774675977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4618548987085459699567969 3463911740314094774675977)
                    ·
                      refine ⟨2597933805235571081006983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3463911740314094774675977 2597933805235571081006983)
                      ·
                        rfl

theorem cell23_5059458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_5059458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059458 prefixEnd_5059458 := by exact prefixLift 5059458
  have htrace : WordTrace (prefixWord ++ tailWord_5059458) baseStart_5059458 baseEnd_5059458 := by
    simpa [prefixWord, tailWord_5059458, baseEnd_5059458] using wordTrace_append hprefix tailTrace_5059458
  have hstable : (prefixWord ++ tailWord_5059458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059458).length < 2 ^ (prefixWord ++ tailWord_5059458).sum := by decide
  have hdescent : baseEnd_5059458 < baseStart_5059458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059473 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 5, 4]
def baseStart_5059473 : Nat := 118140960795 + 5059473 * 2 ^ 59
def prefixEnd_5059473 : Nat := 4983230072969 + 3 ^ 40 * 5059473 * 2
def baseEnd_5059473 : Nat := 865980502481796174106471

theorem tailTrace_5059473 : CollatzResearch.WordTrace tailWord_5059473 prefixEnd_5059473 865980502481796174106471 := by
  unfold tailWord_5059473
  simp only [CollatzResearch.WordTrace]
  refine ⟨184534140399400885039855073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123022760266267256693236715 184534140399400885039855073)
  ·
    refine ⟨138400605299550663779891305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184534140399400885039855073 138400605299550663779891305)
    ·
      refine ⟨103800453974662997834918479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138400605299550663779891305 103800453974662997834918479)
      ·
        refine ⟨155700680961994496752377719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103800453974662997834918479 155700680961994496752377719)
        ·
          refine ⟨233551021442991745128566579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155700680961994496752377719 233551021442991745128566579)
          ·
            refine ⟨350326532164487617692849869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233551021442991745128566579 350326532164487617692849869)
            ·
              refine ⟨131372449561682856634818701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 350326532164487617692849869 131372449561682856634818701)
              ·
                refine ⟨49264668585631071238057013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131372449561682856634818701 49264668585631071238057013)
                ·
                  refine ⟨4618562679902912928567845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49264668585631071238057013 4618562679902912928567845)
                  ·
                    refine ⟨865980502481796174106471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4618562679902912928567845 865980502481796174106471)
                    ·
                      rfl

theorem cell23_5059473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5, 4].length) (baseStart_5059473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059473 prefixEnd_5059473 := by exact prefixLift 5059473
  have htrace : WordTrace (prefixWord ++ tailWord_5059473) baseStart_5059473 baseEnd_5059473 := by
    simpa [prefixWord, tailWord_5059473, baseEnd_5059473] using wordTrace_append hprefix tailTrace_5059473
  have hstable : (prefixWord ++ tailWord_5059473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059473).length < 2 ^ (prefixWord ++ tailWord_5059473).sum := by decide
  have hdescent : baseEnd_5059473 < baseStart_5059473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059524 : List Nat := [2, 3, 3, 3, 1, 1, 1, 2, 3, 4]
def baseStart_5059524 : Nat := 118140960795 + 5059524 * 2 ^ 59
def prefixEnd_5059524 : Nat := 4983230072969 + 3 ^ 40 * 5059524 * 2
def baseEnd_5059524 : Nat := 865989231652922607593893

theorem tailTrace_5059524 : CollatzResearch.WordTrace tailWord_5059524 prefixEnd_5059524 865989231652922607593893 := by
  unfold tailWord_5059524
  simp only [CollatzResearch.WordTrace]
  refine ⟨92268000261108060374980813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123024000348144080499974417 92268000261108060374980813)
  ·
    refine ⟨34600500097915522640617805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92268000261108060374980813 34600500097915522640617805)
    ·
      refine ⟨12975187536718320990231677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34600500097915522640617805 12975187536718320990231677)
      ·
        refine ⟨4865695326269370371336879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12975187536718320990231677 4865695326269370371336879)
        ·
          refine ⟨7298542989404055557005319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4865695326269370371336879 7298542989404055557005319)
          ·
            refine ⟨10947814484106083335507979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7298542989404055557005319 10947814484106083335507979)
            ·
              refine ⟨16421721726159125003261969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10947814484106083335507979 16421721726159125003261969)
              ·
                refine ⟨12316291294619343752446477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16421721726159125003261969 12316291294619343752446477)
                ·
                  refine ⟨4618609235482253907167429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12316291294619343752446477 4618609235482253907167429)
                  ·
                    refine ⟨865989231652922607593893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4618609235482253907167429 865989231652922607593893)
                    ·
                      rfl

theorem cell23_5059524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_5059524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059524 prefixEnd_5059524 := by exact prefixLift 5059524
  have htrace : WordTrace (prefixWord ++ tailWord_5059524) baseStart_5059524 baseEnd_5059524 := by
    simpa [prefixWord, tailWord_5059524, baseEnd_5059524] using wordTrace_append hprefix tailTrace_5059524
  have hstable : (prefixWord ++ tailWord_5059524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059524).length < 2 ^ (prefixWord ++ tailWord_5059524).sum := by decide
  have hdescent : baseEnd_5059524 < baseStart_5059524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059554 : List Nat := [3, 3, 3, 1, 1, 3, 1, 2, 6]
def baseStart_5059554 : Nat := 118140960795 + 5059554 * 2 ^ 59
def prefixEnd_5059554 : Nat := 4983230072969 + 3 ^ 40 * 5059554 * 2
def baseEnd_5059554 : Nat := 288664788819822522822949

theorem tailTrace_5059554 : CollatzResearch.WordTrace tailWord_5059554 prefixEnd_5059554 288664788819822522822949 := by
  unfold tailWord_5059554
  simp only [CollatzResearch.WordTrace]
  refine ⟨46134273678026858968388429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123024729808071623915702477 46134273678026858968388429)
  ·
    refine ⟨17300352629260072113145661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46134273678026858968388429 17300352629260072113145661)
    ·
      refine ⟨6487632235972527042429623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17300352629260072113145661 6487632235972527042429623)
      ·
        refine ⟨9731448353958790563644435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6487632235972527042429623 9731448353958790563644435)
        ·
          refine ⟨14597172530938185845466653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9731448353958790563644435 14597172530938185845466653)
          ·
            refine ⟨5473939699101819692049995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14597172530938185845466653 5473939699101819692049995)
            ·
              refine ⟨8210909548652729538074993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5473939699101819692049995 8210909548652729538074993)
              ·
                refine ⟨6158182161489547153556245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8210909548652729538074993 6158182161489547153556245)
                ·
                  refine ⟨288664788819822522822949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6158182161489547153556245 288664788819822522822949)
                  ·
                    rfl

theorem cell23_5059554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_5059554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059554 prefixEnd_5059554 := by exact prefixLift 5059554
  have htrace : WordTrace (prefixWord ++ tailWord_5059554) baseStart_5059554 baseEnd_5059554 := by
    simpa [prefixWord, tailWord_5059554, baseEnd_5059554] using wordTrace_append hprefix tailTrace_5059554
  have hstable : (prefixWord ++ tailWord_5059554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059554).length < 2 ^ (prefixWord ++ tailWord_5059554).sum := by decide
  have hdescent : baseEnd_5059554 < baseStart_5059554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059580 : List Nat := [2, 2, 2, 1, 2, 3, 3, 1, 1, 6]
def baseStart_5059580 : Nat := 118140960795 + 5059580 * 2 ^ 59
def prefixEnd_5059580 : Nat := 4983230072969 + 3 ^ 40 * 5059580 * 2
def baseEnd_5059580 : Nat := 865998816625139867893807

theorem tailTrace_5059580 : CollatzResearch.WordTrace tailWord_5059580 prefixEnd_5059580 865998816625139867893807 := by
  unfold tailWord_5059580
  simp only [CollatzResearch.WordTrace]
  refine ⟨92269021505006621157000097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123025362006675494876000129 92269021505006621157000097)
  ·
    refine ⟨69201766128754965867750073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92269021505006621157000097 69201766128754965867750073)
    ·
      refine ⟨51901324596566224400812555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69201766128754965867750073 51901324596566224400812555)
      ·
        refine ⟨77851986894849336601218833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51901324596566224400812555 77851986894849336601218833)
        ·
          refine ⟨58388990171137002450914125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77851986894849336601218833 58388990171137002450914125)
          ·
            refine ⟨21895871314176375919092797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58388990171137002450914125 21895871314176375919092797)
            ·
              refine ⟨8210951742816140969659799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21895871314176375919092797 8210951742816140969659799)
              ·
                refine ⟨12316427614224211454489699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8210951742816140969659799 12316427614224211454489699)
                ·
                  refine ⟨18474641421336317181734549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12316427614224211454489699 18474641421336317181734549)
                  ·
                    refine ⟨865998816625139867893807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18474641421336317181734549 865998816625139867893807)
                    ·
                      rfl

theorem cell23_5059580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_5059580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059580 prefixEnd_5059580 := by exact prefixLift 5059580
  have htrace : WordTrace (prefixWord ++ tailWord_5059580) baseStart_5059580 baseEnd_5059580 := by
    simpa [prefixWord, tailWord_5059580, baseEnd_5059580] using wordTrace_append hprefix tailTrace_5059580
  have hstable : (prefixWord ++ tailWord_5059580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059580).length < 2 ^ (prefixWord ++ tailWord_5059580).sum := by decide
  have hdescent : baseEnd_5059580 < baseStart_5059580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059607 : List Nat := [1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 5]
def baseStart_5059607 : Nat := 118140960795 + 5059607 * 2 ^ 59
def prefixEnd_5059607 : Nat := 4983230072969 + 3 ^ 40 * 5059607 * 2
def baseEnd_5059607 : Nat := 2598010313853090998043797

theorem tailTrace_5059607 : CollatzResearch.WordTrace tailWord_5059607 prefixEnd_5059607 2598010313853090998043797 := by
  unfold tailWord_5059607
  simp only [CollatzResearch.WordTrace]
  refine ⟨184539027780915425925233075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123026018520610283950155383 184539027780915425925233075)
  ·
    refine ⟨276808541671373138887849613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184539027780915425925233075 276808541671373138887849613)
    ·
      refine ⟨103803203126764927082943605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 276808541671373138887849613 103803203126764927082943605)
      ·
        refine ⟨9731550293134211914025963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103803203126764927082943605 9731550293134211914025963)
        ·
          refine ⟨14597325439701317871038945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9731550293134211914025963 14597325439701317871038945)
          ·
            refine ⟨10947994079775988403279209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14597325439701317871038945 10947994079775988403279209)
            ·
              refine ⟨8210995559831991302459407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10947994079775988403279209 8210995559831991302459407)
              ·
                refine ⟨12316493339747986953689111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8210995559831991302459407 12316493339747986953689111)
                ·
                  refine ⟨18474740009621980430533667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12316493339747986953689111 18474740009621980430533667)
                  ·
                    refine ⟨27712110014432970645800501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18474740009621980430533667 27712110014432970645800501)
                    ·
                      refine ⟨2598010313853090998043797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27712110014432970645800501 2598010313853090998043797)
                      ·
                        rfl

theorem cell23_5059607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_5059607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059607 prefixEnd_5059607 := by exact prefixLift 5059607
  have htrace : WordTrace (prefixWord ++ tailWord_5059607) baseStart_5059607 baseEnd_5059607 := by
    simpa [prefixWord, tailWord_5059607, baseEnd_5059607] using wordTrace_append hprefix tailTrace_5059607
  have hstable : (prefixWord ++ tailWord_5059607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059607).length < 2 ^ (prefixWord ++ tailWord_5059607).sum := by decide
  have hdescent : baseEnd_5059607 < baseStart_5059607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059630 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_5059630 : Nat := 118140960795 + 5059630 * 2 ^ 59
def prefixEnd_5059630 : Nat := 4983230072969 + 3 ^ 40 * 5059630 * 2
def baseEnd_5059630 : Nat := 2598022123908144408056191

theorem tailTrace_5059630 : CollatzResearch.WordTrace tailWord_5059630 prefixEnd_5059630 2598022123908144408056191 := by
  unfold tailWord_5059630
  simp only [CollatzResearch.WordTrace]
  refine ⟨23067483332479012606665043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123026577773221400568880229 23067483332479012606665043)
  ·
    refine ⟨34601224998718518909997565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23067483332479012606665043 34601224998718518909997565)
    ·
      refine ⟨12975459374519444591249087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34601224998718518909997565 12975459374519444591249087)
      ·
        refine ⟨19463189061779166886873631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12975459374519444591249087 19463189061779166886873631)
        ·
          refine ⟨29194783592668750330310447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19463189061779166886873631 29194783592668750330310447)
          ·
            refine ⟨43792175389003125495465671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29194783592668750330310447 43792175389003125495465671)
            ·
              refine ⟨65688263083504688243198507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43792175389003125495465671 65688263083504688243198507)
              ·
                refine ⟨98532394625257032364797761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65688263083504688243198507 98532394625257032364797761)
                ·
                  refine ⟨73899295968942774273598321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98532394625257032364797761 73899295968942774273598321)
                  ·
                    refine ⟨55424471976707080705198741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73899295968942774273598321 55424471976707080705198741)
                    ·
                      refine ⟨2598022123908144408056191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55424471976707080705198741 2598022123908144408056191)
                      ·
                        rfl

theorem cell23_5059630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_5059630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059630 prefixEnd_5059630 := by exact prefixLift 5059630
  have htrace : WordTrace (prefixWord ++ tailWord_5059630) baseStart_5059630 baseEnd_5059630 := by
    simpa [prefixWord, tailWord_5059630, baseEnd_5059630] using wordTrace_append hprefix tailTrace_5059630
  have hstable : (prefixWord ++ tailWord_5059630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059630).length < 2 ^ (prefixWord ++ tailWord_5059630).sum := by decide
  have hdescent : baseEnd_5059630 < baseStart_5059630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059654 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3]
def baseStart_5059654 : Nat := 118140960795 + 5059654 * 2 ^ 59
def prefixEnd_5059654 : Nat := 4983230072969 + 3 ^ 40 * 5059654 * 2
def baseEnd_5059654 : Nat := 2598034447443852314156081

theorem tailTrace_5059654 : CollatzResearch.WordTrace tailWord_5059654 prefixEnd_5059654 2598034447443852314156081 := by
  unfold tailWord_5059654
  simp only [CollatzResearch.WordTrace]
  refine ⟨5766898187867036029756063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 123027161341163435301462677 5766898187867036029756063)
  ·
    refine ⟨8650347281800554044634095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5766898187867036029756063 8650347281800554044634095)
    ·
      refine ⟨12975520922700831066951143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8650347281800554044634095 12975520922700831066951143)
      ·
        refine ⟨19463281384051246600426715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12975520922700831066951143 19463281384051246600426715)
        ·
          refine ⟨29194922076076869900640073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19463281384051246600426715 29194922076076869900640073)
          ·
            refine ⟨21896191557057652425480055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29194922076076869900640073 21896191557057652425480055)
            ·
              refine ⟨32844287335586478638220083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21896191557057652425480055 32844287335586478638220083)
              ·
                refine ⟨49266431003379717957330125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32844287335586478638220083 49266431003379717957330125)
                ·
                  refine ⟨18474911626267394233998797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49266431003379717957330125 18474911626267394233998797)
                  ·
                    refine ⟨6928091859850272837749549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18474911626267394233998797 6928091859850272837749549)
                    ·
                      refine ⟨2598034447443852314156081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6928091859850272837749549 2598034447443852314156081)
                      ·
                        rfl

theorem cell23_5059654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_5059654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059654 prefixEnd_5059654 := by exact prefixLift 5059654
  have htrace : WordTrace (prefixWord ++ tailWord_5059654) baseStart_5059654 baseEnd_5059654 := by
    simpa [prefixWord, tailWord_5059654, baseEnd_5059654] using wordTrace_append hprefix tailTrace_5059654
  have hstable : (prefixWord ++ tailWord_5059654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059654).length < 2 ^ (prefixWord ++ tailWord_5059654).sum := by decide
  have hdescent : baseEnd_5059654 < baseStart_5059654 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059680 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 3]
def baseStart_5059680 : Nat := 118140960795 + 5059680 * 2 ^ 59
def prefixEnd_5059680 : Nat := 4983230072969 + 3 ^ 40 * 5059680 * 2
def baseEnd_5059680 : Nat := 2598047797940869212430961

theorem tailTrace_5059680 : CollatzResearch.WordTrace tailWord_5059680 prefixEnd_5059680 2598047797940869212430961 := by
  unfold tailWord_5059680
  simp only [CollatzResearch.WordTrace]
  refine ⟨92270845154825479696320247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123027793539767306261760329 92270845154825479696320247)
  ·
    refine ⟨138406267732238219544480371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92270845154825479696320247 138406267732238219544480371)
    ·
      refine ⟨207609401598357329316720557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138406267732238219544480371 207609401598357329316720557)
      ·
        refine ⟨77853525599383998493770209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207609401598357329316720557 77853525599383998493770209)
        ·
          refine ⟨58390144199537998870327657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77853525599383998493770209 58390144199537998870327657)
          ·
            refine ⟨43792608149653499152745743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58390144199537998870327657 43792608149653499152745743)
            ·
              refine ⟨65688912224480248729118615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43792608149653499152745743 65688912224480248729118615)
              ·
                refine ⟨98533368336720373093677923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65688912224480248729118615 98533368336720373093677923)
                ·
                  refine ⟨147800052505080559640516885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98533368336720373093677923 147800052505080559640516885)
                  ·
                    refine ⟨6928127461175651233149229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 147800052505080559640516885 6928127461175651233149229)
                    ·
                      refine ⟨2598047797940869212430961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6928127461175651233149229 2598047797940869212430961)
                      ·
                        rfl

theorem cell23_5059680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_5059680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059680 prefixEnd_5059680 := by exact prefixLift 5059680
  have htrace : WordTrace (prefixWord ++ tailWord_5059680) baseStart_5059680 baseEnd_5059680 := by
    simpa [prefixWord, tailWord_5059680, baseEnd_5059680] using wordTrace_append hprefix tailTrace_5059680
  have hstable : (prefixWord ++ tailWord_5059680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059680).length < 2 ^ (prefixWord ++ tailWord_5059680).sum := by decide
  have hdescent : baseEnd_5059680 < baseStart_5059680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5059694 : List Nat := [4, 1, 2, 2, 1, 2, 1, 3, 1, 4, 2]
def baseStart_5059694 : Nat := 118140960795 + 5059694 * 2 ^ 59
def prefixEnd_5059694 : Nat := 4983230072969 + 3 ^ 40 * 5059694 * 2
def baseEnd_5059694 : Nat := 2598054986670032157655897

theorem tailTrace_5059694 : CollatzResearch.WordTrace tailWord_5059694 prefixEnd_5059694 2598054986670032157655897 := by
  unfold tailWord_5059694
  simp only [CollatzResearch.WordTrace]
  refine ⟨23067775116450029972956267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123028133954400159855766757 23067775116450029972956267)
  ·
    refine ⟨34601662674675044959434401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23067775116450029972956267 34601662674675044959434401)
    ·
      refine ⟨25951247006006283719575801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34601662674675044959434401 25951247006006283719575801)
      ·
        refine ⟨19463435254504712789681851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25951247006006283719575801 19463435254504712789681851)
        ·
          refine ⟨29195152881757069184522777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19463435254504712789681851 29195152881757069184522777)
          ·
            refine ⟨21896364661317801888392083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29195152881757069184522777 21896364661317801888392083)
            ·
              refine ⟨32844546991976702832588125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21896364661317801888392083 32844546991976702832588125)
              ·
                refine ⟨12316705121991263562220547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32844546991976702832588125 12316705121991263562220547)
                ·
                  refine ⟨18475057682986895343330821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12316705121991263562220547 18475057682986895343330821)
                  ·
                    refine ⟨3464073315560042876874529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18475057682986895343330821 3464073315560042876874529)
                    ·
                      refine ⟨2598054986670032157655897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3464073315560042876874529 2598054986670032157655897)
                      ·
                        rfl

theorem cell23_5059694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_5059694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5059694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5059694 prefixEnd_5059694 := by exact prefixLift 5059694
  have htrace : WordTrace (prefixWord ++ tailWord_5059694) baseStart_5059694 baseEnd_5059694 := by
    simpa [prefixWord, tailWord_5059694, baseEnd_5059694] using wordTrace_append hprefix tailTrace_5059694
  have hstable : (prefixWord ++ tailWord_5059694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5059694).length < 2 ^ (prefixWord ++ tailWord_5059694).sum := by decide
  have hdescent : baseEnd_5059694 < baseStart_5059694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5059694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
