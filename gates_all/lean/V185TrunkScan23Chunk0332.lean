import V185TrunkScan23Chunk0331

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1962620 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 6, 2, 2]
def baseStart_1962620 : Nat := 118140960795 + 1962620 * 2 ^ 59
def prefixEnd_1962620 : Nat := 4983230072969 + 3 ^ 40 * 1962620 * 2
def baseEnd_1962620 : Nat := 1007767402127216473924081

theorem tailTrace_1962620 : CollatzResearch.WordTrace tailWord_1962620 prefixEnd_1962620 1007767402127216473924081 := by
  unfold tailWord_1962620
  simp only [CollatzResearch.WordTrace]
  refine ⟨35791316074885201827682657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47721754766513602436910209 35791316074885201827682657)
  ·
    refine ⟨26843487056163901370761993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35791316074885201827682657 26843487056163901370761993)
    ·
      refine ⟨20132615292122926028071495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26843487056163901370761993 20132615292122926028071495)
      ·
        refine ⟨30198922938184389042107243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20132615292122926028071495 30198922938184389042107243)
        ·
          refine ⟨45298384407276583563160865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30198922938184389042107243 45298384407276583563160865)
          ·
            refine ⟨33973788305457437672370649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45298384407276583563160865 33973788305457437672370649)
            ·
              refine ⟨25480341229093078254277987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33973788305457437672370649 25480341229093078254277987)
              ·
                refine ⟨38220511843639617381416981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25480341229093078254277987 38220511843639617381416981)
                ·
                  refine ⟨1791586492670607064753921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38220511843639617381416981 1791586492670607064753921)
                  ·
                    refine ⟨1343689869502955298565441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1791586492670607064753921 1343689869502955298565441)
                    ·
                      refine ⟨1007767402127216473924081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1343689869502955298565441 1007767402127216473924081)
                      ·
                        rfl

theorem cell23_1962620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 6, 2, 2].length) (baseStart_1962620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962620 prefixEnd_1962620 := by exact prefixLift 1962620
  have htrace : WordTrace (prefixWord ++ tailWord_1962620) baseStart_1962620 baseEnd_1962620 := by
    simpa [prefixWord, tailWord_1962620, baseEnd_1962620] using wordTrace_append hprefix tailTrace_1962620
  have hstable : (prefixWord ++ tailWord_1962620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962620).length < 2 ^ (prefixWord ++ tailWord_1962620).sum := by decide
  have hdescent : baseEnd_1962620 < baseStart_1962620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962643 : List Nat := [1, 1, 1, 2, 1, 2, 2, 8, 5]
def baseStart_1962643 : Nat := 118140960795 + 1962643 * 2 ^ 59
def prefixEnd_1962643 : Nat := 4983230072969 + 3 ^ 40 * 1962643 * 2
def baseEnd_1962643 : Nat := 111975468020252209326275

theorem tailTrace_1962643 : CollatzResearch.WordTrace tailWord_1962643 prefixEnd_1962643 111975468020252209326275 := by
  unfold tailWord_1962643
  simp only [CollatzResearch.WordTrace]
  refine ⟨71583471028687078583452583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47722314019124719055635055 71583471028687078583452583)
  ·
    refine ⟨107375206543030617875178875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71583471028687078583452583 107375206543030617875178875)
    ·
      refine ⟨161062809814545926812768313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107375206543030617875178875 161062809814545926812768313)
      ·
        refine ⟨120797107360909445109576235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161062809814545926812768313 120797107360909445109576235)
        ·
          refine ⟨181195661041364167664364353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120797107360909445109576235 181195661041364167664364353)
          ·
            refine ⟨135896745781023125748273265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181195661041364167664364353 135896745781023125748273265)
            ·
              refine ⟨101922559335767344311204949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135896745781023125748273265 101922559335767344311204949)
              ·
                refine ⟨1194404992216023566146933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 101922559335767344311204949 1194404992216023566146933)
                ·
                  refine ⟨111975468020252209326275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1194404992216023566146933 111975468020252209326275)
                  ·
                    rfl

theorem cell23_1962643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 8, 5].length) (baseStart_1962643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962643 prefixEnd_1962643 := by exact prefixLift 1962643
  have htrace : WordTrace (prefixWord ++ tailWord_1962643) baseStart_1962643 baseEnd_1962643 := by
    simpa [prefixWord, tailWord_1962643, baseEnd_1962643] using wordTrace_append hprefix tailTrace_1962643
  have hstable : (prefixWord ++ tailWord_1962643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962643).length < 2 ^ (prefixWord ++ tailWord_1962643).sum := by decide
  have hdescent : baseEnd_1962643 < baseStart_1962643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962653 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 1, 5, 3]
def baseStart_1962653 : Nat := 118140960795 + 1962653 * 2 ^ 59
def prefixEnd_1962653 : Nat := 4983230072969 + 3 ^ 40 * 1962653 * 2
def baseEnd_1962653 : Nat := 1007784346988814844811429

theorem tailTrace_1962653 : CollatzResearch.WordTrace tailWord_1962653 prefixEnd_1962653 1007784346988814844811429 := by
  unfold tailWord_1962653
  simp only [CollatzResearch.WordTrace]
  refine ⟨71583835758650850291316613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47722557172433900194211075 71583835758650850291316613)
  ·
    refine ⟨13421969204747034429621865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71583835758650850291316613 13421969204747034429621865)
    ·
      refine ⟨10066476903560275822216399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13421969204747034429621865 10066476903560275822216399)
      ·
        refine ⟨15099715355340413733324599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10066476903560275822216399 15099715355340413733324599)
        ·
          refine ⟨22649573033010620599986899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15099715355340413733324599 22649573033010620599986899)
          ·
            refine ⟨33974359549515930899980349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22649573033010620599986899 33974359549515930899980349)
            ·
              refine ⟨12740384831068474087492631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33974359549515930899980349 12740384831068474087492631)
              ·
                refine ⟨19110577246602711131238947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12740384831068474087492631 19110577246602711131238947)
                ·
                  refine ⟨28665865869904066696858421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19110577246602711131238947 28665865869904066696858421)
                  ·
                    refine ⟨2687424925303506252830477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28665865869904066696858421 2687424925303506252830477)
                    ·
                      refine ⟨1007784346988814844811429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2687424925303506252830477 1007784346988814844811429)
                      ·
                        rfl

theorem cell23_1962653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_1962653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962653 prefixEnd_1962653 := by exact prefixLift 1962653
  have htrace : WordTrace (prefixWord ++ tailWord_1962653) baseStart_1962653 baseEnd_1962653 := by
    simpa [prefixWord, tailWord_1962653, baseEnd_1962653] using wordTrace_append hprefix tailTrace_1962653
  have hstable : (prefixWord ++ tailWord_1962653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962653).length < 2 ^ (prefixWord ++ tailWord_1962653).sum := by decide
  have hdescent : baseEnd_1962653 < baseStart_1962653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962654 : List Nat := [4, 3, 1, 1, 1, 1, 1, 5, 2, 2, 2]
def baseStart_1962654 : Nat := 118140960795 + 1962654 * 2 ^ 59
def prefixEnd_1962654 : Nat := 4983230072969 + 3 ^ 40 * 1962654 * 2
def baseEnd_1962654 : Nat := 1007784860469469340898925

theorem tailTrace_1962654 : CollatzResearch.WordTrace tailWord_1962654 prefixEnd_1962654 1007784860469469340898925 := by
  unfold tailWord_1962654
  simp only [CollatzResearch.WordTrace]
  refine ⟨8947984028955903432762877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47722581487764818308068677 8947984028955903432762877)
  ·
    refine ⟨3355494010858463787286079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8947984028955903432762877 3355494010858463787286079)
    ·
      refine ⟨5033241016287695680929119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3355494010858463787286079 5033241016287695680929119)
      ·
        refine ⟨7549861524431543521393679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5033241016287695680929119 7549861524431543521393679)
        ·
          refine ⟨11324792286647315282090519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7549861524431543521393679 11324792286647315282090519)
          ·
            refine ⟨16987188429970972923135779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11324792286647315282090519 16987188429970972923135779)
            ·
              refine ⟨25480782644956459384703669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16987188429970972923135779 25480782644956459384703669)
              ·
                refine ⟨2388823372964668067315969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25480782644956459384703669 2388823372964668067315969)
                ·
                  refine ⟨1791617529723501050486977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2388823372964668067315969 1791617529723501050486977)
                  ·
                    refine ⟨1343713147292625787865233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1791617529723501050486977 1343713147292625787865233)
                    ·
                      refine ⟨1007784860469469340898925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1343713147292625787865233 1007784860469469340898925)
                      ·
                        rfl

theorem cell23_1962654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_1962654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962654 prefixEnd_1962654 := by exact prefixLift 1962654
  have htrace : WordTrace (prefixWord ++ tailWord_1962654) baseStart_1962654 baseEnd_1962654 := by
    simpa [prefixWord, tailWord_1962654, baseEnd_1962654] using wordTrace_append hprefix tailTrace_1962654
  have hstable : (prefixWord ++ tailWord_1962654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962654).length < 2 ^ (prefixWord ++ tailWord_1962654).sum := by decide
  have hdescent : baseEnd_1962654 < baseStart_1962654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962677 : List Nat := [1, 3, 3, 3, 1, 2, 2, 3, 5]
def baseStart_1962677 : Nat := 118140960795 + 1962677 * 2 ^ 59
def prefixEnd_1962677 : Nat := 4983230072969 + 3 ^ 40 * 1962677 * 2
def baseEnd_1962677 : Nat := 111977407836058083434591

theorem tailTrace_1962677 : CollatzResearch.WordTrace tailWord_1962677 prefixEnd_1962677 111977407836058083434591 := by
  unfold tailWord_1962677
  simp only [CollatzResearch.WordTrace]
  refine ⟨71584711110563902390190285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47723140740375934926793523 71584711110563902390190285)
  ·
    refine ⟨26844266666461463396321357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71584711110563902390190285 26844266666461463396321357)
    ·
      refine ⟨10066599999923048773620509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26844266666461463396321357 10066599999923048773620509)
      ·
        refine ⟨3774974999971143290107691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10066599999923048773620509 3774974999971143290107691)
        ·
          refine ⟨5662462499956714935161537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3774974999971143290107691 5662462499956714935161537)
          ·
            refine ⟨4246846874967536201371153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5662462499956714935161537 4246846874967536201371153)
            ·
              refine ⟨3185135156225652151028365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4246846874967536201371153 3185135156225652151028365)
              ·
                refine ⟨1194425683584619556635637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3185135156225652151028365 1194425683584619556635637)
                ·
                  refine ⟨111977407836058083434591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1194425683584619556635637 111977407836058083434591)
                  ·
                    rfl

theorem cell23_1962677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 3, 5].length) (baseStart_1962677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962677 prefixEnd_1962677 := by exact prefixLift 1962677
  have htrace : WordTrace (prefixWord ++ tailWord_1962677) baseStart_1962677 baseEnd_1962677 := by
    simpa [prefixWord, tailWord_1962677, baseEnd_1962677] using wordTrace_append hprefix tailTrace_1962677
  have hstable : (prefixWord ++ tailWord_1962677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962677).length < 2 ^ (prefixWord ++ tailWord_1962677).sum := by decide
  have hdescent : baseEnd_1962677 < baseStart_1962677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962694 : List Nat := [6, 1, 2, 1, 2, 1, 2, 1, 7]
def baseStart_1962694 : Nat := 118140960795 + 1962694 * 2 ^ 59
def prefixEnd_1962694 : Nat := 4983230072969 + 3 ^ 40 * 1962694 * 2
def baseEnd_1962694 : Nat := 111978377743961020488749

theorem tailTrace_1962694 : CollatzResearch.WordTrace tailWord_1962694 prefixEnd_1962694 111978377743961020488749 := by
  unfold tailWord_1962694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2237041598484447321673723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47723554101001542862372757 2237041598484447321673723)
  ·
    refine ⟨3355562397726670982510585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2237041598484447321673723 3355562397726670982510585)
    ·
      refine ⟨2516671798295003236882939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3355562397726670982510585 2516671798295003236882939)
      ·
        refine ⟨3775007697442504855324409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2516671798295003236882939 3775007697442504855324409)
        ·
          refine ⟨2831255773081878641493307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3775007697442504855324409 2831255773081878641493307)
          ·
            refine ⟨4246883659622817962239961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2831255773081878641493307 4246883659622817962239961)
            ·
              refine ⟨3185162744717113471679971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4246883659622817962239961 3185162744717113471679971)
              ·
                refine ⟨4777744117075670207519957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3185162744717113471679971 4777744117075670207519957)
                ·
                  refine ⟨111978377743961020488749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4777744117075670207519957 111978377743961020488749)
                  ·
                    rfl

theorem cell23_1962694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_1962694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962694 prefixEnd_1962694 := by exact prefixLift 1962694
  have htrace : WordTrace (prefixWord ++ tailWord_1962694) baseStart_1962694 baseEnd_1962694 := by
    simpa [prefixWord, tailWord_1962694, baseEnd_1962694] using wordTrace_append hprefix tailTrace_1962694
  have hstable : (prefixWord ++ tailWord_1962694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962694).length < 2 ^ (prefixWord ++ tailWord_1962694).sum := by decide
  have hdescent : baseEnd_1962694 < baseStart_1962694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962713 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 3, 4, 3]
def baseStart_1962713 : Nat := 118140960795 + 1962713 * 2 ^ 59
def prefixEnd_1962713 : Nat := 4983230072969 + 3 ^ 40 * 1962713 * 2
def baseEnd_1962713 : Nat := 1007815155828084610061153

theorem tailTrace_1962713 : CollatzResearch.WordTrace tailWord_1962713 prefixEnd_1962713 1007815155828084610061153 := by
  unfold tailWord_1962713
  simp only [CollatzResearch.WordTrace]
  refine ⟨71586024138433480538500793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47724016092288987025667195 71586024138433480538500793)
  ·
    refine ⟨53689518103825110403875595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71586024138433480538500793 53689518103825110403875595)
    ·
      refine ⟨80534277155737665605813393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53689518103825110403875595 80534277155737665605813393)
      ·
        refine ⟨60400707866803249204360045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80534277155737665605813393 60400707866803249204360045)
        ·
          refine ⟨22650265450051218451635017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60400707866803249204360045 22650265450051218451635017)
          ·
            refine ⟨16987699087538413838726263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22650265450051218451635017 16987699087538413838726263)
            ·
              refine ⟨25481548631307620758089395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16987699087538413838726263 25481548631307620758089395)
              ·
                refine ⟨38222322946961431137134093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25481548631307620758089395 38222322946961431137134093)
                ·
                  refine ⟨14333371105110536676425285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38222322946961431137134093 14333371105110536676425285)
                  ·
                    refine ⟨2687507082208225626829741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14333371105110536676425285 2687507082208225626829741)
                    ·
                      refine ⟨1007815155828084610061153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2687507082208225626829741 1007815155828084610061153)
                      ·
                        rfl

theorem cell23_1962713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 4, 3].length) (baseStart_1962713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962713 prefixEnd_1962713 := by exact prefixLift 1962713
  have htrace : WordTrace (prefixWord ++ tailWord_1962713) baseStart_1962713 baseEnd_1962713 := by
    simpa [prefixWord, tailWord_1962713, baseEnd_1962713] using wordTrace_append hprefix tailTrace_1962713
  have hstable : (prefixWord ++ tailWord_1962713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962713).length < 2 ^ (prefixWord ++ tailWord_1962713).sum := by decide
  have hdescent : baseEnd_1962713 < baseStart_1962713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962730 : List Nat := [3, 1, 3, 1, 1, 1, 1, 5, 2, 2, 3]
def baseStart_1962730 : Nat := 118140960795 + 1962730 * 2 ^ 59
def prefixEnd_1962730 : Nat := 4983230072969 + 3 ^ 40 * 1962730 * 2
def baseEnd_1962730 : Nat := 1007823884999211043548575

theorem tailTrace_1962730 : CollatzResearch.WordTrace tailWord_1962730 prefixEnd_1962730 1007823884999211043548575 := by
  unfold tailWord_1962730
  simp only [CollatzResearch.WordTrace]
  refine ⟨17896661044842973110467411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47724429452914594961246429 17896661044842973110467411)
  ·
    refine ⟨26844991567264459665701117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17896661044842973110467411 26844991567264459665701117)
    ·
      refine ⟨10066871837724172374637919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26844991567264459665701117 10066871837724172374637919)
      ·
        refine ⟨15100307756586258561956879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10066871837724172374637919 15100307756586258561956879)
        ·
          refine ⟨22650461634879387842935319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15100307756586258561956879 22650461634879387842935319)
          ·
            refine ⟨33975692452319081764402979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22650461634879387842935319 33975692452319081764402979)
            ·
              refine ⟨50963538678478622646604469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33975692452319081764402979 50963538678478622646604469)
              ·
                refine ⟨4777831751107370873119169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50963538678478622646604469 4777831751107370873119169)
                ·
                  refine ⟨3583373813330528154839377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4777831751107370873119169 3583373813330528154839377)
                  ·
                    refine ⟨2687530359997896116129533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3583373813330528154839377 2687530359997896116129533)
                    ·
                      refine ⟨1007823884999211043548575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2687530359997896116129533 1007823884999211043548575)
                      ·
                        rfl

theorem cell23_1962730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_1962730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962730 prefixEnd_1962730 := by exact prefixLift 1962730
  have htrace : WordTrace (prefixWord ++ tailWord_1962730) baseStart_1962730 baseEnd_1962730 := by
    simpa [prefixWord, tailWord_1962730, baseEnd_1962730] using wordTrace_append hprefix tailTrace_1962730
  have hstable : (prefixWord ++ tailWord_1962730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962730).length < 2 ^ (prefixWord ++ tailWord_1962730).sum := by decide
  have hdescent : baseEnd_1962730 < baseStart_1962730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962733 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 10]
def baseStart_1962733 : Nat := 118140960795 + 1962733 * 2 ^ 59
def prefixEnd_1962733 : Nat := 4983230072969 + 3 ^ 40 * 1962733 * 2
def baseEnd_1962733 : Nat := 111980602826797170201229

theorem tailTrace_1962733 : CollatzResearch.WordTrace tailWord_1962733 prefixEnd_1962733 111980602826797170201229 := by
  unfold tailWord_1962733
  simp only [CollatzResearch.WordTrace]
  refine ⟨71586753598361023954228853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47724502398907349302819235 71586753598361023954228853)
  ·
    refine ⟨6711258149846345995708955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71586753598361023954228853 6711258149846345995708955)
    ·
      refine ⟨10066887224769518993563433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6711258149846345995708955 10066887224769518993563433)
      ·
        refine ⟨7550165418577139245172575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10066887224769518993563433 7550165418577139245172575)
        ·
          refine ⟨11325248127865708867758863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7550165418577139245172575 11325248127865708867758863)
          ·
            refine ⟨16987872191798563301638295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11325248127865708867758863 16987872191798563301638295)
            ·
              refine ⟨25481808287697844952457443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16987872191798563301638295 25481808287697844952457443)
              ·
                refine ⟨38222712431546767428686165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25481808287697844952457443 38222712431546767428686165)
                ·
                  refine ⟨111980602826797170201229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 38222712431546767428686165 111980602826797170201229)
                  ·
                    rfl

theorem cell23_1962733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_1962733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962733 prefixEnd_1962733 := by exact prefixLift 1962733
  have htrace : WordTrace (prefixWord ++ tailWord_1962733) baseStart_1962733 baseEnd_1962733 := by
    simpa [prefixWord, tailWord_1962733, baseEnd_1962733] using wordTrace_append hprefix tailTrace_1962733
  have hstable : (prefixWord ++ tailWord_1962733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962733).length < 2 ^ (prefixWord ++ tailWord_1962733).sum := by decide
  have hdescent : baseEnd_1962733 < baseStart_1962733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962750 : List Nat := [4, 2, 2, 1, 2, 1, 2, 1, 8]
def baseStart_1962750 : Nat := 118140960795 + 1962750 * 2 ^ 59
def prefixEnd_1962750 : Nat := 4983230072969 + 3 ^ 40 * 1962750 * 2
def baseEnd_1962750 : Nat := 111981572734700107255387

theorem tailTrace_1962750 : CollatzResearch.WordTrace tailWord_1962750 prefixEnd_1962750 111981572734700107255387 := by
  unfold tailWord_1962750
  simp only [CollatzResearch.WordTrace]
  refine ⟨8948421704912429482199713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47724915759532957238398469 8948421704912429482199713)
  ·
    refine ⟨6711316278684322111649785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8948421704912429482199713 6711316278684322111649785)
    ·
      refine ⟨5033487209013241583737339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6711316278684322111649785 5033487209013241583737339)
      ·
        refine ⟨7550230813519862375606009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5033487209013241583737339 7550230813519862375606009)
        ·
          refine ⟨5662673110139896781704507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7550230813519862375606009 5662673110139896781704507)
          ·
            refine ⟨8494009665209845172556761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5662673110139896781704507 8494009665209845172556761)
            ·
              refine ⟨6370507248907383879417571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8494009665209845172556761 6370507248907383879417571)
              ·
                refine ⟨9555760873361075819126357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6370507248907383879417571 9555760873361075819126357)
                ·
                  refine ⟨111981572734700107255387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9555760873361075819126357 111981572734700107255387)
                  ·
                    rfl

theorem cell23_1962750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_1962750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962750 prefixEnd_1962750 := by exact prefixLift 1962750
  have htrace : WordTrace (prefixWord ++ tailWord_1962750) baseStart_1962750 baseEnd_1962750 := by
    simpa [prefixWord, tailWord_1962750, baseEnd_1962750] using wordTrace_append hprefix tailTrace_1962750
  have hstable : (prefixWord ++ tailWord_1962750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962750).length < 2 ^ (prefixWord ++ tailWord_1962750).sum := by decide
  have hdescent : baseEnd_1962750 < baseStart_1962750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962754 : List Nat := [3, 4, 1, 1, 1, 4, 1, 1, 3, 4]
def baseStart_1962754 : Nat := 118140960795 + 1962754 * 2 ^ 59
def prefixEnd_1962754 : Nat := 4983230072969 + 3 ^ 40 * 1962754 * 2
def baseEnd_1962754 : Nat := 335945402844972983216155

theorem tailTrace_1962754 : CollatzResearch.WordTrace tailWord_1962754 prefixEnd_1962754 335945402844972983216155 := by
  unfold tailWord_1962754
  simp only [CollatzResearch.WordTrace]
  refine ⟨17896879882821236135185829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47725013020856629693828877 17896879882821236135185829)
  ·
    refine ⟨3355664978028981775347343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17896879882821236135185829 3355664978028981775347343)
    ·
      refine ⟨5033497467043472663021015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3355664978028981775347343 5033497467043472663021015)
      ·
        refine ⟨7550246200565208994531523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5033497467043472663021015 7550246200565208994531523)
        ·
          refine ⟨11325369300847813491797285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7550246200565208994531523 11325369300847813491797285)
          ·
            refine ⟨2123506743908965029711991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11325369300847813491797285 2123506743908965029711991)
            ·
              refine ⟨3185260115863447544567987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2123506743908965029711991 3185260115863447544567987)
              ·
                refine ⟨4777890173795171316851981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3185260115863447544567987 4777890173795171316851981)
                ·
                  refine ⟨1791708815173189243819493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4777890173795171316851981 1791708815173189243819493)
                  ·
                    refine ⟨335945402844972983216155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1791708815173189243819493 335945402844972983216155)
                    ·
                      rfl

theorem cell23_1962754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_1962754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962754 prefixEnd_1962754 := by exact prefixLift 1962754
  have htrace : WordTrace (prefixWord ++ tailWord_1962754) baseStart_1962754 baseEnd_1962754 := by
    simpa [prefixWord, tailWord_1962754, baseEnd_1962754] using wordTrace_append hprefix tailTrace_1962754
  have hstable : (prefixWord ++ tailWord_1962754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962754).length < 2 ^ (prefixWord ++ tailWord_1962754).sum := by decide
  have hdescent : baseEnd_1962754 < baseStart_1962754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962763 : List Nat := [1, 1, 1, 1, 5, 1, 1, 4, 3, 5]
def baseStart_1962763 : Nat := 118140960795 + 1962763 * 2 ^ 59
def prefixEnd_1962763 : Nat := 4983230072969 + 3 ^ 40 * 1962763 * 2
def baseEnd_1962763 : Nat := 335946943286936471478641

theorem tailTrace_1962763 : CollatzResearch.WordTrace tailWord_1962763 prefixEnd_1962763 335946943286936471478641 := by
  unfold tailWord_1962763
  simp only [CollatzResearch.WordTrace]
  refine ⟨71587847788252339077820943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47725231858834892718547295 71587847788252339077820943)
  ·
    refine ⟨107381771682378508616731415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71587847788252339077820943 107381771682378508616731415)
    ·
      refine ⟨161072657523567762925097123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107381771682378508616731415 161072657523567762925097123)
      ·
        refine ⟨241608986285351644387645685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161072657523567762925097123 241608986285351644387645685)
        ·
          refine ⟨22650842464251716661341783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 241608986285351644387645685 22650842464251716661341783)
          ·
            refine ⟨33976263696377574992012675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22650842464251716661341783 33976263696377574992012675)
            ·
              refine ⟨50964395544566362488019013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33976263696377574992012675 50964395544566362488019013)
              ·
                refine ⟨9555824164606192966503565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50964395544566362488019013 9555824164606192966503565)
                ·
                  refine ⟨3583434061727322362438837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9555824164606192966503565 3583434061727322362438837)
                  ·
                    refine ⟨335946943286936471478641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3583434061727322362438837 335946943286936471478641)
                    ·
                      rfl

theorem cell23_1962763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 5].length) (baseStart_1962763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962763 prefixEnd_1962763 := by exact prefixLift 1962763
  have htrace : WordTrace (prefixWord ++ tailWord_1962763) baseStart_1962763 baseEnd_1962763 := by
    simpa [prefixWord, tailWord_1962763, baseEnd_1962763] using wordTrace_append hprefix tailTrace_1962763
  have hstable : (prefixWord ++ tailWord_1962763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962763).length < 2 ^ (prefixWord ++ tailWord_1962763).sum := by decide
  have hdescent : baseEnd_1962763 < baseStart_1962763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962780 : List Nat := [2, 2, 3, 1, 1, 4, 1, 1, 3, 5]
def baseStart_1962780 : Nat := 118140960795 + 1962780 * 2 ^ 59
def prefixEnd_1962780 : Nat := 4983230072969 + 3 ^ 40 * 1962780 * 2
def baseEnd_1962780 : Nat := 335949853010645282641115

theorem tailTrace_1962780 : CollatzResearch.WordTrace tailWord_1962780 prefixEnd_1962780 335949853010645282641115 := by
  unfold tailWord_1962780
  simp only [CollatzResearch.WordTrace]
  refine ⟨35794233914595375490594897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47725645219460500654126529 35794233914595375490594897)
  ·
    refine ⟨26845675435946531617946173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35794233914595375490594897 26845675435946531617946173)
    ·
      refine ⟨10067128288479949356729815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26845675435946531617946173 10067128288479949356729815)
      ·
        refine ⟨15100692432719924035094723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10067128288479949356729815 15100692432719924035094723)
        ·
          refine ⟨22651038649079886052642085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15100692432719924035094723 22651038649079886052642085)
          ·
            refine ⟨4247069746702478634870391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22651038649079886052642085 4247069746702478634870391)
            ·
              refine ⟨6370604620053717952305587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4247069746702478634870391 6370604620053717952305587)
              ·
                refine ⟨9555906930080576928458381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6370604620053717952305587 9555906930080576928458381)
                ·
                  refine ⟨3583465098780216348171893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9555906930080576928458381 3583465098780216348171893)
                  ·
                    refine ⟨335949853010645282641115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3583465098780216348171893 335949853010645282641115)
                    ·
                      rfl

theorem cell23_1962780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_1962780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962780 prefixEnd_1962780 := by exact prefixLift 1962780
  have htrace : WordTrace (prefixWord ++ tailWord_1962780) baseStart_1962780 baseEnd_1962780 := by
    simpa [prefixWord, tailWord_1962780, baseEnd_1962780] using wordTrace_append hprefix tailTrace_1962780
  have hstable : (prefixWord ++ tailWord_1962780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962780).length < 2 ^ (prefixWord ++ tailWord_1962780).sum := by decide
  have hdescent : baseEnd_1962780 < baseStart_1962780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962793 : List Nat := [1, 2, 1, 1, 1, 1, 1, 8, 1, 6]
def baseStart_1962793 : Nat := 118140960795 + 1962793 * 2 ^ 59
def prefixEnd_1962793 : Nat := 4983230072969 + 3 ^ 40 * 1962793 * 2
def baseEnd_1962793 : Nat := 335952078093481432353595

theorem tailTrace_1962793 : CollatzResearch.WordTrace tailWord_1962793 prefixEnd_1962793 335952078093481432353595 := by
  unfold tailWord_1962793
  simp only [CollatzResearch.WordTrace]
  refine ⟨71588941978143654201413033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47725961318762436134275355 71588941978143654201413033)
  ·
    refine ⟨53691706483607740651059775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71588941978143654201413033 53691706483607740651059775)
    ·
      refine ⟨80537559725411610976589663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53691706483607740651059775 80537559725411610976589663)
      ·
        refine ⟨120806339588117416464884495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80537559725411610976589663 120806339588117416464884495)
        ·
          refine ⟨181209509382176124697326743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120806339588117416464884495 181209509382176124697326743)
          ·
            refine ⟨271814264073264187045990115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181209509382176124697326743 271814264073264187045990115)
            ·
              refine ⟨407721396109896280568985173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271814264073264187045990115 407721396109896280568985173)
              ·
                refine ⟨4777985110662847037917795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 407721396109896280568985173 4777985110662847037917795)
                ·
                  refine ⟨7166977665994270556876693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4777985110662847037917795 7166977665994270556876693)
                  ·
                    refine ⟨335952078093481432353595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7166977665994270556876693 335952078093481432353595)
                    ·
                      rfl

theorem cell23_1962793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 6].length) (baseStart_1962793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962793 prefixEnd_1962793 := by exact prefixLift 1962793
  have htrace : WordTrace (prefixWord ++ tailWord_1962793) baseStart_1962793 baseEnd_1962793 := by
    simpa [prefixWord, tailWord_1962793, baseEnd_1962793] using wordTrace_append hprefix tailTrace_1962793
  have hstable : (prefixWord ++ tailWord_1962793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962793).length < 2 ^ (prefixWord ++ tailWord_1962793).sum := by decide
  have hdescent : baseEnd_1962793 < baseStart_1962793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962800 : List Nat := [2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 4]
def baseStart_1962800 : Nat := 118140960795 + 1962800 * 2 ^ 59
def prefixEnd_1962800 : Nat := 4983230072969 + 3 ^ 40 * 1962800 * 2
def baseEnd_1962800 : Nat := 1007859828645025769673253

theorem tailTrace_1962800 : CollatzResearch.WordTrace tailWord_1962800 prefixEnd_1962800 1007859828645025769673253 := by
  unfold tailWord_1962800
  simp only [CollatzResearch.WordTrace]
  refine ⟨35794598644559147198458927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47726131526078862931278569 35794598644559147198458927)
  ·
    refine ⟨53691897966838720797688391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35794598644559147198458927 53691897966838720797688391)
    ·
      refine ⟨80537846950258081196532587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53691897966838720797688391 80537846950258081196532587)
      ·
        refine ⟨120806770425387121794798881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80537846950258081196532587 120806770425387121794798881)
        ·
          refine ⟨90605077819040341346099161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120806770425387121794798881 90605077819040341346099161)
          ·
            refine ⟨67953808364280256009574371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90605077819040341346099161 67953808364280256009574371)
            ·
              refine ⟨101930712546420384014361557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67953808364280256009574371 101930712546420384014361557)
              ·
                refine ⟨2389001075306727750336599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 101930712546420384014361557 2389001075306727750336599)
                ·
                  refine ⟨3583501612960091625504899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2389001075306727750336599 3583501612960091625504899)
                  ·
                    refine ⟨5375252419440137438257349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3583501612960091625504899 5375252419440137438257349)
                    ·
                      refine ⟨1007859828645025769673253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5375252419440137438257349 1007859828645025769673253)
                      ·
                        rfl

theorem cell23_1962800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 4].length) (baseStart_1962800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962800 prefixEnd_1962800 := by exact prefixLift 1962800
  have htrace : WordTrace (prefixWord ++ tailWord_1962800) baseStart_1962800 baseEnd_1962800 := by
    simpa [prefixWord, tailWord_1962800, baseEnd_1962800] using wordTrace_append hprefix tailTrace_1962800
  have hstable : (prefixWord ++ tailWord_1962800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962800).length < 2 ^ (prefixWord ++ tailWord_1962800).sum := by decide
  have hdescent : baseEnd_1962800 < baseStart_1962800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962834 : List Nat := [3, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2]
def baseStart_1962834 : Nat := 118140960795 + 1962834 * 2 ^ 59
def prefixEnd_1962834 : Nat := 4983230072969 + 3 ^ 40 * 1962834 * 2
def baseEnd_1962834 : Nat := 1007877286987278636648097

theorem tailTrace_1962834 : CollatzResearch.WordTrace tailWord_1962834 prefixEnd_1962834 1007877286987278636648097 := by
  unfold tailWord_1962834
  simp only [CollatzResearch.WordTrace]
  refine ⟨17897609342748779550913889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47726958247330078802437037 17897609342748779550913889)
  ·
    refine ⟨13423207007061584663185417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17897609342748779550913889 13423207007061584663185417)
    ·
      refine ⟨10067405255296188497389063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13423207007061584663185417 10067405255296188497389063)
      ·
        refine ⟨15101107882944282746083595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10067405255296188497389063 15101107882944282746083595)
        ·
          refine ⟨22651661824416424119125393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15101107882944282746083595 22651661824416424119125393)
          ·
            refine ⟨16988746368312318089344045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22651661824416424119125393 16988746368312318089344045)
            ·
              refine ⟨6370779888117119283504017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16988746368312318089344045 6370779888117119283504017)
              ·
                refine ⟨4778084916087839462628013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6370779888117119283504017 4778084916087839462628013)
                ·
                  refine ⟨1791781843532939798485505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4778084916087839462628013 1791781843532939798485505)
                  ·
                    refine ⟨1343836382649704848864129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1791781843532939798485505 1343836382649704848864129)
                    ·
                      refine ⟨1007877286987278636648097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1343836382649704848864129 1007877286987278636648097)
                      ·
                        rfl

theorem cell23_1962834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_1962834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962834 prefixEnd_1962834 := by exact prefixLift 1962834
  have htrace : WordTrace (prefixWord ++ tailWord_1962834) baseStart_1962834 baseEnd_1962834 := by
    simpa [prefixWord, tailWord_1962834, baseEnd_1962834] using wordTrace_append hprefix tailTrace_1962834
  have hstable : (prefixWord ++ tailWord_1962834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962834).length < 2 ^ (prefixWord ++ tailWord_1962834).sum := by decide
  have hdescent : baseEnd_1962834 < baseStart_1962834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962837 : List Nat := [1, 3, 2, 2, 2, 1, 2, 4, 1, 2, 3]
def baseStart_1962837 : Nat := 118140960795 + 1962837 * 2 ^ 59
def prefixEnd_1962837 : Nat := 4983230072969 + 3 ^ 40 * 1962837 * 2
def baseEnd_1962837 : Nat := 1007878827429242124910583

theorem tailTrace_1962837 : CollatzResearch.WordTrace tailWord_1962837 prefixEnd_1962837 1007878827429242124910583 := by
  unfold tailWord_1962837
  simp only [CollatzResearch.WordTrace]
  refine ⟨71590546789984249716014765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47727031193322833144009843 71590546789984249716014765)
  ·
    refine ⟨26846455046244093643505537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71590546789984249716014765 26846455046244093643505537)
    ·
      refine ⟨20134841284683070232629153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26846455046244093643505537 20134841284683070232629153)
      ·
        refine ⟨15101130963512302674471865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20134841284683070232629153 15101130963512302674471865)
        ·
          refine ⟨11325848222634227005853899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15101130963512302674471865 11325848222634227005853899)
          ·
            refine ⟨16988772333951340508780849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11325848222634227005853899 16988772333951340508780849)
            ·
              refine ⟨12741579250463505381585637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16988772333951340508780849 12741579250463505381585637)
              ·
                refine ⟨2389046109461907259047307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12741579250463505381585637 2389046109461907259047307)
                ·
                  refine ⟨3583569164192860888570961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2389046109461907259047307 3583569164192860888570961)
                  ·
                    refine ⟨2687676873144645666428221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3583569164192860888570961 2687676873144645666428221)
                    ·
                      refine ⟨1007878827429242124910583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2687676873144645666428221 1007878827429242124910583)
                      ·
                        rfl

theorem cell23_1962837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_1962837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962837 prefixEnd_1962837 := by exact prefixLift 1962837
  have htrace : WordTrace (prefixWord ++ tailWord_1962837) baseStart_1962837 baseEnd_1962837 := by
    simpa [prefixWord, tailWord_1962837, baseEnd_1962837] using wordTrace_append hprefix tailTrace_1962837
  have hstable : (prefixWord ++ tailWord_1962837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962837).length < 2 ^ (prefixWord ++ tailWord_1962837).sum := by decide
  have hdescent : baseEnd_1962837 < baseStart_1962837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962851 : List Nat := [1, 1, 1, 5, 3, 1, 1, 5, 1, 2, 2]
def baseStart_1962851 : Nat := 118140960795 + 1962851 * 2 ^ 59
def prefixEnd_1962851 : Nat := 4983230072969 + 3 ^ 40 * 1962851 * 2
def baseEnd_1962851 : Nat := 1007886016158405070135519

theorem tailTrace_1962851 : CollatzResearch.WordTrace tailWord_1962851 prefixEnd_1962851 1007886016158405070135519 := by
  unfold tailWord_1962851
  simp only [CollatzResearch.WordTrace]
  refine ⟨71591057411933530107024407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47727371607955686738016271 71591057411933530107024407)
  ·
    refine ⟨107386586117900295160536611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71591057411933530107024407 107386586117900295160536611)
    ·
      refine ⟨161079879176850442740804917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107386586117900295160536611 161079879176850442740804917)
      ·
        refine ⟨15101238672829729006950461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161079879176850442740804917 15101238672829729006950461)
        ·
          refine ⟨5662964502311148377606423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15101238672829729006950461 5662964502311148377606423)
          ·
            refine ⟨8494446753466722566409635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5662964502311148377606423 8494446753466722566409635)
            ·
              refine ⟨12741670130200083849614453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8494446753466722566409635 12741670130200083849614453)
              ·
                refine ⟨1194531574706257860901355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12741670130200083849614453 1194531574706257860901355)
                ·
                  refine ⟨1791797362059386791352033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1194531574706257860901355 1791797362059386791352033)
                  ·
                    refine ⟨1343848021544540093514025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1791797362059386791352033 1343848021544540093514025)
                    ·
                      refine ⟨1007886016158405070135519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1343848021544540093514025 1007886016158405070135519)
                      ·
                        rfl

theorem cell23_1962851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_1962851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962851 prefixEnd_1962851 := by exact prefixLift 1962851
  have htrace : WordTrace (prefixWord ++ tailWord_1962851) baseStart_1962851 baseEnd_1962851 := by
    simpa [prefixWord, tailWord_1962851, baseEnd_1962851] using wordTrace_append hprefix tailTrace_1962851
  have hstable : (prefixWord ++ tailWord_1962851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962851).length < 2 ^ (prefixWord ++ tailWord_1962851).sum := by decide
  have hdescent : baseEnd_1962851 < baseStart_1962851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962877 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 5, 3, 2]
def baseStart_1962877 : Nat := 118140960795 + 1962877 * 2 ^ 59
def prefixEnd_1962877 : Nat := 4983230072969 + 3 ^ 40 * 1962877 * 2
def baseEnd_1962877 : Nat := 1007899366655421968410399

theorem tailTrace_1962877 : CollatzResearch.WordTrace tailWord_1962877 prefixEnd_1962877 1007899366655421968410399 := by
  unfold tailWord_1962877
  simp only [CollatzResearch.WordTrace]
  refine ⟨71592005709839336547470885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47728003806559557698313923 71592005709839336547470885)
  ·
    refine ⟨13423501070594875602650791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71592005709839336547470885 13423501070594875602650791)
    ·
      refine ⟨20135251605892313403976187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13423501070594875602650791 20135251605892313403976187)
      ·
        refine ⟨30202877408838470105964281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20135251605892313403976187 30202877408838470105964281)
        ·
          refine ⟨22652158056628852579473211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30202877408838470105964281 22652158056628852579473211)
          ·
            refine ⟨33978237084943278869209817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22652158056628852579473211 33978237084943278869209817)
            ·
              refine ⟨25483677813707459151907363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33978237084943278869209817 25483677813707459151907363)
              ·
                refine ⟨38225516720561188727861045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25483677813707459151907363 38225516720561188727861045)
                ·
                  refine ⟨3583642192552611443236973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38225516720561188727861045 3583642192552611443236973)
                  ·
                    refine ⟨1343865822207229291213865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3583642192552611443236973 1343865822207229291213865)
                    ·
                      refine ⟨1007899366655421968410399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1343865822207229291213865 1007899366655421968410399)
                      ·
                        rfl

theorem cell23_1962877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 3, 2].length) (baseStart_1962877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962877 prefixEnd_1962877 := by exact prefixLift 1962877
  have htrace : WordTrace (prefixWord ++ tailWord_1962877) baseStart_1962877 baseEnd_1962877 := by
    simpa [prefixWord, tailWord_1962877, baseEnd_1962877] using wordTrace_append hprefix tailTrace_1962877
  have hstable : (prefixWord ++ tailWord_1962877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962877).length < 2 ^ (prefixWord ++ tailWord_1962877).sum := by decide
  have hdescent : baseEnd_1962877 < baseStart_1962877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962878 : List Nat := [4, 2, 3, 1, 2, 1, 3, 1, 2, 4]
def baseStart_1962878 : Nat := 118140960795 + 1962878 * 2 ^ 59
def prefixEnd_1962878 : Nat := 4983230072969 + 3 ^ 40 * 1962878 * 2
def baseEnd_1962878 : Nat := 335966626712025488165965

theorem tailTrace_1962878 : CollatzResearch.WordTrace tailWord_1962878 prefixEnd_1962878 335966626712025488165965 := by
  unfold tailWord_1962878
  simp only [CollatzResearch.WordTrace]
  refine ⟨8949005272854464214782161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47728028121890475812171525 8949005272854464214782161)
  ·
    refine ⟨6711753954640848161086621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8949005272854464214782161 6711753954640848161086621)
    ·
      refine ⟨2516907732990318060407483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6711753954640848161086621 2516907732990318060407483)
      ·
        refine ⟨3775361599485477090611225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2516907732990318060407483 3775361599485477090611225)
        ·
          refine ⟨2831521199614107817958419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3775361599485477090611225 2831521199614107817958419)
          ·
            refine ⟨4247281799421161726937629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2831521199614107817958419 4247281799421161726937629)
            ·
              refine ⟨1592730674782935647601611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4247281799421161726937629 1592730674782935647601611)
              ·
                refine ⟨2389096012174403471402417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1592730674782935647601611 2389096012174403471402417)
                ·
                  refine ⟨1791822009130802603551813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2389096012174403471402417 1791822009130802603551813)
                  ·
                    refine ⟨335966626712025488165965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1791822009130802603551813 335966626712025488165965)
                    ·
                      rfl

theorem cell23_1962878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_1962878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962878 prefixEnd_1962878 := by exact prefixLift 1962878
  have htrace : WordTrace (prefixWord ++ tailWord_1962878) baseStart_1962878 baseEnd_1962878 := by
    simpa [prefixWord, tailWord_1962878, baseEnd_1962878] using wordTrace_append hprefix tailTrace_1962878
  have hstable : (prefixWord ++ tailWord_1962878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962878).length < 2 ^ (prefixWord ++ tailWord_1962878).sum := by decide
  have hdescent : baseEnd_1962878 < baseStart_1962878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962902 : List Nat := [5, 3, 1, 1, 1, 1, 3, 3, 1, 2, 2]
def baseStart_1962902 : Nat := 118140960795 + 1962902 * 2 ^ 59
def prefixEnd_1962902 : Nat := 4983230072969 + 3 ^ 40 * 1962902 * 2
def baseEnd_1962902 : Nat := 1007912203671784370597785

theorem tailTrace_1962902 : CollatzResearch.WordTrace tailWord_1962902 prefixEnd_1962902 1007912203671784370597785 := by
  unfold tailWord_1962902
  simp only [CollatzResearch.WordTrace]
  refine ⟨4474557345921797863570685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47728611689832510544753973 4474557345921797863570685)
  ·
    refine ⟨1677959004720674198839007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4474557345921797863570685 1677959004720674198839007)
    ·
      refine ⟨2516938507081011298258511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1677959004720674198839007 2516938507081011298258511)
      ·
        refine ⟨3775407760621516947387767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2516938507081011298258511 3775407760621516947387767)
        ·
          refine ⟨5663111640932275421081651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3775407760621516947387767 5663111640932275421081651)
          ·
            refine ⟨8494667461398413131622477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5663111640932275421081651 8494667461398413131622477)
            ·
              refine ⟨3185500298024404924358429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8494667461398413131622477 3185500298024404924358429)
              ·
                refine ⟨1194562611759151846634411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3185500298024404924358429 1194562611759151846634411)
                ·
                  refine ⟨1791843917638727769951617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1194562611759151846634411 1791843917638727769951617)
                  ·
                    refine ⟨1343882938229045827463713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1791843917638727769951617 1343882938229045827463713)
                    ·
                      refine ⟨1007912203671784370597785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1343882938229045827463713 1007912203671784370597785)
                      ·
                        rfl

theorem cell23_1962902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_1962902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962902 prefixEnd_1962902 := by exact prefixLift 1962902
  have htrace : WordTrace (prefixWord ++ tailWord_1962902) baseStart_1962902 baseEnd_1962902 := by
    simpa [prefixWord, tailWord_1962902, baseEnd_1962902] using wordTrace_append hprefix tailTrace_1962902
  have hstable : (prefixWord ++ tailWord_1962902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962902).length < 2 ^ (prefixWord ++ tailWord_1962902).sum := by decide
  have hdescent : baseEnd_1962902 < baseStart_1962902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962981 : List Nat := [1, 3, 1, 6, 1, 1, 1, 4, 5]
def baseStart_1962981 : Nat := 118140960795 + 1962981 * 2 ^ 59
def prefixEnd_1962981 : Nat := 4983230072969 + 3 ^ 40 * 1962981 * 2
def baseEnd_1962981 : Nat := 111994752071498840167769

theorem tailTrace_1962981 : CollatzResearch.WordTrace tailWord_1962981 prefixEnd_1962981 111994752071498840167769 := by
  unfold tailWord_1962981
  simp only [CollatzResearch.WordTrace]
  refine ⟨71595798901462562309256797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47730532600975041539504531 71595798901462562309256797)
  ·
    refine ⟨26848424588048460865971299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71595798901462562309256797 26848424588048460865971299)
    ·
      refine ⟨40272636882072691298956949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26848424588048460865971299 40272636882072691298956949)
      ·
        refine ⟨1887779853847157404638607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40272636882072691298956949 1887779853847157404638607)
        ·
          refine ⟨2831669780770736106957911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1887779853847157404638607 2831669780770736106957911)
          ·
            refine ⟨4247504671156104160436867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2831669780770736106957911 4247504671156104160436867)
            ·
              refine ⟨6371257006734156240655301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4247504671156104160436867 6371257006734156240655301)
              ·
                refine ⟨1194610688762654295122869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6371257006734156240655301 1194610688762654295122869)
                ·
                  refine ⟨111994752071498840167769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1194610688762654295122869 111994752071498840167769)
                  ·
                    rfl

theorem cell23_1962981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 4, 5].length) (baseStart_1962981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1962981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1962981 prefixEnd_1962981 := by exact prefixLift 1962981
  have htrace : WordTrace (prefixWord ++ tailWord_1962981) baseStart_1962981 baseEnd_1962981 := by
    simpa [prefixWord, tailWord_1962981, baseEnd_1962981] using wordTrace_append hprefix tailTrace_1962981
  have hstable : (prefixWord ++ tailWord_1962981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962981).length < 2 ^ (prefixWord ++ tailWord_1962981).sum := by decide
  have hdescent : baseEnd_1962981 < baseStart_1962981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963041 : List Nat := [1, 2, 3, 2, 3, 1, 2, 4, 1, 4]
def baseStart_1963041 : Nat := 118140960795 + 1963041 * 2 ^ 59
def prefixEnd_1963041 : Nat := 4983230072969 + 3 ^ 40 * 1963041 * 2
def baseEnd_1963041 : Nat := 335994525827586442253215

theorem tailTrace_1963041 : CollatzResearch.WordTrace tailWord_1963041 prefixEnd_1963041 335994525827586442253215 := by
  unfold tailWord_1963041
  simp only [CollatzResearch.WordTrace]
  refine ⟨71597987281245192556440977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47731991520830128370960651 71597987281245192556440977)
  ·
    refine ⟨53698490460933894417330733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71597987281245192556440977 53698490460933894417330733)
    ·
      refine ⟨20136933922850210406499025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53698490460933894417330733 20136933922850210406499025)
      ·
        refine ⟨15102700442137657804874269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20136933922850210406499025 15102700442137657804874269)
        ·
          refine ⟨5663512665801621676827851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15102700442137657804874269 5663512665801621676827851)
          ·
            refine ⟨8495268998702432515241777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5663512665801621676827851 8495268998702432515241777)
            ·
              refine ⟨6371451749026824386431333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8495268998702432515241777 6371451749026824386431333)
              ·
                refine ⟨1194647202942529572455875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6371451749026824386431333 1194647202942529572455875)
                ·
                  refine ⟨1791970804413794358683813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1194647202942529572455875 1791970804413794358683813)
                  ·
                    refine ⟨335994525827586442253215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1791970804413794358683813 335994525827586442253215)
                    ·
                      rfl

theorem cell23_1963041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_1963041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963041 prefixEnd_1963041 := by exact prefixLift 1963041
  have htrace : WordTrace (prefixWord ++ tailWord_1963041) baseStart_1963041 baseEnd_1963041 := by
    simpa [prefixWord, tailWord_1963041, baseEnd_1963041] using wordTrace_append hprefix tailTrace_1963041
  have hstable : (prefixWord ++ tailWord_1963041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963041).length < 2 ^ (prefixWord ++ tailWord_1963041).sum := by decide
  have hdescent : baseEnd_1963041 < baseStart_1963041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963081 : List Nat := [1, 2, 1, 1, 2, 2, 2, 7, 1, 1, 3]
def baseStart_1963081 : Nat := 118140960795 + 1963081 * 2 ^ 59
def prefixEnd_1963081 : Nat := 4983230072969 + 3 ^ 40 * 1963081 * 2
def baseEnd_1963081 : Nat := 1008004116708939170259461

theorem tailTrace_1963081 : CollatzResearch.WordTrace tailWord_1963081 prefixEnd_1963081 1008004116708939170259461 := by
  unfold tailWord_1963081
  simp only [CollatzResearch.WordTrace]
  refine ⟨71599446201100279387897097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47732964134066852925264731 71599446201100279387897097)
  ·
    refine ⟨53699584650825209540922823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71599446201100279387897097 53699584650825209540922823)
    ·
      refine ⟨80549376976237814311384235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53699584650825209540922823 80549376976237814311384235)
      ·
        refine ⟨120824065464356721467076353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80549376976237814311384235 120824065464356721467076353)
        ·
          refine ⟨90618049098267541100307265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120824065464356721467076353 90618049098267541100307265)
          ·
            refine ⟨67963536823700655825230449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90618049098267541100307265 67963536823700655825230449)
            ·
              refine ⟨50972652617775491868922837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67963536823700655825230449 50972652617775491868922837)
              ·
                refine ⟨1194671545729113090677879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 50972652617775491868922837 1194671545729113090677879)
                ·
                  refine ⟨1792007318593669636016819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1194671545729113090677879 1792007318593669636016819)
                  ·
                    refine ⟨2688010977890504454025229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1792007318593669636016819 2688010977890504454025229)
                    ·
                      refine ⟨1008004116708939170259461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2688010977890504454025229 1008004116708939170259461)
                      ·
                        rfl

theorem cell23_1963081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 7, 1, 1, 3].length) (baseStart_1963081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963081 prefixEnd_1963081 := by exact prefixLift 1963081
  have htrace : WordTrace (prefixWord ++ tailWord_1963081) baseStart_1963081 baseEnd_1963081 := by
    simpa [prefixWord, tailWord_1963081, baseEnd_1963081] using wordTrace_append hprefix tailTrace_1963081
  have hstable : (prefixWord ++ tailWord_1963081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963081).length < 2 ^ (prefixWord ++ tailWord_1963081).sum := by decide
  have hdescent : baseEnd_1963081 < baseStart_1963081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963107 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 2, 6, 3]
def baseStart_1963107 : Nat := 118140960795 + 1963107 * 2 ^ 59
def prefixEnd_1963107 : Nat := 4983230072969 + 3 ^ 40 * 1963107 * 2
def baseEnd_1963107 : Nat := 1008017467205956068534341

theorem tailTrace_1963107 : CollatzResearch.WordTrace tailWord_1963107 prefixEnd_1963107 1008017467205956068534341 := by
  unfold tailWord_1963107
  simp only [CollatzResearch.WordTrace]
  refine ⟨71600394499006085828343575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47733596332670723885562383 71600394499006085828343575)
  ·
    refine ⟨107400591748509128742515363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71600394499006085828343575 107400591748509128742515363)
    ·
      refine ⟨161100887622763693113773045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107400591748509128742515363 161100887622763693113773045)
      ·
        refine ⟨15103208214634096229416223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161100887622763693113773045 15103208214634096229416223)
        ·
          refine ⟨22654812321951144344124335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15103208214634096229416223 22654812321951144344124335)
          ·
            refine ⟨33982218482926716516186503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22654812321951144344124335 33982218482926716516186503)
            ·
              refine ⟨50973327724390074774279755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33982218482926716516186503 50973327724390074774279755)
              ·
                refine ⟨76459991586585112161419633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50973327724390074774279755 76459991586585112161419633)
                ·
                  refine ⟨57344993689938834121064725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76459991586585112161419633 57344993689938834121064725)
                  ·
                    refine ⟨2688046579215882849424909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57344993689938834121064725 2688046579215882849424909)
                    ·
                      refine ⟨1008017467205956068534341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2688046579215882849424909 1008017467205956068534341)
                      ·
                        rfl

theorem cell23_1963107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_1963107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963107 prefixEnd_1963107 := by exact prefixLift 1963107
  have htrace : WordTrace (prefixWord ++ tailWord_1963107) baseStart_1963107 baseEnd_1963107 := by
    simpa [prefixWord, tailWord_1963107, baseEnd_1963107] using wordTrace_append hprefix tailTrace_1963107
  have hstable : (prefixWord ++ tailWord_1963107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963107).length < 2 ^ (prefixWord ++ tailWord_1963107).sum := by decide
  have hdescent : baseEnd_1963107 < baseStart_1963107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963125 : List Nat := [1, 3, 4, 3, 1, 1, 2, 1, 2, 3, 2]
def baseStart_1963125 : Nat := 118140960795 + 1963125 * 2 ^ 59
def prefixEnd_1963125 : Nat := 4983230072969 + 3 ^ 40 * 1963125 * 2
def baseEnd_1963125 : Nat := 1008026709857736998109259

theorem tailTrace_1963125 : CollatzResearch.WordTrace tailWord_1963125 prefixEnd_1963125 1008026709857736998109259 := by
  unfold tailWord_1963125
  simp only [CollatzResearch.WordTrace]
  refine ⟨71601051012940874902498829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47734034008627249934999219 71601051012940874902498829)
  ·
    refine ⟨26850394129852828088437061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71601051012940874902498829 26850394129852828088437061)
    ·
      refine ⟨5034448899347405266581949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26850394129852828088437061 5034448899347405266581949)
      ·
        refine ⟨1887918337255276974968231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5034448899347405266581949 1887918337255276974968231)
        ·
          refine ⟨2831877505882915462452347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1887918337255276974968231 2831877505882915462452347)
          ·
            refine ⟨4247816258824373193678521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2831877505882915462452347 4247816258824373193678521)
            ·
              refine ⟨3185862194118279895258891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4247816258824373193678521 3185862194118279895258891)
              ·
                refine ⟨4778793291177419842888337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3185862194118279895258891 4778793291177419842888337)
                ·
                  refine ⟨3584094968383064882166253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4778793291177419842888337 3584094968383064882166253)
                  ·
                    refine ⟨1344035613143649330812345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3584094968383064882166253 1344035613143649330812345)
                    ·
                      refine ⟨1008026709857736998109259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1344035613143649330812345 1008026709857736998109259)
                      ·
                        rfl

theorem cell23_1963125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_1963125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963125 prefixEnd_1963125 := by exact prefixLift 1963125
  have htrace : WordTrace (prefixWord ++ tailWord_1963125) baseStart_1963125 baseEnd_1963125 := by
    simpa [prefixWord, tailWord_1963125, baseEnd_1963125] using wordTrace_append hprefix tailTrace_1963125
  have hstable : (prefixWord ++ tailWord_1963125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963125).length < 2 ^ (prefixWord ++ tailWord_1963125).sum := by decide
  have hdescent : baseEnd_1963125 < baseStart_1963125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963141 : List Nat := [1, 3, 1, 1, 6, 2, 1, 1, 1, 1, 5]
def baseStart_1963141 : Nat := 118140960795 + 1963141 * 2 ^ 59
def prefixEnd_1963141 : Nat := 4983230072969 + 3 ^ 40 * 1963141 * 2
def baseEnd_1963141 : Nat := 1008034925548208935509185

theorem tailTrace_1963141 : CollatzResearch.WordTrace tailWord_1963141 prefixEnd_1963141 1008034925548208935509185 := by
  unfold tailWord_1963141
  simp only [CollatzResearch.WordTrace]
  refine ⟨71601634580882909635081277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47734423053921939756720851 71601634580882909635081277)
  ·
    refine ⟨26850612967831091113155479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71601634580882909635081277 26850612967831091113155479)
    ·
      refine ⟨40275919451746636669733219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26850612967831091113155479 40275919451746636669733219)
      ·
        refine ⟨60413879177619955004599829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40275919451746636669733219 60413879177619955004599829)
        ·
          refine ⟨2831900586450935390840617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 60413879177619955004599829 2831900586450935390840617)
          ·
            refine ⟨2123925439838201543130463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2831900586450935390840617 2123925439838201543130463)
            ·
              refine ⟨3185888159757302314695695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2123925439838201543130463 3185888159757302314695695)
              ·
                refine ⟨4778832239635953472043543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3185888159757302314695695 4778832239635953472043543)
                ·
                  refine ⟨7168248359453930208065315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4778832239635953472043543 7168248359453930208065315)
                  ·
                    refine ⟨10752372539180895312097973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7168248359453930208065315 10752372539180895312097973)
                    ·
                      refine ⟨1008034925548208935509185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10752372539180895312097973 1008034925548208935509185)
                      ·
                        rfl

theorem cell23_1963141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 1, 5].length) (baseStart_1963141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963141 prefixEnd_1963141 := by exact prefixLift 1963141
  have htrace : WordTrace (prefixWord ++ tailWord_1963141) baseStart_1963141 baseEnd_1963141 := by
    simpa [prefixWord, tailWord_1963141, baseEnd_1963141] using wordTrace_append hprefix tailTrace_1963141
  have hstable : (prefixWord ++ tailWord_1963141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963141).length < 2 ^ (prefixWord ++ tailWord_1963141).sum := by decide
  have hdescent : baseEnd_1963141 < baseStart_1963141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963144 : List Nat := [2, 1, 3, 4, 3, 10]
def baseStart_1963144 : Nat := 118140960795 + 1963144 * 2 ^ 59
def prefixEnd_1963144 : Nat := 4983230072969 + 3 ^ 40 * 1963144 * 2
def baseEnd_1963144 : Nat := 4148298213951326846797

theorem tailTrace_1963144 : CollatzResearch.WordTrace tailWord_1963144 prefixEnd_1963144 4148298213951326846797 := by
  unfold tailWord_1963144
  simp only [CollatzResearch.WordTrace]
  refine ⟨35800871999936020573720243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47734495999914694098293657 35800871999936020573720243)
  ·
    refine ⟨53701307999904030860580365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35800871999936020573720243 53701307999904030860580365)
    ·
      refine ⟨20137990499964011572717637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53701307999904030860580365 20137990499964011572717637)
      ·
        refine ⟨3775873218743252169884557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20137990499964011572717637 3775873218743252169884557)
        ·
          refine ⟨1415952457028719563706709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3775873218743252169884557 1415952457028719563706709)
          ·
            refine ⟨4148298213951326846797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1415952457028719563706709 4148298213951326846797)
            ·
              rfl

theorem cell23_1963144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 10].length) (baseStart_1963144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963144 prefixEnd_1963144 := by exact prefixLift 1963144
  have htrace : WordTrace (prefixWord ++ tailWord_1963144) baseStart_1963144 baseEnd_1963144 := by
    simpa [prefixWord, tailWord_1963144, baseEnd_1963144] using wordTrace_append hprefix tailTrace_1963144
  have hstable : (prefixWord ++ tailWord_1963144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963144).length < 2 ^ (prefixWord ++ tailWord_1963144).sum := by decide
  have hdescent : baseEnd_1963144 < baseStart_1963144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963155 : List Nat := [1, 1, 1, 2, 1, 2, 8, 2, 1, 2, 2]
def baseStart_1963155 : Nat := 118140960795 + 1963155 * 2 ^ 59
def prefixEnd_1963155 : Nat := 4983230072969 + 3 ^ 40 * 1963155 * 2
def baseEnd_1963155 : Nat := 1008042114277371880734121

theorem tailTrace_1963155 : CollatzResearch.WordTrace tailWord_1963155 prefixEnd_1963155 1008042114277371880734121 := by
  unfold tailWord_1963155
  simp only [CollatzResearch.WordTrace]
  refine ⟨71602145202832190026090919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47734763468554793350727279 71602145202832190026090919)
  ·
    refine ⟨107403217804248285039136379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71602145202832190026090919 107403217804248285039136379)
    ·
      refine ⟨161104826706372427558704569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107403217804248285039136379 161104826706372427558704569)
      ·
        refine ⟨120828620029779320669028427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161104826706372427558704569 120828620029779320669028427)
        ·
          refine ⟨181242930044668981003542641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120828620029779320669028427 181242930044668981003542641)
          ·
            refine ⟨135932197533501735752656981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181242930044668981003542641 135932197533501735752656981)
            ·
              refine ⟨1592955439845723465851449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 135932197533501735752656981 1592955439845723465851449)
              ·
                refine ⟨1194716579884292599388587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1592955439845723465851449 1194716579884292599388587)
                ·
                  refine ⟨1792074869826438899082881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1194716579884292599388587 1792074869826438899082881)
                  ·
                    refine ⟨1344056152369829174312161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1792074869826438899082881 1344056152369829174312161)
                    ·
                      refine ⟨1008042114277371880734121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1344056152369829174312161 1008042114277371880734121)
                      ·
                        rfl

theorem cell23_1963155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 2, 1, 2, 2].length) (baseStart_1963155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963155 prefixEnd_1963155 := by exact prefixLift 1963155
  have htrace : WordTrace (prefixWord ++ tailWord_1963155) baseStart_1963155 baseEnd_1963155 := by
    simpa [prefixWord, tailWord_1963155, baseEnd_1963155] using wordTrace_append hprefix tailTrace_1963155
  have hstable : (prefixWord ++ tailWord_1963155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963155).length < 2 ^ (prefixWord ++ tailWord_1963155).sum := by decide
  have hdescent : baseEnd_1963155 < baseStart_1963155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963222 : List Nat := [5, 2, 1, 2, 3, 1, 1, 1, 1, 3, 3]
def baseStart_1963222 : Nat := 118140960795 + 1963222 * 2 ^ 59
def prefixEnd_1963222 : Nat := 4983230072969 + 3 ^ 40 * 1963222 * 2
def baseEnd_1963222 : Nat := 1008076517481223118596313

theorem tailTrace_1963222 : CollatzResearch.WordTrace tailWord_1963222 prefixEnd_1963222 1008076517481223118596313 := by
  unfold tailWord_1963222
  simp only [CollatzResearch.WordTrace]
  refine ⟨4475286805849341279298745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47736392595726306979186613 4475286805849341279298745)
  ·
    refine ⟨3356465104387005959474059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4475286805849341279298745 3356465104387005959474059)
    ·
      refine ⟨5034697656580508939211089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3356465104387005959474059 5034697656580508939211089)
      ·
        refine ⟨3776023242435381704408317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5034697656580508939211089 3776023242435381704408317)
        ·
          refine ⟨1416008715913268139153119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3776023242435381704408317 1416008715913268139153119)
          ·
            refine ⟨2124013073869902208729679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1416008715913268139153119 2124013073869902208729679)
            ·
              refine ⟨3186019610804853313094519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2124013073869902208729679 3186019610804853313094519)
              ·
                refine ⟨4779029416207279969641779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3186019610804853313094519 4779029416207279969641779)
                ·
                  refine ⟨7168544124310919954462669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4779029416207279969641779 7168544124310919954462669)
                  ·
                    refine ⟨2688204046616594982923501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7168544124310919954462669 2688204046616594982923501)
                    ·
                      refine ⟨1008076517481223118596313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2688204046616594982923501 1008076517481223118596313)
                      ·
                        rfl

theorem cell23_1963222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_1963222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963222 prefixEnd_1963222 := by exact prefixLift 1963222
  have htrace : WordTrace (prefixWord ++ tailWord_1963222) baseStart_1963222 baseEnd_1963222 := by
    simpa [prefixWord, tailWord_1963222, baseEnd_1963222] using wordTrace_append hprefix tailTrace_1963222
  have hstable : (prefixWord ++ tailWord_1963222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963222).length < 2 ^ (prefixWord ++ tailWord_1963222).sum := by decide
  have hdescent : baseEnd_1963222 < baseStart_1963222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963251 : List Nat := [1, 1, 1, 2, 2, 5, 3, 3, 5]
def baseStart_1963251 : Nat := 118140960795 + 1963251 * 2 ^ 59
def prefixEnd_1963251 : Nat := 4983230072969 + 3 ^ 40 * 1963251 * 2
def baseEnd_1963251 : Nat := 112010156491133722792631

theorem tailTrace_1963251 : CollatzResearch.WordTrace tailWord_1963251 prefixEnd_1963251 112010156491133722792631 := by
  unfold tailWord_1963251
  simp only [CollatzResearch.WordTrace]
  refine ⟨71605646610484398421585607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47737097740322932281057071 71605646610484398421585607)
  ·
    refine ⟨107408469915726597632378411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71605646610484398421585607 107408469915726597632378411)
    ·
      refine ⟨161112704873589896448567617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107408469915726597632378411 161112704873589896448567617)
      ·
        refine ⟨120834528655192422336425713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161112704873589896448567617 120834528655192422336425713)
        ·
          refine ⟨90625896491394316752319285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120834528655192422336425713 90625896491394316752319285)
          ·
            refine ⟨8496177796068217195529933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90625896491394316752319285 8496177796068217195529933)
            ·
              refine ⟨3186066673525581448323725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8496177796068217195529933 3186066673525581448323725)
              ·
                refine ⟨1194775002572093043121397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3186066673525581448323725 1194775002572093043121397)
                ·
                  refine ⟨112010156491133722792631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1194775002572093043121397 112010156491133722792631)
                  ·
                    rfl

theorem cell23_1963251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 3, 5].length) (baseStart_1963251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963251 prefixEnd_1963251 := by exact prefixLift 1963251
  have htrace : WordTrace (prefixWord ++ tailWord_1963251) baseStart_1963251 baseEnd_1963251 := by
    simpa [prefixWord, tailWord_1963251, baseEnd_1963251] using wordTrace_append hprefix tailTrace_1963251
  have hstable : (prefixWord ++ tailWord_1963251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963251).length < 2 ^ (prefixWord ++ tailWord_1963251).sum := by decide
  have hdescent : baseEnd_1963251 < baseStart_1963251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963298 : List Nat := [3, 3, 1, 1, 4, 1, 2, 1, 2, 5]
def baseStart_1963298 : Nat := 118140960795 + 1963298 * 2 ^ 59
def prefixEnd_1963298 : Nat := 4983230072969 + 3 ^ 40 * 1963298 * 2
def baseEnd_1963298 : Nat := 336038514003654940415321

theorem tailTrace_1963298 : CollatzResearch.WordTrace tailWord_1963298 prefixEnd_1963298 336038514003654940415321 := by
  unfold tailWord_1963298
  simp only [CollatzResearch.WordTrace]
  refine ⟨17901840210328531362136637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47738240560876083632364365 17901840210328531362136637)
  ·
    refine ⟨6713190078873199260801239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17901840210328531362136637 6713190078873199260801239)
    ·
      refine ⟨10069785118309798891201859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6713190078873199260801239 10069785118309798891201859)
      ·
        refine ⟨15104677677464698336802789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10069785118309798891201859 15104677677464698336802789)
        ·
          refine ⟨2832127064524630938150523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15104677677464698336802789 2832127064524630938150523)
          ·
            refine ⟨4248190596786946407225785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2832127064524630938150523 4248190596786946407225785)
            ·
              refine ⟨3186142947590209805419339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4248190596786946407225785 3186142947590209805419339)
              ·
                refine ⟨4779214421385314708129009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3186142947590209805419339 4779214421385314708129009)
                ·
                  refine ⟨3584410816038986031096757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4779214421385314708129009 3584410816038986031096757)
                  ·
                    refine ⟨336038514003654940415321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3584410816038986031096757 336038514003654940415321)
                    ·
                      rfl

theorem cell23_1963298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_1963298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963298 prefixEnd_1963298 := by exact prefixLift 1963298
  have htrace : WordTrace (prefixWord ++ tailWord_1963298) baseStart_1963298 baseEnd_1963298 := by
    simpa [prefixWord, tailWord_1963298, baseEnd_1963298] using wordTrace_append hprefix tailTrace_1963298
  have hstable : (prefixWord ++ tailWord_1963298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963298).length < 2 ^ (prefixWord ++ tailWord_1963298).sum := by decide
  have hdescent : baseEnd_1963298 < baseStart_1963298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963301 : List Nat := [1, 3, 1, 2, 4, 1, 1, 3, 2, 1, 4]
def baseStart_1963301 : Nat := 118140960795 + 1963301 * 2 ^ 59
def prefixEnd_1963301 : Nat := 4983230072969 + 3 ^ 40 * 1963301 * 2
def baseEnd_1963301 : Nat := 1008117082452928309508449

theorem tailTrace_1963301 : CollatzResearch.WordTrace tailWord_1963301 prefixEnd_1963301 1008117082452928309508449 := by
  unfold tailWord_1963301
  simp only [CollatzResearch.WordTrace]
  refine ⟨71607470260303256960905757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47738313506868837973937171 71607470260303256960905757)
  ·
    refine ⟨26852801347613721360339659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71607470260303256960905757 26852801347613721360339659)
    ·
      refine ⟨40279202021420582040509489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26852801347613721360339659 40279202021420582040509489)
      ·
        refine ⟨30209401516065436530382117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40279202021420582040509489 30209401516065436530382117)
        ·
          refine ⟨5664262784262269349446647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30209401516065436530382117 5664262784262269349446647)
          ·
            refine ⟨8496394176393404024169971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5664262784262269349446647 8496394176393404024169971)
            ·
              refine ⟨12744591264590106036254957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8496394176393404024169971 12744591264590106036254957)
              ·
                refine ⟨4779221724221289763595609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12744591264590106036254957 4779221724221289763595609)
                ·
                  refine ⟨3584416293165967322696707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4779221724221289763595609 3584416293165967322696707)
                  ·
                    refine ⟨5376624439748950984045061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3584416293165967322696707 5376624439748950984045061)
                    ·
                      refine ⟨1008117082452928309508449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5376624439748950984045061 1008117082452928309508449)
                      ·
                        rfl

theorem cell23_1963301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_1963301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963301 prefixEnd_1963301 := by exact prefixLift 1963301
  have htrace : WordTrace (prefixWord ++ tailWord_1963301) baseStart_1963301 baseEnd_1963301 := by
    simpa [prefixWord, tailWord_1963301, baseEnd_1963301] using wordTrace_append hprefix tailTrace_1963301
  have hstable : (prefixWord ++ tailWord_1963301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963301).length < 2 ^ (prefixWord ++ tailWord_1963301).sum := by decide
  have hdescent : baseEnd_1963301 < baseStart_1963301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963328 : List Nat := [2, 1, 1, 2, 2, 1, 5, 4, 1, 4]
def baseStart_1963328 : Nat := 118140960795 + 1963328 * 2 ^ 59
def prefixEnd_1963328 : Nat := 4983230072969 + 3 ^ 40 * 1963328 * 2
def baseEnd_1963328 : Nat := 336043648810199901290275

theorem tailTrace_1963328 : CollatzResearch.WordTrace tailWord_1963328 prefixEnd_1963328 336043648810199901290275 := by
  unfold tailWord_1963328
  simp only [CollatzResearch.WordTrace]
  refine ⟨35804227515602720286069319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47738970020803627048092425 35804227515602720286069319)
  ·
    refine ⟨53706341273404080429103979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35804227515602720286069319 53706341273404080429103979)
    ·
      refine ⟨80559511910106120643655969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53706341273404080429103979 80559511910106120643655969)
      ·
        refine ⟨60419633932579590482741977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80559511910106120643655969 60419633932579590482741977)
        ·
          refine ⟨45314725449434692862056483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60419633932579590482741977 45314725449434692862056483)
          ·
            refine ⟨67972088174152039293084725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45314725449434692862056483 67972088174152039293084725)
            ·
              refine ⟨6372383266326753683726693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67972088174152039293084725 6372383266326753683726693)
              ·
                refine ⟨1194821862436266315698755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6372383266326753683726693 1194821862436266315698755)
                ·
                  refine ⟨1792232793654399473548133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1194821862436266315698755 1792232793654399473548133)
                  ·
                    refine ⟨336043648810199901290275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1792232793654399473548133 336043648810199901290275)
                    ·
                      rfl

theorem cell23_1963328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 4, 1, 4].length) (baseStart_1963328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963328 prefixEnd_1963328 := by exact prefixLift 1963328
  have htrace : WordTrace (prefixWord ++ tailWord_1963328) baseStart_1963328 baseEnd_1963328 := by
    simpa [prefixWord, tailWord_1963328, baseEnd_1963328] using wordTrace_append hprefix tailTrace_1963328
  have hstable : (prefixWord ++ tailWord_1963328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963328).length < 2 ^ (prefixWord ++ tailWord_1963328).sum := by decide
  have hdescent : baseEnd_1963328 < baseStart_1963328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963378 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 4, 3, 2]
def baseStart_1963378 : Nat := 118140960795 + 1963378 * 2 ^ 59
def prefixEnd_1963378 : Nat := 4983230072969 + 3 ^ 40 * 1963378 * 2
def baseEnd_1963378 : Nat := 1008156620463324508245595

theorem tailTrace_1963378 : CollatzResearch.WordTrace tailWord_1963378 prefixEnd_1963378 1008156620463324508245595 := by
  unfold tailWord_1963378
  simp only [CollatzResearch.WordTrace]
  refine ⟨17902569670256074777864697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47740185787349532740972525 17902569670256074777864697)
  ·
    refine ⟨13426927252692056083398523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17902569670256074777864697 13426927252692056083398523)
    ·
      refine ⟨20140390879038084125097785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13426927252692056083398523 20140390879038084125097785)
      ·
        refine ⟨15105293159278563093823339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20140390879038084125097785 15105293159278563093823339)
        ·
          refine ⟨22657939738917844640735009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15105293159278563093823339 22657939738917844640735009)
          ·
            refine ⟨16993454804188383480551257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22657939738917844640735009 16993454804188383480551257)
            ·
              refine ⟨12745091103141287610413443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16993454804188383480551257 12745091103141287610413443)
              ·
                refine ⟨19117636654711931415620165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12745091103141287610413443 19117636654711931415620165)
                ·
                  refine ⟨3584556872758487140428781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19117636654711931415620165 3584556872758487140428781)
                  ·
                    refine ⟨1344208827284432677660793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3584556872758487140428781 1344208827284432677660793)
                    ·
                      refine ⟨1008156620463324508245595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1344208827284432677660793 1008156620463324508245595)
                      ·
                        rfl

theorem cell23_1963378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_1963378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963378 prefixEnd_1963378 := by exact prefixLift 1963378
  have htrace : WordTrace (prefixWord ++ tailWord_1963378) baseStart_1963378 baseEnd_1963378 := by
    simpa [prefixWord, tailWord_1963378, baseEnd_1963378] using wordTrace_append hprefix tailTrace_1963378
  have hstable : (prefixWord ++ tailWord_1963378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963378).length < 2 ^ (prefixWord ++ tailWord_1963378).sum := by decide
  have hdescent : baseEnd_1963378 < baseStart_1963378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963385 : List Nat := [1, 2, 1, 3, 2, 1, 4, 4, 1, 1, 3]
def baseStart_1963385 : Nat := 118140960795 + 1963385 * 2 ^ 59
def prefixEnd_1963385 : Nat := 4983230072969 + 3 ^ 40 * 1963385 * 2
def baseEnd_1963385 : Nat := 1008160214827905980858063

theorem tailTrace_1963385 : CollatzResearch.WordTrace tailWord_1963385 prefixEnd_1963385 1008160214827905980858063 := by
  unfold tailWord_1963385
  simp only [CollatzResearch.WordTrace]
  refine ⟨71610533991998939306963609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47740355994665959537975739 71610533991998939306963609)
  ·
    refine ⟨53707900493999204480222707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71610533991998939306963609 53707900493999204480222707)
    ·
      refine ⟨80561850740998806720334061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53707900493999204480222707 80561850740998806720334061)
      ·
        refine ⟨30210694027874552520125273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80561850740998806720334061 30210694027874552520125273)
        ·
          refine ⟨22658020520905914390093955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30210694027874552520125273 22658020520905914390093955)
          ·
            refine ⟨33987030781358871585140933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22658020520905914390093955 33987030781358871585140933)
            ·
              refine ⟨6372568271504788422213925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33987030781358871585140933 6372568271504788422213925)
              ·
                refine ⟨1194856550907147829165111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6372568271504788422213925 1194856550907147829165111)
                ·
                  refine ⟨1792284826360721743747667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1194856550907147829165111 1792284826360721743747667)
                  ·
                    refine ⟨2688427239541082615621501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1792284826360721743747667 2688427239541082615621501)
                    ·
                      refine ⟨1008160214827905980858063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2688427239541082615621501 1008160214827905980858063)
                      ·
                        rfl

theorem cell23_1963385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 4, 1, 1, 3].length) (baseStart_1963385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963385 prefixEnd_1963385 := by exact prefixLift 1963385
  have htrace : WordTrace (prefixWord ++ tailWord_1963385) baseStart_1963385 baseEnd_1963385 := by
    simpa [prefixWord, tailWord_1963385, baseEnd_1963385] using wordTrace_append hprefix tailTrace_1963385
  have hstable : (prefixWord ++ tailWord_1963385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963385).length < 2 ^ (prefixWord ++ tailWord_1963385).sum := by decide
  have hdescent : baseEnd_1963385 < baseStart_1963385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963391 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 4, 6, 2]
def baseStart_1963391 : Nat := 118140960795 + 1963391 * 2 ^ 59
def prefixEnd_1963391 : Nat := 4983230072969 + 3 ^ 40 * 1963391 * 2
def baseEnd_1963391 : Nat := 1008163295711832957383035

theorem tailTrace_1963391 : CollatzResearch.WordTrace tailWord_1963391 prefixEnd_1963391 1008163295711832957383035 := by
  unfold tailWord_1963391
  simp only [CollatzResearch.WordTrace]
  refine ⟨71610752829977202331682027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47740501886651468221121351 71610752829977202331682027)
  ·
    refine ⟨107416129244965803497523041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71610752829977202331682027 107416129244965803497523041)
    ·
      refine ⟨80562096933724352623142281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107416129244965803497523041 80562096933724352623142281)
      ·
        refine ⟨60421572700293264467356711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80562096933724352623142281 60421572700293264467356711)
        ·
          refine ⟨90632359050439896701035067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60421572700293264467356711 90632359050439896701035067)
          ·
            refine ⟨135948538575659845051552601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90632359050439896701035067 135948538575659845051552601)
            ·
              refine ⟨101961403931744883788664451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135948538575659845051552601 101961403931744883788664451)
              ·
                refine ⟨152942105897617325682996677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101961403931744883788664451 152942105897617325682996677)
                ·
                  refine ⟨28676644855803248565561877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152942105897617325682996677 28676644855803248565561877)
                  ·
                    refine ⟨1344217727615777276510713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28676644855803248565561877 1344217727615777276510713)
                    ·
                      refine ⟨1008163295711832957383035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1344217727615777276510713 1008163295711832957383035)
                      ·
                        rfl

theorem cell23_1963391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 6, 2].length) (baseStart_1963391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963391 prefixEnd_1963391 := by exact prefixLift 1963391
  have htrace : WordTrace (prefixWord ++ tailWord_1963391) baseStart_1963391 baseEnd_1963391 := by
    simpa [prefixWord, tailWord_1963391, baseEnd_1963391] using wordTrace_append hprefix tailTrace_1963391
  have hstable : (prefixWord ++ tailWord_1963391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963391).length < 2 ^ (prefixWord ++ tailWord_1963391).sum := by decide
  have hdescent : baseEnd_1963391 < baseStart_1963391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963548 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 4, 3, 3]
def baseStart_1963548 : Nat := 118140960795 + 1963548 * 2 ^ 59
def prefixEnd_1963548 : Nat := 4983230072969 + 3 ^ 40 * 1963548 * 2
def baseEnd_1963548 : Nat := 1008243912174588843119813

theorem tailTrace_1963548 : CollatzResearch.WordTrace tailWord_1963548 prefixEnd_1963548 1008243912174588843119813 := by
  unfold tailWord_1963548
  simp only [CollatzResearch.WordTrace]
  refine ⟨35808239545204209072573649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47744319393605612096764865 35808239545204209072573649)
  ·
    refine ⟨26856179658903156804430237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35808239545204209072573649 26856179658903156804430237)
    ·
      refine ⟨10071067372088683801661339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26856179658903156804430237 10071067372088683801661339)
      ·
        refine ⟨15106601058133025702492009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10071067372088683801661339 15106601058133025702492009)
        ·
          refine ⟨11329950793599769276869007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15106601058133025702492009 11329950793599769276869007)
          ·
            refine ⟨16994926190399653915303511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11329950793599769276869007 16994926190399653915303511)
            ·
              refine ⟨25492389285599480872955267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16994926190399653915303511 25492389285599480872955267)
              ·
                refine ⟨38238583928399221309432901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25492389285599480872955267 38238583928399221309432901)
                ·
                  refine ⟨7169734486574853995518669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38238583928399221309432901 7169734486574853995518669)
                  ·
                    refine ⟨2688650432465570248319501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7169734486574853995518669 2688650432465570248319501)
                    ·
                      refine ⟨1008243912174588843119813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2688650432465570248319501 1008243912174588843119813)
                      ·
                        rfl

theorem cell23_1963548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_1963548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963548 prefixEnd_1963548 := by exact prefixLift 1963548
  have htrace : WordTrace (prefixWord ++ tailWord_1963548) baseStart_1963548 baseEnd_1963548 := by
    simpa [prefixWord, tailWord_1963548, baseEnd_1963548] using wordTrace_append hprefix tailTrace_1963548
  have hstable : (prefixWord ++ tailWord_1963548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963548).length < 2 ^ (prefixWord ++ tailWord_1963548).sum := by decide
  have hdescent : baseEnd_1963548 < baseStart_1963548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963566 : List Nat := [4, 1, 3, 1, 2, 2, 3, 1, 2, 2, 2]
def baseStart_1963566 : Nat := 118140960795 + 1963566 * 2 ^ 59
def prefixEnd_1963566 : Nat := 4983230072969 + 3 ^ 40 * 1963566 * 2
def baseEnd_1963566 : Nat := 1008253154826369772694731

theorem tailTrace_1963566 : CollatzResearch.WordTrace tailWord_1963566 prefixEnd_1963566 1008253154826369772694731 := by
  unfold tailWord_1963566
  simp only [CollatzResearch.WordTrace]
  refine ⟨8952141950542900902412819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47744757069562138146201701 8952141950542900902412819)
  ·
    refine ⟨13428212925814351353619229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8952141950542900902412819 13428212925814351353619229)
    ·
      refine ⟨5035579847180381757607211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13428212925814351353619229 5035579847180381757607211)
      ·
        refine ⟨7553369770770572636410817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5035579847180381757607211 7553369770770572636410817)
        ·
          refine ⟨5665027328077929477308113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7553369770770572636410817 5665027328077929477308113)
          ·
            refine ⟨4248770496058447107981085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5665027328077929477308113 4248770496058447107981085)
            ·
              refine ⟨1593288936021917665492907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4248770496058447107981085 1593288936021917665492907)
              ·
                refine ⟨2389933404032876498239361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1593288936021917665492907 2389933404032876498239361)
                ·
                  refine ⟨1792450053024657373679521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2389933404032876498239361 1792450053024657373679521)
                  ·
                    refine ⟨1344337539768493030259641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1792450053024657373679521 1344337539768493030259641)
                    ·
                      refine ⟨1008253154826369772694731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1344337539768493030259641 1008253154826369772694731)
                      ·
                        rfl

theorem cell23_1963566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_1963566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963566 prefixEnd_1963566 := by exact prefixLift 1963566
  have htrace : WordTrace (prefixWord ++ tailWord_1963566) baseStart_1963566 baseEnd_1963566 := by
    simpa [prefixWord, tailWord_1963566, baseEnd_1963566] using wordTrace_append hprefix tailTrace_1963566
  have hstable : (prefixWord ++ tailWord_1963566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963566).length < 2 ^ (prefixWord ++ tailWord_1963566).sum := by decide
  have hdescent : baseEnd_1963566 < baseStart_1963566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963606 : List Nat := [5, 2, 2, 2, 2, 1, 1, 1, 7]
def baseStart_1963606 : Nat := 118140960795 + 1963606 * 2 ^ 59
def prefixEnd_1963606 : Nat := 4983230072969 + 3 ^ 40 * 1963606 * 2
def baseEnd_1963606 : Nat := 112030410450283290688283

theorem tailTrace_1963606 : CollatzResearch.WordTrace tailWord_1963606 prefixEnd_1963606 112030410450283290688283 := by
  unfold tailWord_1963606
  simp only [CollatzResearch.WordTrace]
  refine ⟨4476162157762393378172417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47745729682798862700505781 4476162157762393378172417)
  ·
    refine ⟨3357121618321795033629313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4476162157762393378172417 3357121618321795033629313)
    ·
      refine ⟨2517841213741346275221985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3357121618321795033629313 2517841213741346275221985)
      ·
        refine ⟨1888380910306009706416489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2517841213741346275221985 1888380910306009706416489)
        ·
          refine ⟨1416285682729507279812367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1888380910306009706416489 1416285682729507279812367)
          ·
            refine ⟨2124428524094260919718551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1416285682729507279812367 2124428524094260919718551)
            ·
              refine ⟨3186642786141391379577827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2124428524094260919718551 3186642786141391379577827)
              ·
                refine ⟨4779964179212087069366741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3186642786141391379577827 4779964179212087069366741)
                ·
                  refine ⟨112030410450283290688283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4779964179212087069366741 112030410450283290688283)
                  ·
                    rfl

theorem cell23_1963606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_1963606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963606 prefixEnd_1963606 := by exact prefixLift 1963606
  have htrace : WordTrace (prefixWord ++ tailWord_1963606) baseStart_1963606 baseEnd_1963606 := by
    simpa [prefixWord, tailWord_1963606, baseEnd_1963606] using wordTrace_append hprefix tailTrace_1963606
  have hstable : (prefixWord ++ tailWord_1963606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963606).length < 2 ^ (prefixWord ++ tailWord_1963606).sum := by decide
  have hdescent : baseEnd_1963606 < baseStart_1963606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963665 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 4, 3, 2]
def baseStart_1963665 : Nat := 118140960795 + 1963665 * 2 ^ 59
def prefixEnd_1963665 : Nat := 4983230072969 + 3 ^ 40 * 1963665 * 2
def baseEnd_1963665 : Nat := 1008303989411164885356775

theorem tailTrace_1963665 : CollatzResearch.WordTrace tailWord_1963665 prefixEnd_1963665 1008303989411164885356775 := by
  unfold tailWord_1963665
  simp only [CollatzResearch.WordTrace]
  refine ⟨71620746430984547127156449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47747164287323031418104299 71620746430984547127156449)
  ·
    refine ⟨53715559823238410345367337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71620746430984547127156449 53715559823238410345367337)
    ·
      refine ⟨40286669867428807759025503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53715559823238410345367337 40286669867428807759025503)
      ·
        refine ⟨60430004801143211638538255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40286669867428807759025503 60430004801143211638538255)
        ·
          refine ⟨90645007201714817457807383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60430004801143211638538255 90645007201714817457807383)
          ·
            refine ⟨135967510802572226186711075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90645007201714817457807383 135967510802572226186711075)
            ·
              refine ⟨203951266203858339280066613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135967510802572226186711075 203951266203858339280066613)
              ·
                refine ⟨19120431206611719307506245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203951266203858339280066613 19120431206611719307506245)
                ·
                  refine ⟨3585080851239697370157421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19120431206611719307506245 3585080851239697370157421)
                  ·
                    refine ⟨1344405319214886513809033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3585080851239697370157421 1344405319214886513809033)
                    ·
                      refine ⟨1008303989411164885356775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1344405319214886513809033 1008303989411164885356775)
                      ·
                        rfl

theorem cell23_1963665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 3, 2].length) (baseStart_1963665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963665 prefixEnd_1963665 := by exact prefixLift 1963665
  have htrace : WordTrace (prefixWord ++ tailWord_1963665) baseStart_1963665 baseEnd_1963665 := by
    simpa [prefixWord, tailWord_1963665, baseEnd_1963665] using wordTrace_append hprefix tailTrace_1963665
  have hstable : (prefixWord ++ tailWord_1963665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963665).length < 2 ^ (prefixWord ++ tailWord_1963665).sum := by decide
  have hdescent : baseEnd_1963665 < baseStart_1963665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963695 : List Nat := [1, 1, 2, 1, 2, 4, 2, 4, 1, 1, 4]
def baseStart_1963695 : Nat := 118140960795 + 1963695 * 2 ^ 59
def prefixEnd_1963695 : Nat := 4983230072969 + 3 ^ 40 * 1963695 * 2
def baseEnd_1963695 : Nat := 1008319393830799767981637

theorem tailTrace_1963695 : CollatzResearch.WordTrace tailWord_1963695 prefixEnd_1963695 1008319393830799767981637 := by
  unfold tailWord_1963695
  simp only [CollatzResearch.WordTrace]
  refine ⟨71621840620875862250748539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47747893747250574833832359 71621840620875862250748539)
  ·
    refine ⟨107432760931313793376122809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71621840620875862250748539 107432760931313793376122809)
    ·
      refine ⟨80574570698485345032092107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107432760931313793376122809 80574570698485345032092107)
      ·
        refine ⟨120861856047728017548138161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80574570698485345032092107 120861856047728017548138161)
        ·
          refine ⟨90646392035796013161103621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120861856047728017548138161 90646392035796013161103621)
          ·
            refine ⟨16996198506711752467706929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90646392035796013161103621 16996198506711752467706929)
            ·
              refine ⟨12747148880033814350780197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16996198506711752467706929 12747148880033814350780197)
              ·
                refine ⟨2390090415006340190771287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12747148880033814350780197 2390090415006340190771287)
                ·
                  refine ⟨3585135622509510286156931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2390090415006340190771287 3585135622509510286156931)
                  ·
                    refine ⟨5377703433764265429235397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3585135622509510286156931 5377703433764265429235397)
                    ·
                      refine ⟨1008319393830799767981637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5377703433764265429235397 1008319393830799767981637)
                      ·
                        rfl

theorem cell23_1963695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 1, 4].length) (baseStart_1963695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963695 prefixEnd_1963695 := by exact prefixLift 1963695
  have htrace : WordTrace (prefixWord ++ tailWord_1963695) baseStart_1963695 baseEnd_1963695 := by
    simpa [prefixWord, tailWord_1963695, baseEnd_1963695] using wordTrace_append hprefix tailTrace_1963695
  have hstable : (prefixWord ++ tailWord_1963695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963695).length < 2 ^ (prefixWord ++ tailWord_1963695).sum := by decide
  have hdescent : baseEnd_1963695 < baseStart_1963695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963712 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 5, 2, 2]
def baseStart_1963712 : Nat := 118140960795 + 1963712 * 2 ^ 59
def prefixEnd_1963712 : Nat := 4983230072969 + 3 ^ 40 * 1963712 * 2
def baseEnd_1963712 : Nat := 1008328123001926201469059

theorem tailTrace_1963712 : CollatzResearch.WordTrace tailWord_1963712 prefixEnd_1963712 1008328123001926201469059 := by
  unfold tailWord_1963712
  simp only [CollatzResearch.WordTrace]
  refine ⟨35811230330907137077058695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47748307107876182769411593 35811230330907137077058695)
  ·
    refine ⟨53716845496360705615588043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35811230330907137077058695 53716845496360705615588043)
    ·
      refine ⟨80575268244541058423382065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53716845496360705615588043 80575268244541058423382065)
      ·
        refine ⟨60431451183405793817536549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80575268244541058423382065 60431451183405793817536549)
        ·
          refine ⟨11330897096888586340788103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60431451183405793817536549 11330897096888586340788103)
          ·
            refine ⟨16996345645332879511182155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11330897096888586340788103 16996345645332879511182155)
            ·
              refine ⟨25494518467999319266773233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16996345645332879511182155 25494518467999319266773233)
              ·
                refine ⟨19120888850999489450079925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25494518467999319266773233 19120888850999489450079925)
                ·
                  refine ⟨1792583329781202135944993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19120888850999489450079925 1792583329781202135944993)
                  ·
                    refine ⟨1344437497335901601958745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1792583329781202135944993 1344437497335901601958745)
                    ·
                      refine ⟨1008328123001926201469059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1344437497335901601958745 1008328123001926201469059)
                      ·
                        rfl

theorem cell23_1963712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 5, 2, 2].length) (baseStart_1963712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963712 prefixEnd_1963712 := by exact prefixLift 1963712
  have htrace : WordTrace (prefixWord ++ tailWord_1963712) baseStart_1963712 baseEnd_1963712 := by
    simpa [prefixWord, tailWord_1963712, baseEnd_1963712] using wordTrace_append hprefix tailTrace_1963712
  have hstable : (prefixWord ++ tailWord_1963712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963712).length < 2 ^ (prefixWord ++ tailWord_1963712).sum := by decide
  have hdescent : baseEnd_1963712 < baseStart_1963712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963722 : List Nat := [3, 1, 2, 1, 5, 1, 1, 1, 4, 4]
def baseStart_1963722 : Nat := 118140960795 + 1963722 * 2 ^ 59
def prefixEnd_1963722 : Nat := 4983230072969 + 3 ^ 40 * 1963722 * 2
def baseEnd_1963722 : Nat := 336111085936157054114671

theorem tailTrace_1963722 : CollatzResearch.WordTrace tailWord_1963722 prefixEnd_1963722 336111085936157054114671 := by
  unfold tailWord_1963722
  simp only [CollatzResearch.WordTrace]
  refine ⟨17905706347944511465495355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47748550261185363907987613 17905706347944511465495355)
  ·
    refine ⟨26858559521916767198243033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17905706347944511465495355 26858559521916767198243033)
    ·
      refine ⟨20143919641437575398682275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26858559521916767198243033 20143919641437575398682275)
      ·
        refine ⟨30215879462156363098023413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20143919641437575398682275 30215879462156363098023413)
        ·
          refine ⟨2832738699577159040439695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30215879462156363098023413 2832738699577159040439695)
          ·
            refine ⟨4249108049365738560659543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2832738699577159040439695 4249108049365738560659543)
            ·
              refine ⟨6373662074048607840989315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4249108049365738560659543 6373662074048607840989315)
              ·
                refine ⟨9560493111072911761483973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6373662074048607840989315 9560493111072911761483973)
                ·
                  refine ⟨1792592458326170955278245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9560493111072911761483973 1792592458326170955278245)
                  ·
                    refine ⟨336111085936157054114671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1792592458326170955278245 336111085936157054114671)
                    ·
                      rfl

theorem cell23_1963722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_1963722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963722 prefixEnd_1963722 := by exact prefixLift 1963722
  have htrace : WordTrace (prefixWord ++ tailWord_1963722) baseStart_1963722 baseEnd_1963722 := by
    simpa [prefixWord, tailWord_1963722, baseEnd_1963722] using wordTrace_append hprefix tailTrace_1963722
  have hstable : (prefixWord ++ tailWord_1963722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963722).length < 2 ^ (prefixWord ++ tailWord_1963722).sum := by decide
  have hdescent : baseEnd_1963722 < baseStart_1963722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963729 : List Nat := [1, 2, 2, 1, 2, 5, 2, 1, 3, 2, 2]
def baseStart_1963729 : Nat := 118140960795 + 1963729 * 2 ^ 59
def prefixEnd_1963729 : Nat := 4983230072969 + 3 ^ 40 * 1963729 * 2
def baseEnd_1963729 : Nat := 1008336852173052634956481

theorem tailTrace_1963729 : CollatzResearch.WordTrace tailWord_1963729 prefixEnd_1963729 1008336852173052634956481 := by
  unfold tailWord_1963729
  simp only [CollatzResearch.WordTrace]
  refine ⟨71623080702752686057486241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47748720468501790704990827 71623080702752686057486241)
  ·
    refine ⟨53717310527064514543114681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71623080702752686057486241 53717310527064514543114681)
    ·
      refine ⟨40287982895298385907336011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53717310527064514543114681 40287982895298385907336011)
      ·
        refine ⟨60431974342947578861004017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40287982895298385907336011 60431974342947578861004017)
        ·
          refine ⟨45323980757210684145753013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60431974342947578861004017 45323980757210684145753013)
          ·
            refine ⟨4249123195988501638664345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45323980757210684145753013 4249123195988501638664345)
            ·
              refine ⟨3186842396991376228998259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4249123195988501638664345 3186842396991376228998259)
              ·
                refine ⟨4780263595487064343497389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3186842396991376228998259 4780263595487064343497389)
                ·
                  refine ⟨1792598848307649128811521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4780263595487064343497389 1792598848307649128811521)
                  ·
                    refine ⟨1344449136230736846608641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1792598848307649128811521 1344449136230736846608641)
                    ·
                      refine ⟨1008336852173052634956481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1344449136230736846608641 1008336852173052634956481)
                      ·
                        rfl

theorem cell23_1963729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 3, 2, 2].length) (baseStart_1963729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963729 prefixEnd_1963729 := by exact prefixLift 1963729
  have htrace : WordTrace (prefixWord ++ tailWord_1963729) baseStart_1963729 baseEnd_1963729 := by
    simpa [prefixWord, tailWord_1963729, baseEnd_1963729] using wordTrace_append hprefix tailTrace_1963729
  have hstable : (prefixWord ++ tailWord_1963729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963729).length < 2 ^ (prefixWord ++ tailWord_1963729).sum := by decide
  have hdescent : baseEnd_1963729 < baseStart_1963729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963732 : List Nat := [2, 4, 1, 3, 1, 2, 1, 2, 1, 1, 5]
def baseStart_1963732 : Nat := 118140960795 + 1963732 * 2 ^ 59
def prefixEnd_1963732 : Nat := 4983230072969 + 3 ^ 40 * 1963732 * 2
def baseEnd_1963732 : Nat := 1008338392615016123218967

theorem tailTrace_1963732 : CollatzResearch.WordTrace tailWord_1963732 prefixEnd_1963732 1008338392615016123218967 := by
  unfold tailWord_1963732
  simp only [CollatzResearch.WordTrace]
  refine ⟨35811595060870908784922725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47748793414494545046563633 35811595060870908784922725)
  ·
    refine ⟨6714674073913295397173011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35811595060870908784922725 6714674073913295397173011)
    ·
      refine ⟨10072011110869943095759517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6714674073913295397173011 10072011110869943095759517)
      ·
        refine ⟨3777004166576228660909819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10072011110869943095759517 3777004166576228660909819)
        ·
          refine ⟨5665506249864342991364729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3777004166576228660909819 5665506249864342991364729)
          ·
            refine ⟨4249129687398257243523547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5665506249864342991364729 4249129687398257243523547)
            ·
              refine ⟨6373694531097385865285321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4249129687398257243523547 6373694531097385865285321)
              ·
                refine ⟨4780270898323039398963991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6373694531097385865285321 4780270898323039398963991)
                ·
                  refine ⟨7170406347484559098445987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4780270898323039398963991 7170406347484559098445987)
                  ·
                    refine ⟨10755609521226838647668981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7170406347484559098445987 10755609521226838647668981)
                    ·
                      refine ⟨1008338392615016123218967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10755609521226838647668981 1008338392615016123218967)
                      ·
                        rfl

theorem cell23_1963732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_1963732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963732 prefixEnd_1963732 := by exact prefixLift 1963732
  have htrace : WordTrace (prefixWord ++ tailWord_1963732) baseStart_1963732 baseEnd_1963732 := by
    simpa [prefixWord, tailWord_1963732, baseEnd_1963732] using wordTrace_append hprefix tailTrace_1963732
  have hstable : (prefixWord ++ tailWord_1963732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963732).length < 2 ^ (prefixWord ++ tailWord_1963732).sum := by decide
  have hdescent : baseEnd_1963732 < baseStart_1963732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963752 : List Nat := [2, 1, 4, 1, 3, 3, 2, 7]
def baseStart_1963752 : Nat := 118140960795 + 1963752 * 2 ^ 59
def prefixEnd_1963752 : Nat := 4983230072969 + 3 ^ 40 * 1963752 * 2
def baseEnd_1963752 : Nat := 37346246749189112776625

theorem tailTrace_1963752 : CollatzResearch.WordTrace tailWord_1963752 prefixEnd_1963752 37346246749189112776625 := by
  unfold tailWord_1963752
  simp only [CollatzResearch.WordTrace]
  refine ⟨35811959790834680492786755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47749279721112907323715673 35811959790834680492786755)
  ·
    refine ⟨53717939686252020739180133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35811959790834680492786755 53717939686252020739180133)
    ·
      refine ⟨10072113691172253888596275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53717939686252020739180133 10072113691172253888596275)
      ·
        refine ⟨15108170536758380832894413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10072113691172253888596275 15108170536758380832894413)
        ·
          refine ⟨5665563951284392812335405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15108170536758380832894413 5665563951284392812335405)
          ·
            refine ⟨2124586481731647304625777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5665563951284392812335405 2124586481731647304625777)
            ·
              refine ⟨1593439861298735478469333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2124586481731647304625777 1593439861298735478469333)
              ·
                refine ⟨37346246749189112776625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1593439861298735478469333 37346246749189112776625)
                ·
                  rfl

theorem cell23_1963752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 7].length) (baseStart_1963752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963752 prefixEnd_1963752 := by exact prefixLift 1963752
  have htrace : WordTrace (prefixWord ++ tailWord_1963752) baseStart_1963752 baseEnd_1963752 := by
    simpa [prefixWord, tailWord_1963752, baseEnd_1963752] using wordTrace_append hprefix tailTrace_1963752
  have hstable : (prefixWord ++ tailWord_1963752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963752).length < 2 ^ (prefixWord ++ tailWord_1963752).sum := by decide
  have hdescent : baseEnd_1963752 < baseStart_1963752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963762 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 6, 1, 3]
def baseStart_1963762 : Nat := 118140960795 + 1963762 * 2 ^ 59
def prefixEnd_1963762 : Nat := 4983230072969 + 3 ^ 40 * 1963762 * 2
def baseEnd_1963762 : Nat := 1008353797034651005843829

theorem tailTrace_1963762 : CollatzResearch.WordTrace tailWord_1963762 prefixEnd_1963762 1008353797034651005843829 := by
  unfold tailWord_1963762
  simp only [CollatzResearch.WordTrace]
  refine ⟨17906071077908283173359385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47749522874422088462291693 17906071077908283173359385)
  ·
    refine ⟨13429553308431212380019539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17906071077908283173359385 13429553308431212380019539)
    ·
      refine ⟨20144329962646818570029309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13429553308431212380019539 20144329962646818570029309)
      ·
        refine ⟨7554123735992556963760991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20144329962646818570029309 7554123735992556963760991)
        ·
          refine ⟨11331185603988835445641487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7554123735992556963760991 11331185603988835445641487)
          ·
            refine ⟨16996778405983253168462231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11331185603988835445641487 16996778405983253168462231)
            ·
              refine ⟨25495167608974879752693347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16996778405983253168462231 25495167608974879752693347)
              ·
                refine ⟨38242751413462319629040021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25495167608974879752693347 38242751413462319629040021)
                ·
                  refine ⟨1792628972506046232611251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38242751413462319629040021 1792628972506046232611251)
                  ·
                    refine ⟨2688943458759069348916877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1792628972506046232611251 2688943458759069348916877)
                    ·
                      refine ⟨1008353797034651005843829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2688943458759069348916877 1008353797034651005843829)
                      ·
                        rfl

theorem cell23_1963762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_1963762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963762 prefixEnd_1963762 := by exact prefixLift 1963762
  have htrace : WordTrace (prefixWord ++ tailWord_1963762) baseStart_1963762 baseEnd_1963762 := by
    simpa [prefixWord, tailWord_1963762, baseEnd_1963762] using wordTrace_append hprefix tailTrace_1963762
  have hstable : (prefixWord ++ tailWord_1963762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963762).length < 2 ^ (prefixWord ++ tailWord_1963762).sum := by decide
  have hdescent : baseEnd_1963762 < baseStart_1963762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963853 : List Nat := [1, 6, 1, 2, 1, 1, 2, 3, 2, 2, 2]
def baseStart_1963853 : Nat := 118140960795 + 1963853 * 2 ^ 59
def prefixEnd_1963853 : Nat := 4983230072969 + 3 ^ 40 * 1963853 * 2
def baseEnd_1963853 : Nat := 1008400523774210149805911

theorem tailTrace_1963853 : CollatzResearch.WordTrace tailWord_1963853 prefixEnd_1963853 1008400523774210149805911 := by
  unfold tailWord_1963853
  simp only [CollatzResearch.WordTrace]
  refine ⟨71627603354303455235000213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47751735569535636823333475 71627603354303455235000213)
  ·
    refine ⟨3357543907232974464140635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 71627603354303455235000213 3357543907232974464140635)
    ·
      refine ⟨5036315860849461696210953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3357543907232974464140635 5036315860849461696210953)
      ·
        refine ⟨3777236895637096272158215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5036315860849461696210953 3777236895637096272158215)
        ·
          refine ⟨5665855343455644408237323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3777236895637096272158215 5665855343455644408237323)
          ·
            refine ⟨8498783015183466612355985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5665855343455644408237323 8498783015183466612355985)
            ·
              refine ⟨6374087261387599959266989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8498783015183466612355985 6374087261387599959266989)
              ·
                refine ⟨2390282723020349984725121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6374087261387599959266989 2390282723020349984725121)
                ·
                  refine ⟨1792712042265262488543841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2390282723020349984725121 1792712042265262488543841)
                  ·
                    refine ⟨1344534031698946866407881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1792712042265262488543841 1344534031698946866407881)
                    ·
                      refine ⟨1008400523774210149805911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1344534031698946866407881 1008400523774210149805911)
                      ·
                        rfl

theorem cell23_1963853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_1963853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963853 prefixEnd_1963853 := by exact prefixLift 1963853
  have htrace : WordTrace (prefixWord ++ tailWord_1963853) baseStart_1963853 baseEnd_1963853 := by
    simpa [prefixWord, tailWord_1963853, baseEnd_1963853] using wordTrace_append hprefix tailTrace_1963853
  have hstable : (prefixWord ++ tailWord_1963853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963853).length < 2 ^ (prefixWord ++ tailWord_1963853).sum := by decide
  have hdescent : baseEnd_1963853 < baseStart_1963853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963872 : List Nat := [2, 1, 1, 3, 3, 2, 3, 1, 2, 5]
def baseStart_1963872 : Nat := 118140960795 + 1963872 * 2 ^ 59
def prefixEnd_1963872 : Nat := 4983230072969 + 3 ^ 40 * 1963872 * 2
def baseEnd_1963872 : Nat := 336136759968881858489441

theorem tailTrace_1963872 : CollatzResearch.WordTrace tailWord_1963872 prefixEnd_1963872 336136759968881858489441 := by
  unfold tailWord_1963872
  simp only [CollatzResearch.WordTrace]
  refine ⟨35814148170617310739970935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47752197560823080986627913 35814148170617310739970935)
  ·
    refine ⟨53721222255925966109956403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35814148170617310739970935 53721222255925966109956403)
    ·
      refine ⟨80581833383888949164934605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53721222255925966109956403 80581833383888949164934605)
      ·
        refine ⟨30218187518958355936850477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80581833383888949164934605 30218187518958355936850477)
        ·
          refine ⟨11331820319609383476318929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30218187518958355936850477 11331820319609383476318929)
          ·
            refine ⟨8498865239707037607239197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11331820319609383476318929 8498865239707037607239197)
            ·
              refine ⟨3187074464890139102714699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8498865239707037607239197 3187074464890139102714699)
              ·
                refine ⟨4780611697335208654072049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3187074464890139102714699 4780611697335208654072049)
                ·
                  refine ⟨3585458773001406490554037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4780611697335208654072049 3585458773001406490554037)
                  ·
                    refine ⟨336136759968881858489441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3585458773001406490554037 336136759968881858489441)
                    ·
                      rfl

theorem cell23_1963872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 2, 5].length) (baseStart_1963872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963872 prefixEnd_1963872 := by exact prefixLift 1963872
  have htrace : WordTrace (prefixWord ++ tailWord_1963872) baseStart_1963872 baseEnd_1963872 := by
    simpa [prefixWord, tailWord_1963872, baseEnd_1963872] using wordTrace_append hprefix tailTrace_1963872
  have hstable : (prefixWord ++ tailWord_1963872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963872).length < 2 ^ (prefixWord ++ tailWord_1963872).sum := by decide
  have hdescent : baseEnd_1963872 < baseStart_1963872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963932 : List Nat := [2, 2, 3, 3, 1, 1, 1, 2, 8]
def baseStart_1963932 : Nat := 118140960795 + 1963932 * 2 ^ 59
def prefixEnd_1963932 : Nat := 4983230072969 + 3 ^ 40 * 1963932 * 2
def baseEnd_1963932 : Nat := 112049009860657260079783

theorem tailTrace_1963932 : CollatzResearch.WordTrace tailWord_1963932 prefixEnd_1963932 112049009860657260079783 := by
  unfold tailWord_1963932
  simp only [CollatzResearch.WordTrace]
  refine ⟨35815242360508625863563025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47753656480678167818084033 35815242360508625863563025)
  ·
    refine ⟨26861431770381469397672269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35815242360508625863563025 26861431770381469397672269)
    ·
      refine ⟨10073036913893051024127101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26861431770381469397672269 10073036913893051024127101)
      ·
        refine ⟨3777388842709894134047663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10073036913893051024127101 3777388842709894134047663)
        ·
          refine ⟨5666083264064841201071495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3777388842709894134047663 5666083264064841201071495)
          ·
            refine ⟨8499124896097261801607243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5666083264064841201071495 8499124896097261801607243)
            ·
              refine ⟨12748687344145892702410865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8499124896097261801607243 12748687344145892702410865)
              ·
                refine ⟨9561515508109419526808149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12748687344145892702410865 9561515508109419526808149)
                ·
                  refine ⟨112049009860657260079783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9561515508109419526808149 112049009860657260079783)
                  ·
                    rfl

theorem cell23_1963932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 8].length) (baseStart_1963932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963932 prefixEnd_1963932 := by exact prefixLift 1963932
  have htrace : WordTrace (prefixWord ++ tailWord_1963932) baseStart_1963932 baseEnd_1963932 := by
    simpa [prefixWord, tailWord_1963932, baseEnd_1963932] using wordTrace_append hprefix tailTrace_1963932
  have hstable : (prefixWord ++ tailWord_1963932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963932).length < 2 ^ (prefixWord ++ tailWord_1963932).sum := by decide
  have hdescent : baseEnd_1963932 < baseStart_1963932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963952 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 2, 9, 2]
def baseStart_1963952 : Nat := 118140960795 + 1963952 * 2 ^ 59
def prefixEnd_1963952 : Nat := 4983230072969 + 3 ^ 40 * 1963952 * 2
def baseEnd_1963952 : Nat := 1008451358359005262467955

theorem tailTrace_1963952 : CollatzResearch.WordTrace tailWord_1963952 prefixEnd_1963952 1008451358359005262467955 := by
  unfold tailWord_1963952
  simp only [CollatzResearch.WordTrace]
  refine ⟨35815607090472397571427055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47754142787296530095236073 35815607090472397571427055)
  ·
    refine ⟨53723410635708596357140583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35815607090472397571427055 53723410635708596357140583)
    ·
      refine ⟨80585115953562894535710875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53723410635708596357140583 80585115953562894535710875)
      ·
        refine ⟨120877673930344341803566313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80585115953562894535710875 120877673930344341803566313)
        ·
          refine ⟨90658255447758256352674735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120877673930344341803566313 90658255447758256352674735)
          ·
            refine ⟨135987383171637384529012103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90658255447758256352674735 135987383171637384529012103)
            ·
              refine ⟨203981074757456076793518155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135987383171637384529012103 203981074757456076793518155)
              ·
                refine ⟨305971612136184115190277233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203981074757456076793518155 305971612136184115190277233)
                ·
                  refine ⟨229478709102138086392707925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305971612136184115190277233 229478709102138086392707925)
                  ·
                    refine ⟨1344601811145340349957273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 229478709102138086392707925 1344601811145340349957273)
                    ·
                      refine ⟨1008451358359005262467955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1344601811145340349957273 1008451358359005262467955)
                      ·
                        rfl

theorem cell23_1963952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 9, 2].length) (baseStart_1963952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963952 prefixEnd_1963952 := by exact prefixLift 1963952
  have htrace : WordTrace (prefixWord ++ tailWord_1963952) baseStart_1963952 baseEnd_1963952 := by
    simpa [prefixWord, tailWord_1963952, baseEnd_1963952] using wordTrace_append hprefix tailTrace_1963952
  have hstable : (prefixWord ++ tailWord_1963952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963952).length < 2 ^ (prefixWord ++ tailWord_1963952).sum := by decide
  have hdescent : baseEnd_1963952 < baseStart_1963952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963953 : List Nat := [1, 2, 2, 4, 2, 2, 3, 2, 1, 4]
def baseStart_1963953 : Nat := 118140960795 + 1963953 * 2 ^ 59
def prefixEnd_1963953 : Nat := 4983230072969 + 3 ^ 40 * 1963953 * 2
def baseEnd_1963953 : Nat := 336150623946553252851817

theorem tailTrace_1963953 : CollatzResearch.WordTrace tailWord_1963953 prefixEnd_1963953 336150623946553252851817 := by
  unfold tailWord_1963953
  simp only [CollatzResearch.WordTrace]
  refine ⟨71631250653941172313640513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47754167102627448209093675 71631250653941172313640513)
  ·
    refine ⟨53723437990455879235230385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71631250653941172313640513 53723437990455879235230385)
    ·
      refine ⟨40292578492841909426422789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53723437990455879235230385 40292578492841909426422789)
      ·
        refine ⟨7554858467407858017454273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40292578492841909426422789 7554858467407858017454273)
        ·
          refine ⟨5666143850555893513090705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7554858467407858017454273 5666143850555893513090705)
          ·
            refine ⟨4249607887916920134818029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5666143850555893513090705 4249607887916920134818029)
            ·
              refine ⟨1593602957968845050556761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4249607887916920134818029 1593602957968845050556761)
              ·
                refine ⟨1195202218476633787917571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1593602957968845050556761 1195202218476633787917571)
                ·
                  refine ⟨1792803327714950681876357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1195202218476633787917571 1792803327714950681876357)
                  ·
                    refine ⟨336150623946553252851817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1792803327714950681876357 336150623946553252851817)
                    ·
                      rfl

theorem cell23_1963953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 2, 1, 4].length) (baseStart_1963953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963953 prefixEnd_1963953 := by exact prefixLift 1963953
  have htrace : WordTrace (prefixWord ++ tailWord_1963953) baseStart_1963953 baseEnd_1963953 := by
    simpa [prefixWord, tailWord_1963953, baseEnd_1963953] using wordTrace_append hprefix tailTrace_1963953
  have hstable : (prefixWord ++ tailWord_1963953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963953).length < 2 ^ (prefixWord ++ tailWord_1963953).sum := by decide
  have hdescent : baseEnd_1963953 < baseStart_1963953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963966 : List Nat := [4, 2, 1, 1, 1, 5, 2, 1, 6]
def baseStart_1963966 : Nat := 118140960795 + 1963966 * 2 ^ 59
def prefixEnd_1963966 : Nat := 4983230072969 + 3 ^ 40 * 1963966 * 2
def baseEnd_1963966 : Nat := 112050949676463134188099

theorem tailTrace_1963966 : CollatzResearch.WordTrace tailWord_1963966 prefixEnd_1963966 112050949676463134188099 := by
  unfold tailWord_1963966
  simp only [CollatzResearch.WordTrace]
  refine ⟨8953965600361759441732969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47754483201929383689242501 8953965600361759441732969)
  ·
    refine ⟨6715474200271319581299727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8953965600361759441732969 6715474200271319581299727)
    ·
      refine ⟨10073211300406979371949591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6715474200271319581299727 10073211300406979371949591)
      ·
        refine ⟨15109816950610469057924387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10073211300406979371949591 15109816950610469057924387)
        ·
          refine ⟨22664725425915703586886581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15109816950610469057924387 22664725425915703586886581)
          ·
            refine ⟨2124818008679597211270617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22664725425915703586886581 2124818008679597211270617)
            ·
              refine ⟨1593613506509697908452963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2124818008679597211270617 1593613506509697908452963)
              ·
                refine ⟨2390420259764546862679445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1593613506509697908452963 2390420259764546862679445)
                ·
                  refine ⟨112050949676463134188099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2390420259764546862679445 112050949676463134188099)
                  ·
                    rfl

theorem cell23_1963966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_1963966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963966 prefixEnd_1963966 := by exact prefixLift 1963966
  have htrace : WordTrace (prefixWord ++ tailWord_1963966) baseStart_1963966 baseEnd_1963966 := by
    simpa [prefixWord, tailWord_1963966, baseEnd_1963966] using wordTrace_append hprefix tailTrace_1963966
  have hstable : (prefixWord ++ tailWord_1963966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963966).length < 2 ^ (prefixWord ++ tailWord_1963966).sum := by decide
  have hdescent : baseEnd_1963966 < baseStart_1963966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963992 : List Nat := [2, 1, 2, 2, 2, 2, 3, 2, 1, 6]
def baseStart_1963992 : Nat := 118140960795 + 1963992 * 2 ^ 59
def prefixEnd_1963992 : Nat := 4983230072969 + 3 ^ 40 * 1963992 * 2
def baseEnd_1963992 : Nat := 336157299195061701989257

theorem tailTrace_1963992 : CollatzResearch.WordTrace tailWord_1963992 prefixEnd_1963992 336157299195061701989257 := by
  unfold tailWord_1963992
  simp only [CollatzResearch.WordTrace]
  refine ⟨35816336550399940987155115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47755115400533254649540153 35816336550399940987155115)
  ·
    refine ⟨53724504825599911480732673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35816336550399940987155115 53724504825599911480732673)
    ·
      refine ⟨40293378619199933610549505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53724504825599911480732673 40293378619199933610549505)
      ·
        refine ⟨30220033964399950207912129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40293378619199933610549505 30220033964399950207912129)
        ·
          refine ⟨22665025473299962655934097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30220033964399950207912129 22665025473299962655934097)
          ·
            refine ⟨16998769104974971991950573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22665025473299962655934097 16998769104974971991950573)
            ·
              refine ⟨6374538414365614496981465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16998769104974971991950573 6374538414365614496981465)
              ·
                refine ⟨4780903810774210872736099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6374538414365614496981465 4780903810774210872736099)
                ·
                  refine ⟨7171355716161316309104149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4780903810774210872736099 7171355716161316309104149)
                  ·
                    refine ⟨336157299195061701989257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7171355716161316309104149 336157299195061701989257)
                    ·
                      rfl

theorem cell23_1963992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 1, 6].length) (baseStart_1963992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1963992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1963992 prefixEnd_1963992 := by exact prefixLift 1963992
  have htrace : WordTrace (prefixWord ++ tailWord_1963992) baseStart_1963992 baseEnd_1963992 := by
    simpa [prefixWord, tailWord_1963992, baseEnd_1963992] using wordTrace_append hprefix tailTrace_1963992
  have hstable : (prefixWord ++ tailWord_1963992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963992).length < 2 ^ (prefixWord ++ tailWord_1963992).sum := by decide
  have hdescent : baseEnd_1963992 < baseStart_1963992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964005 : List Nat := [1, 3, 1, 18]
def baseStart_1964005 : Nat := 118140960795 + 1964005 * 2 ^ 59
def prefixEnd_1964005 : Nat := 4983230072969 + 3 ^ 40 * 1964005 * 2
def baseEnd_1964005 : Nat := 461124175964194583953

theorem tailTrace_1964005 : CollatzResearch.WordTrace tailWord_1964005 prefixEnd_1964005 461124175964194583953 := by
  unfold tailWord_1964005
  simp only [CollatzResearch.WordTrace]
  refine ⟨71633147249752785194533469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47755431499835190129688979 71633147249752785194533469)
  ·
    refine ⟨26862430218657294447950051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71633147249752785194533469 26862430218657294447950051)
    ·
      refine ⟨40293645327985941671925077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26862430218657294447950051 40293645327985941671925077)
      ·
        refine ⟨461124175964194583953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 18 40293645327985941671925077 461124175964194583953)
        ·
          rfl

theorem cell23_1964005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 18].length) (baseStart_1964005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964005 prefixEnd_1964005 := by exact prefixLift 1964005
  have htrace : WordTrace (prefixWord ++ tailWord_1964005) baseStart_1964005 baseEnd_1964005 := by
    simpa [prefixWord, tailWord_1964005, baseEnd_1964005] using wordTrace_append hprefix tailTrace_1964005
  have hstable : (prefixWord ++ tailWord_1964005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964005).length < 2 ^ (prefixWord ++ tailWord_1964005).sum := by decide
  have hdescent : baseEnd_1964005 < baseStart_1964005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964039 : List Nat := [1, 1, 4, 3, 1, 3, 3, 7]
def baseStart_1964039 : Nat := 118140960795 + 1964039 * 2 ^ 59
def prefixEnd_1964039 : Nat := 4983230072969 + 3 ^ 40 * 1964039 * 2
def baseEnd_1964039 : Nat := 37351704858368386002965

theorem tailTrace_1964039 : CollatzResearch.WordTrace tailWord_1964039 prefixEnd_1964039 37351704858368386002965 := by
  unfold tailWord_1964039
  simp only [CollatzResearch.WordTrace]
  refine ⟨71634387331629609001271171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47756258221086406000847447 71634387331629609001271171)
  ·
    refine ⟨107451580997444413501906757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71634387331629609001271171 107451580997444413501906757)
    ·
      refine ⟨20147171437020827531607517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107451580997444413501906757 20147171437020827531607517)
      ·
        refine ⟨7555189288882810324352819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20147171437020827531607517 7555189288882810324352819)
        ·
          refine ⟨11332783933324215486529229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7555189288882810324352819 11332783933324215486529229)
          ·
            refine ⟨4249793974996580807448461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11332783933324215486529229 4249793974996580807448461)
            ·
              refine ⟨1593672740623717802793173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4249793974996580807448461 1593672740623717802793173)
              ·
                refine ⟨37351704858368386002965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1593672740623717802793173 37351704858368386002965)
                ·
                  rfl

theorem cell23_1964039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 7].length) (baseStart_1964039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964039 prefixEnd_1964039 := by exact prefixLift 1964039
  have htrace : WordTrace (prefixWord ++ tailWord_1964039) baseStart_1964039 baseEnd_1964039 := by
    simpa [prefixWord, tailWord_1964039, baseEnd_1964039] using wordTrace_append hprefix tailTrace_1964039
  have hstable : (prefixWord ++ tailWord_1964039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964039).length < 2 ^ (prefixWord ++ tailWord_1964039).sum := by decide
  have hdescent : baseEnd_1964039 < baseStart_1964039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964059 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 5, 3, 2]
def baseStart_1964059 : Nat := 118140960795 + 1964059 * 2 ^ 59
def prefixEnd_1964059 : Nat := 4983230072969 + 3 ^ 40 * 1964059 * 2
def baseEnd_1964059 : Nat := 1008506300789036343829963

theorem tailTrace_1964059 : CollatzResearch.WordTrace tailWord_1964059 prefixEnd_1964059 1008506300789036343829963 := by
  unfold tailWord_1964059
  simp only [CollatzResearch.WordTrace]
  refine ⟨71635116791557152416999231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47756744527704768277999487 71635116791557152416999231)
  ·
    refine ⟨107452675187335728625498847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71635116791557152416999231 107452675187335728625498847)
    ·
      refine ⟨161179012781003592938248271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107452675187335728625498847 161179012781003592938248271)
      ·
        refine ⟨241768519171505389407372407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161179012781003592938248271 241768519171505389407372407)
        ·
          refine ⟨362652778757258084111058611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241768519171505389407372407 362652778757258084111058611)
          ·
            refine ⟨543979168135887126166587917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362652778757258084111058611 543979168135887126166587917)
            ·
              refine ⟨203992188050957672312470469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 543979168135887126166587917 203992188050957672312470469)
              ·
                refine ⟨38248535259554563558588213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203992188050957672312470469 38248535259554563558588213)
                ·
                  refine ⟨3585800180583240333617645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38248535259554563558588213 3585800180583240333617645)
                  ·
                    refine ⟨1344675067718715125106617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3585800180583240333617645 1344675067718715125106617)
                    ·
                      refine ⟨1008506300789036343829963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1344675067718715125106617 1008506300789036343829963)
                      ·
                        rfl

theorem cell23_1964059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 3, 2].length) (baseStart_1964059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964059 prefixEnd_1964059 := by exact prefixLift 1964059
  have htrace : WordTrace (prefixWord ++ tailWord_1964059) baseStart_1964059 baseEnd_1964059 := by
    simpa [prefixWord, tailWord_1964059, baseEnd_1964059] using wordTrace_append hprefix tailTrace_1964059
  have hstable : (prefixWord ++ tailWord_1964059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964059).length < 2 ^ (prefixWord ++ tailWord_1964059).sum := by decide
  have hdescent : baseEnd_1964059 < baseStart_1964059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964066 : List Nat := [3, 3, 1, 1, 1, 2, 3, 1, 4, 1, 3]
def baseStart_1964066 : Nat := 118140960795 + 1964066 * 2 ^ 59
def prefixEnd_1964066 : Nat := 4983230072969 + 3 ^ 40 * 1964066 * 2
def baseEnd_1964066 : Nat := 1008509895153617816442431

theorem tailTrace_1964066 : CollatzResearch.WordTrace tailWord_1964066 prefixEnd_1964066 1008509895153617816442431 := by
  unfold tailWord_1964066
  simp only [CollatzResearch.WordTrace]
  refine ⟨17908843025632948153126013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47756914735021195075002701 17908843025632948153126013)
  ·
    refine ⟨6715816134612355557422255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17908843025632948153126013 6715816134612355557422255)
    ·
      refine ⟨10073724201918533336133383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6715816134612355557422255 10073724201918533336133383)
      ·
        refine ⟨15110586302877800004200075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10073724201918533336133383 15110586302877800004200075)
        ·
          refine ⟨22665879454316700006300113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15110586302877800004200075 22665879454316700006300113)
          ·
            refine ⟨16999409590737525004725085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22665879454316700006300113 16999409590737525004725085)
            ·
              refine ⟨6374778596526571876771907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16999409590737525004725085 6374778596526571876771907)
              ·
                refine ⟨9562167894789857815157861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6374778596526571876771907 9562167894789857815157861)
                ·
                  refine ⟨1792906480273098340342099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9562167894789857815157861 1792906480273098340342099)
                  ·
                    refine ⟨2689359720409647510513149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1792906480273098340342099 2689359720409647510513149)
                    ·
                      refine ⟨1008509895153617816442431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2689359720409647510513149 1008509895153617816442431)
                      ·
                        rfl

theorem cell23_1964066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_1964066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964066 prefixEnd_1964066 := by exact prefixLift 1964066
  have htrace : WordTrace (prefixWord ++ tailWord_1964066) baseStart_1964066 baseEnd_1964066 := by
    simpa [prefixWord, tailWord_1964066, baseEnd_1964066] using wordTrace_append hprefix tailTrace_1964066
  have hstable : (prefixWord ++ tailWord_1964066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964066).length < 2 ^ (prefixWord ++ tailWord_1964066).sum := by decide
  have hdescent : baseEnd_1964066 < baseStart_1964066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964093 : List Nat := [1, 4, 1, 3, 1, 1, 4, 2, 1, 3, 2]
def baseStart_1964093 : Nat := 118140960795 + 1964093 * 2 ^ 59
def prefixEnd_1964093 : Nat := 4983230072969 + 3 ^ 40 * 1964093 * 2
def baseEnd_1964093 : Nat := 1008523759131289210804807

theorem tailTrace_1964093 : CollatzResearch.WordTrace tailWord_1964093 prefixEnd_1964093 1008523759131289210804807 := by
  unfold tailWord_1964093
  simp only [CollatzResearch.WordTrace]
  refine ⟨71636356873433976223736933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47757571248955984149157955 71636356873433976223736933)
  ·
    refine ⟨13431816913768870541950675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71636356873433976223736933 13431816913768870541950675)
    ·
      refine ⟨20147725370653305812926013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13431816913768870541950675 20147725370653305812926013)
      ·
        refine ⟨7555397013994989679847255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20147725370653305812926013 7555397013994989679847255)
        ·
          refine ⟨11333095520992484519770883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7555397013994989679847255 11333095520992484519770883)
          ·
            refine ⟨16999643281488726779656325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11333095520992484519770883 16999643281488726779656325)
            ·
              refine ⟨3187433115279136271185561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16999643281488726779656325 3187433115279136271185561)
              ·
                refine ⟨2390574836459352203389171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3187433115279136271185561 2390574836459352203389171)
                ·
                  refine ⟨3585862254689028305083757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2390574836459352203389171 3585862254689028305083757)
                  ·
                    refine ⟨1344698345508385614406409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3585862254689028305083757 1344698345508385614406409)
                    ·
                      refine ⟨1008523759131289210804807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1344698345508385614406409 1008523759131289210804807)
                      ·
                        rfl

theorem cell23_1964093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_1964093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964093 prefixEnd_1964093 := by exact prefixLift 1964093
  have htrace : WordTrace (prefixWord ++ tailWord_1964093) baseStart_1964093 baseEnd_1964093 := by
    simpa [prefixWord, tailWord_1964093, baseEnd_1964093] using wordTrace_append hprefix tailTrace_1964093
  have hstable : (prefixWord ++ tailWord_1964093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964093).length < 2 ^ (prefixWord ++ tailWord_1964093).sum := by decide
  have hdescent : baseEnd_1964093 < baseStart_1964093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964122 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 1, 2, 7]
def baseStart_1964122 : Nat := 118140960795 + 1964122 * 2 ^ 59
def prefixEnd_1964122 : Nat := 4983230072969 + 3 ^ 40 * 1964122 * 2
def baseEnd_1964122 : Nat := 1008538650070269597342173

theorem tailTrace_1964122 : CollatzResearch.WordTrace tailWord_1964122 prefixEnd_1964122 1008538650070269597342173 := by
  unfold tailWord_1964122
  simp only [CollatzResearch.WordTrace]
  refine ⟨17909353647582228544135655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47758276393552609451028413 17909353647582228544135655)
  ·
    refine ⟨26864030471373342816203483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17909353647582228544135655 26864030471373342816203483)
    ·
      refine ⟨40296045707060014224305225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26864030471373342816203483 40296045707060014224305225)
      ·
        refine ⟨30222034280295010668228919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40296045707060014224305225 30222034280295010668228919)
        ·
          refine ⟨45333051420442516002343379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30222034280295010668228919 45333051420442516002343379)
          ·
            refine ⟨67999577130663774003515069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45333051420442516002343379 67999577130663774003515069)
            ·
              refine ⟨25499841423998915251318151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67999577130663774003515069 25499841423998915251318151)
              ·
                refine ⟨38249762135998372876977227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25499841423998915251318151 38249762135998372876977227)
                ·
                  refine ⟨57374643203997559315465841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38249762135998372876977227 57374643203997559315465841)
                  ·
                    refine ⟨43030982402998169486599381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57374643203997559315465841 43030982402998169486599381)
                    ·
                      refine ⟨1008538650070269597342173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 43030982402998169486599381 1008538650070269597342173)
                      ·
                        rfl

theorem cell23_1964122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_1964122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964122 prefixEnd_1964122 := by exact prefixLift 1964122
  have htrace : WordTrace (prefixWord ++ tailWord_1964122) baseStart_1964122 baseEnd_1964122 := by
    simpa [prefixWord, tailWord_1964122, baseEnd_1964122] using wordTrace_append hprefix tailTrace_1964122
  have hstable : (prefixWord ++ tailWord_1964122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964122).length < 2 ^ (prefixWord ++ tailWord_1964122).sum := by decide
  have hdescent : baseEnd_1964122 < baseStart_1964122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964140 : List Nat := [2, 2, 1, 1, 3, 3, 4, 1, 2, 2, 2]
def baseStart_1964140 : Nat := 118140960795 + 1964140 * 2 ^ 59
def prefixEnd_1964140 : Nat := 4983230072969 + 3 ^ 40 * 1964140 * 2
def baseEnd_1964140 : Nat := 1008547892722050526917091

theorem tailTrace_1964140 : CollatzResearch.WordTrace tailWord_1964140 prefixEnd_1964140 1008547892722050526917091 := by
  unfold tailWord_1964140
  simp only [CollatzResearch.WordTrace]
  refine ⟨35819035552131851625348937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47758714069509135500465249 35819035552131851625348937)
  ·
    refine ⟨26864276664098888719011703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35819035552131851625348937 26864276664098888719011703)
    ·
      refine ⟨40296414996148333078517555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26864276664098888719011703 40296414996148333078517555)
      ·
        refine ⟨60444622494222499617776333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40296414996148333078517555 60444622494222499617776333)
        ·
          refine ⟨22666733435333437356666125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60444622494222499617776333 22666733435333437356666125)
          ·
            refine ⟨8500025038250039008749797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22666733435333437356666125 8500025038250039008749797)
            ·
              refine ⟨1593754694671882314140587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8500025038250039008749797 1593754694671882314140587)
              ·
                refine ⟨2390632042007823471210881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1593754694671882314140587 2390632042007823471210881)
                ·
                  refine ⟨1792974031505867603408161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2390632042007823471210881 1792974031505867603408161)
                  ·
                    refine ⟨1344730523629400702556121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1792974031505867603408161 1344730523629400702556121)
                    ·
                      refine ⟨1008547892722050526917091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1344730523629400702556121 1008547892722050526917091)
                      ·
                        rfl

theorem cell23_1964140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 2, 2].length) (baseStart_1964140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964140 prefixEnd_1964140 := by exact prefixLift 1964140
  have htrace : WordTrace (prefixWord ++ tailWord_1964140) baseStart_1964140 baseEnd_1964140 := by
    simpa [prefixWord, tailWord_1964140, baseEnd_1964140] using wordTrace_append hprefix tailTrace_1964140
  have hstable : (prefixWord ++ tailWord_1964140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964140).length < 2 ^ (prefixWord ++ tailWord_1964140).sum := by decide
  have hdescent : baseEnd_1964140 < baseStart_1964140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964152 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 3, 1, 7]
def baseStart_1964152 : Nat := 118140960795 + 1964152 * 2 ^ 59
def prefixEnd_1964152 : Nat := 4983230072969 + 3 ^ 40 * 1964152 * 2
def baseEnd_1964152 : Nat := 1008554054489904479967035

theorem tailTrace_1964152 : CollatzResearch.WordTrace tailWord_1964152 prefixEnd_1964152 1008554054489904479967035 := by
  unfold tailWord_1964152
  simp only [CollatzResearch.WordTrace]
  refine ⟨35819254390110114650067355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47759005853480152866756473 35819254390110114650067355)
  ·
    refine ⟨53728881585165171975101033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35819254390110114650067355 53728881585165171975101033)
    ·
      refine ⟨40296661188873878981325775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53728881585165171975101033 40296661188873878981325775)
      ·
        refine ⟨60444991783310818471988663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40296661188873878981325775 60444991783310818471988663)
        ·
          refine ⟨90667487674966227707982995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60444991783310818471988663 90667487674966227707982995)
          ·
            refine ⟨136001231512449341561974493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90667487674966227707982995 136001231512449341561974493)
            ·
              refine ⟨51000461817168503085740435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136001231512449341561974493 51000461817168503085740435)
              ·
                refine ⟨76500692725752754628610653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51000461817168503085740435 76500692725752754628610653)
                ·
                  refine ⟨28687759772157282985728995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76500692725752754628610653 28687759772157282985728995)
                  ·
                    refine ⟨43031639658235924478593493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28687759772157282985728995 43031639658235924478593493)
                    ·
                      refine ⟨1008554054489904479967035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 43031639658235924478593493 1008554054489904479967035)
                      ·
                        rfl

theorem cell23_1964152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_1964152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964152 prefixEnd_1964152 := by exact prefixLift 1964152
  have htrace : WordTrace (prefixWord ++ tailWord_1964152) baseStart_1964152 baseEnd_1964152 := by
    simpa [prefixWord, tailWord_1964152, baseEnd_1964152] using wordTrace_append hprefix tailTrace_1964152
  have hstable : (prefixWord ++ tailWord_1964152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964152).length < 2 ^ (prefixWord ++ tailWord_1964152).sum := by decide
  have hdescent : baseEnd_1964152 < baseStart_1964152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964180 : List Nat := [2, 4, 2, 3, 1, 1, 1, 4, 5]
def baseStart_1964180 : Nat := 118140960795 + 1964180 * 2 ^ 59
def prefixEnd_1964180 : Nat := 4983230072969 + 3 ^ 40 * 1964180 * 2
def baseEnd_1964180 : Nat := 112063159105358930046323

theorem tailTrace_1964180 : CollatzResearch.WordTrace tailWord_1964180 prefixEnd_1964180 112063159105358930046323 := by
  unfold tailWord_1964180
  simp only [CollatzResearch.WordTrace]
  refine ⟨35819765012059395041076997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47759686682745860054769329 35819765012059395041076997)
  ·
    refine ⟨6716205939761136570201937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35819765012059395041076997 6716205939761136570201937)
    ·
      refine ⟨5037154454820852427651453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6716205939761136570201937 5037154454820852427651453)
      ·
        refine ⟨1888932920557819660369295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5037154454820852427651453 1888932920557819660369295)
        ·
          refine ⟨2833399380836729490553943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1888932920557819660369295 2833399380836729490553943)
          ·
            refine ⟨4250099071255094235830915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2833399380836729490553943 4250099071255094235830915)
            ·
              refine ⟨6375148606882641353746373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4250099071255094235830915 6375148606882641353746373)
              ·
                refine ⟨1195340363790495253827445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6375148606882641353746373 1195340363790495253827445)
                ·
                  refine ⟨112063159105358930046323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1195340363790495253827445 112063159105358930046323)
                  ·
                    rfl

theorem cell23_1964180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_1964180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964180 prefixEnd_1964180 := by exact prefixLift 1964180
  have htrace : WordTrace (prefixWord ++ tailWord_1964180) baseStart_1964180 baseEnd_1964180 := by
    simpa [prefixWord, tailWord_1964180, baseEnd_1964180] using wordTrace_append hprefix tailTrace_1964180
  have hstable : (prefixWord ++ tailWord_1964180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964180).length < 2 ^ (prefixWord ++ tailWord_1964180).sum := by decide
  have hdescent : baseEnd_1964180 < baseStart_1964180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964213 : List Nat := [1, 3, 3, 4, 1, 1, 1, 1, 1, 3, 4]
def baseStart_1964213 : Nat := 118140960795 + 1964213 * 2 ^ 59
def prefixEnd_1964213 : Nat := 4983230072969 + 3 ^ 40 * 1964213 * 2
def baseEnd_1964213 : Nat := 1008585376809828741304255

theorem tailTrace_1964213 : CollatzResearch.WordTrace tailWord_1964213 prefixEnd_1964213 1008585376809828741304255 := by
  unfold tailWord_1964213
  simp only [CollatzResearch.WordTrace]
  refine ⟨71640733632999236718105293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47760489088666157812070195 71640733632999236718105293)
  ·
    refine ⟨26865275112374713769289485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71640733632999236718105293 26865275112374713769289485)
    ·
      refine ⟨10074478167140517663483557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26865275112374713769289485 10074478167140517663483557)
      ·
        refine ⟨1888964656338847061903167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10074478167140517663483557 1888964656338847061903167)
        ·
          refine ⟨2833446984508270592854751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1888964656338847061903167 2833446984508270592854751)
          ·
            refine ⟨4250170476762405889282127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2833446984508270592854751 4250170476762405889282127)
            ·
              refine ⟨6375255715143608833923191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4250170476762405889282127 6375255715143608833923191)
              ·
                refine ⟨9562883572715413250884787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6375255715143608833923191 9562883572715413250884787)
                ·
                  refine ⟨14344325359073119876327181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9562883572715413250884787 14344325359073119876327181)
                  ·
                    refine ⟨5379122009652419953622693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14344325359073119876327181 5379122009652419953622693)
                    ·
                      refine ⟨1008585376809828741304255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5379122009652419953622693 1008585376809828741304255)
                      ·
                        rfl

theorem cell23_1964213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_1964213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964213 prefixEnd_1964213 := by exact prefixLift 1964213
  have htrace : WordTrace (prefixWord ++ tailWord_1964213) baseStart_1964213 baseEnd_1964213 := by
    simpa [prefixWord, tailWord_1964213, baseEnd_1964213] using wordTrace_append hprefix tailTrace_1964213
  have hstable : (prefixWord ++ tailWord_1964213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964213).length < 2 ^ (prefixWord ++ tailWord_1964213).sum := by decide
  have hdescent : baseEnd_1964213 < baseStart_1964213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964249 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 5, 5]
def baseStart_1964249 : Nat := 118140960795 + 1964249 * 2 ^ 59
def prefixEnd_1964249 : Nat := 4983230072969 + 3 ^ 40 * 1964249 * 2
def baseEnd_1964249 : Nat := 336201287371130200151363

theorem tailTrace_1964249 : CollatzResearch.WordTrace tailWord_1964249 prefixEnd_1964249 336201287371130200151363 := by
  unfold tailWord_1964249
  simp only [CollatzResearch.WordTrace]
  refine ⟨71642046660868814866415801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47761364440579209910943867 71642046660868814866415801)
  ·
    refine ⟨53731534995651611149811851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71642046660868814866415801 53731534995651611149811851)
    ·
      refine ⟨80597302493477416724717777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53731534995651611149811851 80597302493477416724717777)
      ·
        refine ⟨60447976870108062543538333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80597302493477416724717777 60447976870108062543538333)
        ·
          refine ⟨22667991326290523453826875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60447976870108062543538333 22667991326290523453826875)
          ·
            refine ⟨34001986989435785180740313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22667991326290523453826875 34001986989435785180740313)
            ·
              refine ⟨25501490242076838885555235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34001986989435785180740313 25501490242076838885555235)
              ·
                refine ⟨38252235363115258328332853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25501490242076838885555235 38252235363115258328332853)
                ·
                  refine ⟨3586147065292055468281205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38252235363115258328332853 3586147065292055468281205)
                  ·
                    refine ⟨336201287371130200151363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3586147065292055468281205 336201287371130200151363)
                    ·
                      rfl

theorem cell23_1964249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 5].length) (baseStart_1964249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964249 prefixEnd_1964249 := by exact prefixLift 1964249
  have htrace : WordTrace (prefixWord ++ tailWord_1964249) baseStart_1964249 baseEnd_1964249 := by
    simpa [prefixWord, tailWord_1964249, baseEnd_1964249] using wordTrace_append hprefix tailTrace_1964249
  have hstable : (prefixWord ++ tailWord_1964249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964249).length < 2 ^ (prefixWord ++ tailWord_1964249).sum := by decide
  have hdescent : baseEnd_1964249 < baseStart_1964249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964256 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 3, 5, 2]
def baseStart_1964256 : Nat := 118140960795 + 1964256 * 2 ^ 59
def prefixEnd_1964256 : Nat := 4983230072969 + 3 ^ 40 * 1964256 * 2
def baseEnd_1964256 : Nat := 1008607456477972073066557

theorem tailTrace_1964256 : CollatzResearch.WordTrace tailWord_1964256 prefixEnd_1964256 1008607456477972073066557 := by
  unfold tailWord_1964256
  simp only [CollatzResearch.WordTrace]
  refine ⟨35821150985921727530960311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47761534647895636707947081 35821150985921727530960311)
  ·
    refine ⟨53731726478882591296440467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35821150985921727530960311 53731726478882591296440467)
    ·
      refine ⟨80597589718323886944660701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53731726478882591296440467 80597589718323886944660701)
      ·
        refine ⟨30224096144371457604247763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80597589718323886944660701 30224096144371457604247763)
        ·
          refine ⟨45336144216557186406371645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30224096144371457604247763 45336144216557186406371645)
          ·
            refine ⟨17001054081208944902389367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45336144216557186406371645 17001054081208944902389367)
            ·
              refine ⟨25501581121813417353584051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17001054081208944902389367 25501581121813417353584051)
              ·
                refine ⟨38252371682720126030376077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25501581121813417353584051 38252371682720126030376077)
                ·
                  refine ⟨14344639381020047261391029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38252371682720126030376077 14344639381020047261391029)
                  ·
                    refine ⟨1344809941970629430755409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14344639381020047261391029 1344809941970629430755409)
                    ·
                      refine ⟨1008607456477972073066557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1344809941970629430755409 1008607456477972073066557)
                      ·
                        rfl

theorem cell23_1964256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 3, 5, 2].length) (baseStart_1964256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964256 prefixEnd_1964256 := by exact prefixLift 1964256
  have htrace : WordTrace (prefixWord ++ tailWord_1964256) baseStart_1964256 baseEnd_1964256 := by
    simpa [prefixWord, tailWord_1964256, baseEnd_1964256] using wordTrace_append hprefix tailTrace_1964256
  have hstable : (prefixWord ++ tailWord_1964256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964256).length < 2 ^ (prefixWord ++ tailWord_1964256).sum := by decide
  have hdescent : baseEnd_1964256 < baseStart_1964256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964290 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 4, 3, 2]
def baseStart_1964290 : Nat := 118140960795 + 1964290 * 2 ^ 59
def prefixEnd_1964290 : Nat := 4983230072969 + 3 ^ 40 * 1964290 * 2
def baseEnd_1964290 : Nat := 1008624914820224940041401

theorem tailTrace_1964290 : CollatzResearch.WordTrace tailWord_1964290 prefixEnd_1964290 1008624914820224940041401 := by
  unfold tailWord_1964290
  simp only [CollatzResearch.WordTrace]
  refine ⟨17910885513430069717164581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47762361369146852579105549 17910885513430069717164581)
  ·
    refine ⟨3358291033768138071968359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17910885513430069717164581 3358291033768138071968359)
    ·
      refine ⟨5037436550652207107952539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3358291033768138071968359 5037436550652207107952539)
      ·
        refine ⟨7556154825978310661928809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5037436550652207107952539 7556154825978310661928809)
        ·
          refine ⟨5667116119483732996446607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7556154825978310661928809 5667116119483732996446607)
          ·
            refine ⟨8500674179225599494669911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5667116119483732996446607 8500674179225599494669911)
            ·
              refine ⟨12751011268838399242004867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8500674179225599494669911 12751011268838399242004867)
              ·
                refine ⟨19126516903257598863007301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12751011268838399242004867 19126516903257598863007301)
                ·
                  refine ⟨3586221919360799786813869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19126516903257598863007301 3586221919360799786813869)
                  ·
                    refine ⟨1344833219760299920055201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3586221919360799786813869 1344833219760299920055201)
                    ·
                      refine ⟨1008624914820224940041401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1344833219760299920055201 1008624914820224940041401)
                      ·
                        rfl

theorem cell23_1964290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_1964290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964290 prefixEnd_1964290 := by exact prefixLift 1964290
  have htrace : WordTrace (prefixWord ++ tailWord_1964290) baseStart_1964290 baseEnd_1964290 := by
    simpa [prefixWord, tailWord_1964290, baseEnd_1964290] using wordTrace_append hprefix tailTrace_1964290
  have hstable : (prefixWord ++ tailWord_1964290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964290).length < 2 ^ (prefixWord ++ tailWord_1964290).sum := by decide
  have hdescent : baseEnd_1964290 < baseStart_1964290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964297 : List Nat := [1, 2, 1, 1, 3, 5, 3, 2, 1, 1, 3]
def baseStart_1964297 : Nat := 118140960795 + 1964297 * 2 ^ 59
def prefixEnd_1964297 : Nat := 4983230072969 + 3 ^ 40 * 1964297 * 2
def baseEnd_1964297 : Nat := 1008628509184806412653869

theorem tailTrace_1964297 : CollatzResearch.WordTrace tailWord_1964297 prefixEnd_1964297 1008628509184806412653869 := by
  unfold tailWord_1964297
  simp only [CollatzResearch.WordTrace]
  refine ⟨71643797364694919064163145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47762531576463279376108763 71643797364694919064163145)
  ·
    refine ⟨53732848023521189298122359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71643797364694919064163145 53732848023521189298122359)
    ·
      refine ⟨80599272035281783947183539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53732848023521189298122359 80599272035281783947183539)
      ·
        refine ⟨120898908052922675920775309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80599272035281783947183539 120898908052922675920775309)
        ·
          refine ⟨45337090519846003470290741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120898908052922675920775309 45337090519846003470290741)
          ·
            refine ⟨4250352236235562825339757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45337090519846003470290741 4250352236235562825339757)
            ·
              refine ⟨1593882088588336059502409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4250352236235562825339757 1593882088588336059502409)
              ·
                refine ⟨1195411566441252044626807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1593882088588336059502409 1195411566441252044626807)
                ·
                  refine ⟨1793117349661878066940211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1195411566441252044626807 1793117349661878066940211)
                  ·
                    refine ⟨2689676024492817100410317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1793117349661878066940211 2689676024492817100410317)
                    ·
                      refine ⟨1008628509184806412653869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2689676024492817100410317 1008628509184806412653869)
                      ·
                        rfl

theorem cell23_1964297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 2, 1, 1, 3].length) (baseStart_1964297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964297 prefixEnd_1964297 := by exact prefixLift 1964297
  have htrace : WordTrace (prefixWord ++ tailWord_1964297) baseStart_1964297 baseEnd_1964297 := by
    simpa [prefixWord, tailWord_1964297, baseEnd_1964297] using wordTrace_append hprefix tailTrace_1964297
  have hstable : (prefixWord ++ tailWord_1964297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964297).length < 2 ^ (prefixWord ++ tailWord_1964297).sum := by decide
  have hdescent : baseEnd_1964297 < baseStart_1964297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964299 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 6]
def baseStart_1964299 : Nat := 118140960795 + 1964299 * 2 ^ 59
def prefixEnd_1964299 : Nat := 4983230072969 + 3 ^ 40 * 1964299 * 2
def baseEnd_1964299 : Nat := 1008629536146115404828859

theorem tailTrace_1964299 : CollatzResearch.WordTrace tailWord_1964299 prefixEnd_1964299 1008629536146115404828859 := by
  unfold tailWord_1964299
  simp only [CollatzResearch.WordTrace]
  refine ⟨71643870310687673405735951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47762580207125115603823967 71643870310687673405735951)
  ·
    refine ⟨107465805466031510108603927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71643870310687673405735951 107465805466031510108603927)
    ·
      refine ⟨161198708199047265162905891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107465805466031510108603927 161198708199047265162905891)
      ·
        refine ⟨241798062298570897744358837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161198708199047265162905891 241798062298570897744358837)
        ·
          refine ⟨22668568340491021663533641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 241798062298570897744358837 22668568340491021663533641)
          ·
            refine ⟨17001426255368266247650231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22668568340491021663533641 17001426255368266247650231)
            ·
              refine ⟨25502139383052399371475347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17001426255368266247650231 25502139383052399371475347)
              ·
                refine ⟨38253209074578599057213021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25502139383052399371475347 38253209074578599057213021)
                ·
                  refine ⟨14344953402966974646454883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38253209074578599057213021 14344953402966974646454883)
                  ·
                    refine ⟨21517430104450461969682325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14344953402966974646454883 21517430104450461969682325)
                    ·
                      refine ⟨1008629536146115404828859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21517430104450461969682325 1008629536146115404828859)
                      ·
                        rfl

theorem cell23_1964299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 6].length) (baseStart_1964299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964299 prefixEnd_1964299 := by exact prefixLift 1964299
  have htrace : WordTrace (prefixWord ++ tailWord_1964299) baseStart_1964299 baseEnd_1964299 := by
    simpa [prefixWord, tailWord_1964299, baseEnd_1964299] using wordTrace_append hprefix tailTrace_1964299
  have hstable : (prefixWord ++ tailWord_1964299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964299).length < 2 ^ (prefixWord ++ tailWord_1964299).sum := by decide
  have hdescent : baseEnd_1964299 < baseStart_1964299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964309 : List Nat := [1, 3, 2, 1, 2, 1, 3, 10]
def baseStart_1964309 : Nat := 118140960795 + 1964309 * 2 ^ 59
def prefixEnd_1964309 : Nat := 4983230072969 + 3 ^ 40 * 1964309 * 2
def baseEnd_1964309 : Nat := 37356839664913346877919

theorem tailTrace_1964309 : CollatzResearch.WordTrace tailWord_1964309 prefixEnd_1964309 37356839664913346877919 := by
  unfold tailWord_1964309
  simp only [CollatzResearch.WordTrace]
  refine ⟨71644235040651445113599981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47762823360434296742399987 71644235040651445113599981)
  ·
    refine ⟨26866588140244291917599993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71644235040651445113599981 26866588140244291917599993)
    ·
      refine ⟨20149941105183218938199995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26866588140244291917599993 20149941105183218938199995)
      ·
        refine ⟨30224911657774828407299993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20149941105183218938199995 30224911657774828407299993)
        ·
          refine ⟨22668683743331121305474995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30224911657774828407299993 22668683743331121305474995)
          ·
            refine ⟨34003025614996681958212493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22668683743331121305474995 34003025614996681958212493)
            ·
              refine ⟨12751134605623755734329685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34003025614996681958212493 12751134605623755734329685)
              ·
                refine ⟨37356839664913346877919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12751134605623755734329685 37356839664913346877919)
                ·
                  rfl

theorem cell23_1964309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 10].length) (baseStart_1964309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964309 prefixEnd_1964309 := by exact prefixLift 1964309
  have htrace : WordTrace (prefixWord ++ tailWord_1964309) baseStart_1964309 baseEnd_1964309 := by
    simpa [prefixWord, tailWord_1964309, baseEnd_1964309] using wordTrace_append hprefix tailTrace_1964309
  have hstable : (prefixWord ++ tailWord_1964309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964309).length < 2 ^ (prefixWord ++ tailWord_1964309).sum := by decide
  have hdescent : baseEnd_1964309 < baseStart_1964309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964316 : List Nat := [2, 2, 3, 1, 1, 1, 1, 5, 1, 2, 4]
def baseStart_1964316 : Nat := 118140960795 + 1964316 * 2 ^ 59
def prefixEnd_1964316 : Nat := 4983230072969 + 3 ^ 40 * 1964316 * 2
def baseEnd_1964316 : Nat := 1008638265317241838316281

theorem tailTrace_1964316 : CollatzResearch.WordTrace tailWord_1964316 prefixEnd_1964316 1008638265317241838316281 := by
  unfold tailWord_1964316
  simp only [CollatzResearch.WordTrace]
  refine ⟨35822245175813042654552401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47762993567750723539403201 35822245175813042654552401)
  ·
    refine ⟨26866683881859781990914301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35822245175813042654552401 26866683881859781990914301)
    ·
      refine ⟨10075006455697418246592863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26866683881859781990914301 10075006455697418246592863)
      ·
        refine ⟨15112509683546127369889295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10075006455697418246592863 15112509683546127369889295)
        ·
          refine ⟨22668764525319191054833943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15112509683546127369889295 22668764525319191054833943)
          ·
            refine ⟨34003146787978786582250915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22668764525319191054833943 34003146787978786582250915)
            ·
              refine ⟨51004720181968179873376373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34003146787978786582250915 51004720181968179873376373)
              ·
                refine ⟨4781692517059516863129035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51004720181968179873376373 4781692517059516863129035)
                ·
                  refine ⟨7172538775589275294693553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4781692517059516863129035 7172538775589275294693553)
                  ·
                    refine ⟨5379404081691956471020165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7172538775589275294693553 5379404081691956471020165)
                    ·
                      refine ⟨1008638265317241838316281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5379404081691956471020165 1008638265317241838316281)
                      ·
                        rfl

theorem cell23_1964316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_1964316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964316 prefixEnd_1964316 := by exact prefixLift 1964316
  have htrace : WordTrace (prefixWord ++ tailWord_1964316) baseStart_1964316 baseEnd_1964316 := by
    simpa [prefixWord, tailWord_1964316, baseEnd_1964316] using wordTrace_append hprefix tailTrace_1964316
  have hstable : (prefixWord ++ tailWord_1964316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964316).length < 2 ^ (prefixWord ++ tailWord_1964316).sum := by decide
  have hdescent : baseEnd_1964316 < baseStart_1964316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964317 : List Nat := [1, 4, 2, 3, 3, 1, 1, 2, 1, 5]
def baseStart_1964317 : Nat := 118140960795 + 1964317 * 2 ^ 59
def prefixEnd_1964317 : Nat := 4983230072969 + 3 ^ 40 * 1964317 * 2
def baseEnd_1964317 : Nat := 336212926265965444801259

theorem tailTrace_1964317 : CollatzResearch.WordTrace tailWord_1964317 prefixEnd_1964317 336212926265965444801259 := by
  unfold tailWord_1964317
  simp only [CollatzResearch.WordTrace]
  refine ⟨71644526824622462479891205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47763017883081641653260803 71644526824622462479891205)
  ·
    refine ⟨13433348779616711714979601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71644526824622462479891205 13433348779616711714979601)
    ·
      refine ⟨10075011584712533786234701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13433348779616711714979601 10075011584712533786234701)
      ·
        refine ⟨3778129344267200169838013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10075011584712533786234701 3778129344267200169838013)
        ·
          refine ⟨1416798504100200063689255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3778129344267200169838013 1416798504100200063689255)
          ·
            refine ⟨2125197756150300095533883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1416798504100200063689255 2125197756150300095533883)
            ·
              refine ⟨3187796634225450143300825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2125197756150300095533883 3187796634225450143300825)
              ·
                refine ⟨2390847475669087607475619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3187796634225450143300825 2390847475669087607475619)
                ·
                  refine ⟨3586271213503631411213429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2390847475669087607475619 3586271213503631411213429)
                  ·
                    refine ⟨336212926265965444801259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3586271213503631411213429 336212926265965444801259)
                    ·
                      rfl

theorem cell23_1964317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_1964317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964317 prefixEnd_1964317 := by exact prefixLift 1964317
  have htrace : WordTrace (prefixWord ++ tailWord_1964317) baseStart_1964317 baseEnd_1964317 := by
    simpa [prefixWord, tailWord_1964317, baseEnd_1964317] using wordTrace_append hprefix tailTrace_1964317
  have hstable : (prefixWord ++ tailWord_1964317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964317).length < 2 ^ (prefixWord ++ tailWord_1964317).sum := by decide
  have hdescent : baseEnd_1964317 < baseStart_1964317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964320 : List Nat := [2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 4]
def baseStart_1964320 : Nat := 118140960795 + 1964320 * 2 ^ 59
def prefixEnd_1964320 : Nat := 4983230072969 + 3 ^ 40 * 1964320 * 2
def baseEnd_1964320 : Nat := 1008640319239859822666263

theorem tailTrace_1964320 : CollatzResearch.WordTrace tailWord_1964320 prefixEnd_1964320 1008640319239859822666263 := by
  unfold tailWord_1964320
  simp only [CollatzResearch.WordTrace]
  refine ⟨35822318121805796996125207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47763090829074395994833609 35822318121805796996125207)
  ·
    refine ⟨53733477182708695494187811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35822318121805796996125207 53733477182708695494187811)
    ·
      refine ⟨80600215774063043241281717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53733477182708695494187811 80600215774063043241281717)
      ·
        refine ⟨7556270228818410303870161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80600215774063043241281717 7556270228818410303870161)
        ·
          refine ⟨5667202671613807727902621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7556270228818410303870161 5667202671613807727902621)
          ·
            refine ⟨2125201001855177897963483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5667202671613807727902621 2125201001855177897963483)
            ·
              refine ⟨3187801502782766846945225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2125201001855177897963483 3187801502782766846945225)
              ·
                refine ⟨2390851127087075135208919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3187801502782766846945225 2390851127087075135208919)
                ·
                  refine ⟨3586276690630612702813379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2390851127087075135208919 3586276690630612702813379)
                  ·
                    refine ⟨5379415035945919054220069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3586276690630612702813379 5379415035945919054220069)
                    ·
                      refine ⟨1008640319239859822666263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5379415035945919054220069 1008640319239859822666263)
                      ·
                        rfl

theorem cell23_1964320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_1964320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964320 prefixEnd_1964320 := by exact prefixLift 1964320
  have htrace : WordTrace (prefixWord ++ tailWord_1964320) baseStart_1964320 baseEnd_1964320 := by
    simpa [prefixWord, tailWord_1964320, baseEnd_1964320] using wordTrace_append hprefix tailTrace_1964320
  have hstable : (prefixWord ++ tailWord_1964320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964320).length < 2 ^ (prefixWord ++ tailWord_1964320).sum := by decide
  have hdescent : baseEnd_1964320 < baseStart_1964320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964340 : List Nat := [2, 5, 1, 1, 1, 4, 1, 1, 1, 1, 5]
def baseStart_1964340 : Nat := 118140960795 + 1964340 * 2 ^ 59
def prefixEnd_1964340 : Nat := 4983230072969 + 3 ^ 40 * 1964340 * 2
def baseEnd_1964340 : Nat := 1008650588852949744416171

theorem tailTrace_1964340 : CollatzResearch.WordTrace tailWord_1964340 prefixEnd_1964340 1008650588852949744416171 := by
  unfold tailWord_1964340
  simp only [CollatzResearch.WordTrace]
  refine ⟨35822682851769568703989237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47763577135692758271985649 35822682851769568703989237)
  ·
    refine ⟨3358376517353397065998991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35822682851769568703989237 3358376517353397065998991)
    ·
      refine ⟨5037564776030095598998487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3358376517353397065998991 5037564776030095598998487)
      ·
        refine ⟨7556347164045143398497731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5037564776030095598998487 7556347164045143398497731)
        ·
          refine ⟨11334520746067715097746597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7556347164045143398497731 11334520746067715097746597)
          ·
            refine ⟨2125222639887696580827487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11334520746067715097746597 2125222639887696580827487)
            ·
              refine ⟨3187833959831544871241231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2125222639887696580827487 3187833959831544871241231)
              ·
                refine ⟨4781750939747317306861847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3187833959831544871241231 4781750939747317306861847)
                ·
                  refine ⟨7172626409620975960292771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4781750939747317306861847 7172626409620975960292771)
                  ·
                    refine ⟨10758939614431463940439157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7172626409620975960292771 10758939614431463940439157)
                    ·
                      refine ⟨1008650588852949744416171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10758939614431463940439157 1008650588852949744416171)
                      ·
                        rfl

theorem cell23_1964340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_1964340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964340 prefixEnd_1964340 := by exact prefixLift 1964340
  have htrace : WordTrace (prefixWord ++ tailWord_1964340) baseStart_1964340 baseEnd_1964340 := by
    simpa [prefixWord, tailWord_1964340, baseEnd_1964340] using wordTrace_append hprefix tailTrace_1964340
  have hstable : (prefixWord ++ tailWord_1964340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964340).length < 2 ^ (prefixWord ++ tailWord_1964340).sum := by decide
  have hdescent : baseEnd_1964340 < baseStart_1964340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964370 : List Nat := [3, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3]
def baseStart_1964370 : Nat := 118140960795 + 1964370 * 2 ^ 59
def prefixEnd_1964370 : Nat := 4983230072969 + 3 ^ 40 * 1964370 * 2
def baseEnd_1964370 : Nat := 1008665993272584627041033

theorem tailTrace_1964370 : CollatzResearch.WordTrace tailWord_1964370 prefixEnd_1964370 1008665993272584627041033 := by
  unfold tailWord_1964370
  simp only [CollatzResearch.WordTrace]
  refine ⟨17911614973357613132892641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47764306595620301687713709 17911614973357613132892641)
  ·
    refine ⟨13433711230018209849669481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17911614973357613132892641 13433711230018209849669481)
    ·
      refine ⟨10075283422513657387252111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13433711230018209849669481 10075283422513657387252111)
      ·
        refine ⟨15112925133770486080878167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10075283422513657387252111 15112925133770486080878167)
        ·
          refine ⟨22669387700655729121317251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15112925133770486080878167 22669387700655729121317251)
          ·
            refine ⟨34004081550983593681975877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22669387700655729121317251 34004081550983593681975877)
            ·
              refine ⟨6375765290809423815370477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34004081550983593681975877 6375765290809423815370477)
              ·
                refine ⟨2390911984053533930763929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6375765290809423815370477 2390911984053533930763929)
                ·
                  refine ⟨1793183988040150448072947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2390911984053533930763929 1793183988040150448072947)
                  ·
                    refine ⟨2689775982060225672109421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1793183988040150448072947 2689775982060225672109421)
                    ·
                      refine ⟨1008665993272584627041033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2689775982060225672109421 1008665993272584627041033)
                      ·
                        rfl

theorem cell23_1964370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_1964370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964370 prefixEnd_1964370 := by exact prefixLift 1964370
  have htrace : WordTrace (prefixWord ++ tailWord_1964370) baseStart_1964370 baseEnd_1964370 := by
    simpa [prefixWord, tailWord_1964370, baseEnd_1964370] using wordTrace_append hprefix tailTrace_1964370
  have hstable : (prefixWord ++ tailWord_1964370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964370).length < 2 ^ (prefixWord ++ tailWord_1964370).sum := by decide
  have hdescent : baseEnd_1964370 < baseStart_1964370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964393 : List Nat := [1, 2, 1, 1, 1, 3, 3, 4, 1, 4, 2]
def baseStart_1964393 : Nat := 118140960795 + 1964393 * 2 ^ 59
def prefixEnd_1964393 : Nat := 4983230072969 + 3 ^ 40 * 1964393 * 2
def baseEnd_1964393 : Nat := 1008677803327638037053427

theorem tailTrace_1964393 : CollatzResearch.WordTrace tailWord_1964393 prefixEnd_1964393 1008677803327638037053427 := by
  unfold tailWord_1964393
  simp only [CollatzResearch.WordTrace]
  refine ⟨71647298772347127459657833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47764865848231418306438555 71647298772347127459657833)
  ·
    refine ⟨53735474079260345594743375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71647298772347127459657833 53735474079260345594743375)
    ·
      refine ⟨80603211118890518392115063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53735474079260345594743375 80603211118890518392115063)
      ·
        refine ⟨120904816678335777588172595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80603211118890518392115063 120904816678335777588172595)
        ·
          refine ⟨181357225017503666382258893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120904816678335777588172595 181357225017503666382258893)
          ·
            refine ⟨68008959381563874893347085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181357225017503666382258893 68008959381563874893347085)
            ·
              refine ⟨25503359768086453085005157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68008959381563874893347085 25503359768086453085005157)
              ·
                refine ⟨4781879956516209953438467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25503359768086453085005157 4781879956516209953438467)
                ·
                  refine ⟨7172819934774314930157701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4781879956516209953438467 7172819934774314930157701)
                  ·
                    refine ⟨1344903737770184049404569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7172819934774314930157701 1344903737770184049404569)
                    ·
                      refine ⟨1008677803327638037053427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1344903737770184049404569 1008677803327638037053427)
                      ·
                        rfl

theorem cell23_1964393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 4, 2].length) (baseStart_1964393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964393 prefixEnd_1964393 := by exact prefixLift 1964393
  have htrace : WordTrace (prefixWord ++ tailWord_1964393) baseStart_1964393 baseEnd_1964393 := by
    simpa [prefixWord, tailWord_1964393, baseEnd_1964393] using wordTrace_append hprefix tailTrace_1964393
  have hstable : (prefixWord ++ tailWord_1964393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964393).length < 2 ^ (prefixWord ++ tailWord_1964393).sum := by decide
  have hdescent : baseEnd_1964393 < baseStart_1964393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964473 : List Nat := [1, 2, 1, 4, 3, 2, 1, 1, 1, 2, 5]
def baseStart_1964473 : Nat := 118140960795 + 1964473 * 2 ^ 59
def prefixEnd_1964473 : Nat := 4983230072969 + 3 ^ 40 * 1964473 * 2
def baseEnd_1964473 : Nat := 1008718881779997724053059

theorem tailTrace_1964473 : CollatzResearch.WordTrace tailWord_1964473 prefixEnd_1964473 1008718881779997724053059 := by
  unfold tailWord_1964473
  simp only [CollatzResearch.WordTrace]
  refine ⟨71650216612057301122570073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47766811074704867415046715 71650216612057301122570073)
  ·
    refine ⟨53737662459042975841927555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71650216612057301122570073 53737662459042975841927555)
    ·
      refine ⟨80606493688564463762891333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53737662459042975841927555 80606493688564463762891333)
      ·
        refine ⟨15113717566605836955542125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80606493688564463762891333 15113717566605836955542125)
        ·
          refine ⟨5667644087477188858328297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15113717566605836955542125 5667644087477188858328297)
          ·
            refine ⟨4250733065607891643746223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5667644087477188858328297 4250733065607891643746223)
            ·
              refine ⟨6376099598411837465619335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4250733065607891643746223 6376099598411837465619335)
              ·
                refine ⟨9564149397617756198429003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6376099598411837465619335 9564149397617756198429003)
                ·
                  refine ⟨14346224096426634297643505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9564149397617756198429003 14346224096426634297643505)
                  ·
                    refine ⟨10759668072319975723232629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14346224096426634297643505 10759668072319975723232629)
                    ·
                      refine ⟨1008718881779997724053059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10759668072319975723232629 1008718881779997724053059)
                      ·
                        rfl

theorem cell23_1964473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_1964473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964473 prefixEnd_1964473 := by exact prefixLift 1964473
  have htrace : WordTrace (prefixWord ++ tailWord_1964473) baseStart_1964473 baseEnd_1964473 := by
    simpa [prefixWord, tailWord_1964473, baseEnd_1964473] using wordTrace_append hprefix tailTrace_1964473
  have hstable : (prefixWord ++ tailWord_1964473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964473).length < 2 ^ (prefixWord ++ tailWord_1964473).sum := by decide
  have hdescent : baseEnd_1964473 < baseStart_1964473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964483 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 1, 6, 2]
def baseStart_1964483 : Nat := 118140960795 + 1964483 * 2 ^ 59
def prefixEnd_1964483 : Nat := 4983230072969 + 3 ^ 40 * 1964483 * 2
def baseEnd_1964483 : Nat := 1008724016586542684928013

theorem tailTrace_1964483 : CollatzResearch.WordTrace tailWord_1964483 prefixEnd_1964483 1008724016586542684928013 := by
  unfold tailWord_1964483
  simp only [CollatzResearch.WordTrace]
  refine ⟨71650581342021072830434103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47767054228014048553622735 71650581342021072830434103)
  ·
    refine ⟨107475872013031609245651155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71650581342021072830434103 107475872013031609245651155)
    ·
      refine ⟨161213808019547413868476733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107475872013031609245651155 161213808019547413868476733)
      ·
        refine ⟨60455178007330280200678775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161213808019547413868476733 60455178007330280200678775)
        ·
          refine ⟨90682767010995420301018163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60455178007330280200678775 90682767010995420301018163)
          ·
            refine ⟨136024150516493130451527245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90682767010995420301018163 136024150516493130451527245)
            ·
              refine ⟨51009056443684923919322717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136024150516493130451527245 51009056443684923919322717)
              ·
                refine ⟨19128396166381846469746019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51009056443684923919322717 19128396166381846469746019)
                ·
                  refine ⟨28692594249572769704619029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19128396166381846469746019 28692594249572769704619029)
                  ·
                    refine ⟨1344965355448723579904017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28692594249572769704619029 1344965355448723579904017)
                    ·
                      refine ⟨1008724016586542684928013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1344965355448723579904017 1008724016586542684928013)
                      ·
                        rfl

theorem cell23_1964483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 6, 2].length) (baseStart_1964483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964483 prefixEnd_1964483 := by exact prefixLift 1964483
  have htrace : WordTrace (prefixWord ++ tailWord_1964483) baseStart_1964483 baseEnd_1964483 := by
    simpa [prefixWord, tailWord_1964483, baseEnd_1964483] using wordTrace_append hprefix tailTrace_1964483
  have hstable : (prefixWord ++ tailWord_1964483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964483).length < 2 ^ (prefixWord ++ tailWord_1964483).sum := by decide
  have hdescent : baseEnd_1964483 < baseStart_1964483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964500 : List Nat := [2, 4, 1, 2, 2, 1, 1, 3, 2, 1, 4]
def baseStart_1964500 : Nat := 118140960795 + 1964500 * 2 ^ 59
def prefixEnd_1964500 : Nat := 4983230072969 + 3 ^ 40 * 1964500 * 2
def baseEnd_1964500 : Nat := 1008732745757669118415435

theorem tailTrace_1964500 : CollatzResearch.WordTrace tailWord_1964500 prefixEnd_1964500 1008732745757669118415435 := by
  unfold tailWord_1964500
  simp only [CollatzResearch.WordTrace]
  refine ⟨35825600691479742366901477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47767467588639656489201969 35825600691479742366901477)
  ·
    refine ⟨6717300129652451693794027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35825600691479742366901477 6717300129652451693794027)
    ·
      refine ⟨10075950194478677540691041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6717300129652451693794027 10075950194478677540691041)
      ·
        refine ⟨7556962645859008155518281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10075950194478677540691041 7556962645859008155518281)
        ·
          refine ⟨5667721984394256116638711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7556962645859008155518281 5667721984394256116638711)
          ·
            refine ⟨8501582976591384174958067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5667721984394256116638711 8501582976591384174958067)
            ·
              refine ⟨12752374464887076262437101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8501582976591384174958067 12752374464887076262437101)
              ·
                refine ⟨4782140424332653598413913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12752374464887076262437101 4782140424332653598413913)
                ·
                  refine ⟨3586605318249490198810435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4782140424332653598413913 3586605318249490198810435)
                  ·
                    refine ⟨5379907977374235298215653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3586605318249490198810435 5379907977374235298215653)
                    ·
                      refine ⟨1008732745757669118415435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5379907977374235298215653 1008732745757669118415435)
                      ·
                        rfl

theorem cell23_1964500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_1964500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964500 prefixEnd_1964500 := by exact prefixLift 1964500
  have htrace : WordTrace (prefixWord ++ tailWord_1964500) baseStart_1964500 baseEnd_1964500 := by
    simpa [prefixWord, tailWord_1964500, baseEnd_1964500] using wordTrace_append hprefix tailTrace_1964500
  have hstable : (prefixWord ++ tailWord_1964500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964500).length < 2 ^ (prefixWord ++ tailWord_1964500).sum := by decide
  have hdescent : baseEnd_1964500 < baseStart_1964500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964520 : List Nat := [2, 1, 4, 1, 1, 3, 2, 2, 2, 2, 3]
def baseStart_1964520 : Nat := 118140960795 + 1964520 * 2 ^ 59
def prefixEnd_1964520 : Nat := 4983230072969 + 3 ^ 40 * 1964520 * 2
def baseEnd_1964520 : Nat := 1008743015370759040165343

theorem tailTrace_1964520 : CollatzResearch.WordTrace tailWord_1964520 prefixEnd_1964520 1008743015370759040165343 := by
  unfold tailWord_1964520
  simp only [CollatzResearch.WordTrace]
  refine ⟨35825965421443514074765507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47767953895258018766354009 35825965421443514074765507)
  ·
    refine ⟨53738948132165271112148261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35825965421443514074765507 53738948132165271112148261)
    ·
      refine ⟨10076052774780988333527799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53738948132165271112148261 10076052774780988333527799)
      ·
        refine ⟨15114079162171482500291699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10076052774780988333527799 15114079162171482500291699)
        ·
          refine ⟨22671118743257223750437549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15114079162171482500291699 22671118743257223750437549)
          ·
            refine ⟨8501669528721458906414081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22671118743257223750437549 8501669528721458906414081)
            ·
              refine ⟨6376252146541094179810561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8501669528721458906414081 6376252146541094179810561)
              ·
                refine ⟨4782189109905820634857921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6376252146541094179810561 4782189109905820634857921)
                ·
                  refine ⟨3586641832429365476143441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4782189109905820634857921 3586641832429365476143441)
                  ·
                    refine ⟨2689981374322024107107581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3586641832429365476143441 2689981374322024107107581)
                    ·
                      refine ⟨1008743015370759040165343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2689981374322024107107581 1008743015370759040165343)
                      ·
                        rfl

theorem cell23_1964520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_1964520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964520 prefixEnd_1964520 := by exact prefixLift 1964520
  have htrace : WordTrace (prefixWord ++ tailWord_1964520) baseStart_1964520 baseEnd_1964520 := by
    simpa [prefixWord, tailWord_1964520, baseEnd_1964520] using wordTrace_append hprefix tailTrace_1964520
  have hstable : (prefixWord ++ tailWord_1964520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964520).length < 2 ^ (prefixWord ++ tailWord_1964520).sum := by decide
  have hdescent : baseEnd_1964520 < baseStart_1964520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964523 : List Nat := [1, 1, 1, 1, 2, 3, 6, 2, 6]
def baseStart_1964523 : Nat := 118140960795 + 1964523 * 2 ^ 59
def prefixEnd_1964523 : Nat := 4983230072969 + 3 ^ 40 * 1964523 * 2
def baseEnd_1964523 : Nat := 112082728423635836491981

theorem tailTrace_1964523 : CollatzResearch.WordTrace tailWord_1964523 prefixEnd_1964523 112082728423635836491981 := by
  unfold tailWord_1964523
  simp only [CollatzResearch.WordTrace]
  refine ⟨71652040261876159661890223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47768026841250773107926815 71652040261876159661890223)
  ·
    refine ⟨107478060392814239492835335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71652040261876159661890223 107478060392814239492835335)
    ·
      refine ⟨161217090589221359239253003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107478060392814239492835335 161217090589221359239253003)
      ·
        refine ⟨241825635883832038858879505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161217090589221359239253003 241825635883832038858879505)
        ·
          refine ⟨181369226912874029144159629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241825635883832038858879505 181369226912874029144159629)
          ·
            refine ⟨68013460092327760929059861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181369226912874029144159629 68013460092327760929059861)
            ·
              refine ⟨3188130941827863793549681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68013460092327760929059861 3188130941827863793549681)
              ·
                refine ⟨2391098206370897845162261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3188130941827863793549681 2391098206370897845162261)
                ·
                  refine ⟨112082728423635836491981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2391098206370897845162261 112082728423635836491981)
                  ·
                    rfl

theorem cell23_1964523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 6].length) (baseStart_1964523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964523 prefixEnd_1964523 := by exact prefixLift 1964523
  have htrace : WordTrace (prefixWord ++ tailWord_1964523) baseStart_1964523 baseEnd_1964523 := by
    simpa [prefixWord, tailWord_1964523, baseEnd_1964523] using wordTrace_append hprefix tailTrace_1964523
  have hstable : (prefixWord ++ tailWord_1964523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964523).length < 2 ^ (prefixWord ++ tailWord_1964523).sum := by decide
  have hdescent : baseEnd_1964523 < baseStart_1964523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964584 : List Nat := [2, 1, 5, 2, 1, 2, 2, 1, 3, 1, 3]
def baseStart_1964584 : Nat := 118140960795 + 1964584 * 2 ^ 59
def prefixEnd_1964584 : Nat := 4983230072969 + 3 ^ 40 * 1964584 * 2
def baseEnd_1964584 : Nat := 1008775878132646789765049

theorem tailTrace_1964584 : CollatzResearch.WordTrace tailWord_1964584 prefixEnd_1964584 1008775878132646789765049 := by
  unfold tailWord_1964584
  simp only [CollatzResearch.WordTrace]
  refine ⟨35827132557327583539930403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47769510076436778053240537 35827132557327583539930403)
  ·
    refine ⟨53740698835991375309895605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35827132557327583539930403 53740698835991375309895605)
    ·
      refine ⟨5038190515874191435302713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53740698835991375309895605 5038190515874191435302713)
      ·
        refine ⟨3778642886905643576477035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5038190515874191435302713 3778642886905643576477035)
        ·
          refine ⟨5667964330358465364715553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3778642886905643576477035 5667964330358465364715553)
          ·
            refine ⟨4250973247768849023536665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5667964330358465364715553 4250973247768849023536665)
            ·
              refine ⟨3188229935826636767652499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4250973247768849023536665 3188229935826636767652499)
              ·
                refine ⟨4782344903739955151478749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3188229935826636767652499 4782344903739955151478749)
                ·
                  refine ⟨1793379338902483181804531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4782344903739955151478749 1793379338902483181804531)
                  ·
                    refine ⟨2690069008353724772706797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1793379338902483181804531 2690069008353724772706797)
                    ·
                      refine ⟨1008775878132646789765049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2690069008353724772706797 1008775878132646789765049)
                      ·
                        rfl

theorem cell23_1964584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_1964584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964584 prefixEnd_1964584 := by exact prefixLift 1964584
  have htrace : WordTrace (prefixWord ++ tailWord_1964584) baseStart_1964584 baseEnd_1964584 := by
    simpa [prefixWord, tailWord_1964584, baseEnd_1964584] using wordTrace_append hprefix tailTrace_1964584
  have hstable : (prefixWord ++ tailWord_1964584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964584).length < 2 ^ (prefixWord ++ tailWord_1964584).sum := by decide
  have hdescent : baseEnd_1964584 < baseStart_1964584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964593 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 3, 1, 5]
def baseStart_1964593 : Nat := 118140960795 + 1964593 * 2 ^ 59
def prefixEnd_1964593 : Nat := 4983230072969 + 3 ^ 40 * 1964593 * 2
def baseEnd_1964593 : Nat := 1008780499458537254552507

theorem tailTrace_1964593 : CollatzResearch.WordTrace tailWord_1964593 prefixEnd_1964593 1008780499458537254552507 := by
  unfold tailWord_1964593
  simp only [CollatzResearch.WordTrace]
  refine ⟨71654593371622561616938433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47769728914415041077958955 71654593371622561616938433)
  ·
    refine ⟨53740945028716921212703825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71654593371622561616938433 53740945028716921212703825)
    ·
      refine ⟨40305708771537690909527869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53740945028716921212703825 40305708771537690909527869)
      ·
        refine ⟨15114640789326634091072951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40305708771537690909527869 15114640789326634091072951)
        ·
          refine ⟨22671961183989951136609427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15114640789326634091072951 22671961183989951136609427)
          ·
            refine ⟨34007941775984926704914141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22671961183989951136609427 34007941775984926704914141)
            ·
              refine ⟨12752978165994347514342803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34007941775984926704914141 12752978165994347514342803)
              ·
                refine ⟨19129467248991521271514205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12752978165994347514342803 19129467248991521271514205)
                ·
                  refine ⟨7173550218371820476817827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19129467248991521271514205 7173550218371820476817827)
                  ·
                    refine ⟨10760325327557730715226741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7173550218371820476817827 10760325327557730715226741)
                    ·
                      refine ⟨1008780499458537254552507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10760325327557730715226741 1008780499458537254552507)
                      ·
                        rfl

theorem cell23_1964593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_1964593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964593 prefixEnd_1964593 := by exact prefixLift 1964593
  have htrace : WordTrace (prefixWord ++ tailWord_1964593) baseStart_1964593 baseEnd_1964593 := by
    simpa [prefixWord, tailWord_1964593, baseEnd_1964593] using wordTrace_append hprefix tailTrace_1964593
  have hstable : (prefixWord ++ tailWord_1964593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964593).length < 2 ^ (prefixWord ++ tailWord_1964593).sum := by decide
  have hdescent : baseEnd_1964593 < baseStart_1964593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964607 : List Nat := [1, 1, 2, 2, 3, 2, 1, 4, 3, 2, 2]
def baseStart_1964607 : Nat := 118140960795 + 1964607 * 2 ^ 59
def prefixEnd_1964607 : Nat := 4983230072969 + 3 ^ 40 * 1964607 * 2
def baseEnd_1964607 : Nat := 1008787688187700199777443

theorem tailTrace_1964607 : CollatzResearch.WordTrace tailWord_1964607 prefixEnd_1964607 1008787688187700199777443 := by
  unfold tailWord_1964607
  simp only [CollatzResearch.WordTrace]
  refine ⟨71655103993571842007948075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47770069329047894671965383 71655103993571842007948075)
  ·
    refine ⟨107482655990357763011922113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71655103993571842007948075 107482655990357763011922113)
    ·
      refine ⟨80611991992768322258941585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107482655990357763011922113 80611991992768322258941585)
      ·
        refine ⟨60458993994576241694206189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80611991992768322258941585 60458993994576241694206189)
        ·
          refine ⟨22672122747966090635327321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60458993994576241694206189 22672122747966090635327321)
          ·
            refine ⟨17004092060974567976495491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22672122747966090635327321 17004092060974567976495491)
            ·
              refine ⟨25506138091461851964743237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17004092060974567976495491 25506138091461851964743237)
              ·
                refine ⟨4782400892149097243389357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25506138091461851964743237 4782400892149097243389357)
                ·
                  refine ⟨1793400334555911466271009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4782400892149097243389357 1793400334555911466271009)
                  ·
                    refine ⟨1345050250916933599703257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1793400334555911466271009 1345050250916933599703257)
                    ·
                      refine ⟨1008787688187700199777443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1345050250916933599703257 1008787688187700199777443)
                      ·
                        rfl

theorem cell23_1964607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 3, 2, 2].length) (baseStart_1964607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964607 prefixEnd_1964607 := by exact prefixLift 1964607
  have htrace : WordTrace (prefixWord ++ tailWord_1964607) baseStart_1964607 baseEnd_1964607 := by
    simpa [prefixWord, tailWord_1964607, baseEnd_1964607] using wordTrace_append hprefix tailTrace_1964607
  have hstable : (prefixWord ++ tailWord_1964607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964607).length < 2 ^ (prefixWord ++ tailWord_1964607).sum := by decide
  have hdescent : baseEnd_1964607 < baseStart_1964607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964613 : List Nat := [1, 3, 1, 1, 1, 6, 1, 9]
def baseStart_1964613 : Nat := 118140960795 + 1964613 * 2 ^ 59
def prefixEnd_1964613 : Nat := 4983230072969 + 3 ^ 40 * 1964613 * 2
def baseEnd_1964613 : Nat := 37362621076726932455645

theorem tailTrace_1964613 : CollatzResearch.WordTrace tailWord_1964613 prefixEnd_1964613 37362621076726932455645 := by
  unfold tailWord_1964613
  simp only [CollatzResearch.WordTrace]
  refine ⟨71655322831550105032666493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47770215221033403355110995 71655322831550105032666493)
  ·
    refine ⟨26870746061831289387249935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71655322831550105032666493 26870746061831289387249935)
    ·
      refine ⟨40306119092746934080874903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26870746061831289387249935 40306119092746934080874903)
      ·
        refine ⟨60459178639120401121312355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40306119092746934080874903 60459178639120401121312355)
        ·
          refine ⟨90688767958680601681968533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60459178639120401121312355 90688767958680601681968533)
          ·
            refine ⟨4251035998063153203842275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90688767958680601681968533 4251035998063153203842275)
            ·
              refine ⟨6376553997094729805763413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4251035998063153203842275 6376553997094729805763413)
              ·
                refine ⟨37362621076726932455645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6376553997094729805763413 37362621076726932455645)
                ·
                  rfl

theorem cell23_1964613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 9].length) (baseStart_1964613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964613 prefixEnd_1964613 := by exact prefixLift 1964613
  have htrace : WordTrace (prefixWord ++ tailWord_1964613) baseStart_1964613 baseEnd_1964613 := by
    simpa [prefixWord, tailWord_1964613, baseEnd_1964613] using wordTrace_append hprefix tailTrace_1964613
  have hstable : (prefixWord ++ tailWord_1964613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964613).length < 2 ^ (prefixWord ++ tailWord_1964613).sum := by decide
  have hdescent : baseEnd_1964613 < baseStart_1964613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964624 : List Nat := [2, 1, 1, 1, 1, 3, 2, 7, 1, 2, 2]
def baseStart_1964624 : Nat := 118140960795 + 1964624 * 2 ^ 59
def prefixEnd_1964624 : Nat := 4983230072969 + 3 ^ 40 * 1964624 * 2
def baseEnd_1964624 : Nat := 1008796417358826633264865

theorem tailTrace_1964624 : CollatzResearch.WordTrace tailWord_1964624 prefixEnd_1964624 1008796417358826633264865 := by
  unfold tailWord_1964624
  simp only [CollatzResearch.WordTrace]
  refine ⟨35827862017255126955658463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47770482689673502607544617 35827862017255126955658463)
  ·
    refine ⟨53741793025882690433487695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35827862017255126955658463 53741793025882690433487695)
    ·
      refine ⟨80612689538824035650231543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53741793025882690433487695 80612689538824035650231543)
      ·
        refine ⟨120919034308236053475347315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80612689538824035650231543 120919034308236053475347315)
        ·
          refine ⟨181378551462354080213020973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120919034308236053475347315 181378551462354080213020973)
          ·
            refine ⟨68016956798382780079882865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181378551462354080213020973 68016956798382780079882865)
            ·
              refine ⟨51012717598787085059912149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68016956798382780079882865 51012717598787085059912149)
              ·
                refine ⟨1195610568721572306091691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 51012717598787085059912149 1195610568721572306091691)
                ·
                  refine ⟨1793415853082358459137537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1195610568721572306091691 1793415853082358459137537)
                  ·
                    refine ⟨1345061889811768844353153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1793415853082358459137537 1345061889811768844353153)
                    ·
                      refine ⟨1008796417358826633264865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1345061889811768844353153 1008796417358826633264865)
                      ·
                        rfl

theorem cell23_1964624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 7, 1, 2, 2].length) (baseStart_1964624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964624 prefixEnd_1964624 := by exact prefixLift 1964624
  have htrace : WordTrace (prefixWord ++ tailWord_1964624) baseStart_1964624 baseEnd_1964624 := by
    simpa [prefixWord, tailWord_1964624, baseEnd_1964624] using wordTrace_append hprefix tailTrace_1964624
  have hstable : (prefixWord ++ tailWord_1964624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964624).length < 2 ^ (prefixWord ++ tailWord_1964624).sum := by decide
  have hdescent : baseEnd_1964624 < baseStart_1964624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964643 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 2, 7]
def baseStart_1964643 : Nat := 118140960795 + 1964643 * 2 ^ 59
def prefixEnd_1964643 : Nat := 4983230072969 + 3 ^ 40 * 1964643 * 2
def baseEnd_1964643 : Nat := 336268724497087352975759

theorem tailTrace_1964643 : CollatzResearch.WordTrace tailWord_1964643 prefixEnd_1964643 336268724497087352975759 := by
  unfold tailWord_1964643
  simp only [CollatzResearch.WordTrace]
  refine ⟨71656417021441420156258583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47770944680960946770839055 71656417021441420156258583)
  ·
    refine ⟨107484625532162130234387875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71656417021441420156258583 107484625532162130234387875)
    ·
      refine ⟨161226938298243195351581813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107484625532162130234387875 161226938298243195351581813)
      ·
        refine ⟨15115025465460299564210795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161226938298243195351581813 15115025465460299564210795)
        ·
          refine ⟨22672538198190449346316193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15115025465460299564210795 22672538198190449346316193)
          ·
            refine ⟨17004403648642837009737145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22672538198190449346316193 17004403648642837009737145)
            ·
              refine ⟨12753302736482127757302859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17004403648642837009737145 12753302736482127757302859)
              ·
                refine ⟨19129954104723191635954289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12753302736482127757302859 19129954104723191635954289)
                ·
                  refine ⟨14347465578542393726965717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19129954104723191635954289 14347465578542393726965717)
                  ·
                    refine ⟨336268724497087352975759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14347465578542393726965717 336268724497087352975759)
                    ·
                      rfl

theorem cell23_1964643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 7].length) (baseStart_1964643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964643 prefixEnd_1964643 := by exact prefixLift 1964643
  have htrace : WordTrace (prefixWord ++ tailWord_1964643) baseStart_1964643 baseEnd_1964643 := by
    simpa [prefixWord, tailWord_1964643, baseEnd_1964643] using wordTrace_append hprefix tailTrace_1964643
  have hstable : (prefixWord ++ tailWord_1964643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964643).length < 2 ^ (prefixWord ++ tailWord_1964643).sum := by decide
  have hdescent : baseEnd_1964643 < baseStart_1964643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964661 : List Nat := [1, 3, 4, 2, 2, 2, 1, 2, 1, 2, 3]
def baseStart_1964661 : Nat := 118140960795 + 1964661 * 2 ^ 59
def prefixEnd_1964661 : Nat := 4983230072969 + 3 ^ 40 * 1964661 * 2
def baseEnd_1964661 : Nat := 1008815416143042988502195

theorem tailTrace_1964661 : CollatzResearch.WordTrace tailWord_1964661 prefixEnd_1964661 1008815416143042988502195 := by
  unfold tailWord_1964661
  simp only [CollatzResearch.WordTrace]
  refine ⟨71657073535376209230413837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47771382356917472820275891 71657073535376209230413837)
  ·
    refine ⟨26871402575766078461405189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71657073535376209230413837 26871402575766078461405189)
    ·
      refine ⟨5038387982956139711513473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26871402575766078461405189 5038387982956139711513473)
      ·
        refine ⟨3778790987217104783635105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5038387982956139711513473 3778790987217104783635105)
        ·
          refine ⟨2834093240412828587726329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3778790987217104783635105 2834093240412828587726329)
          ·
            refine ⟨2125569930309621440794747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2834093240412828587726329 2125569930309621440794747)
            ·
              refine ⟨3188354895464432161192121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2125569930309621440794747 3188354895464432161192121)
              ·
                refine ⟨2391266171598324120894091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3188354895464432161192121 2391266171598324120894091)
                ·
                  refine ⟨3586899257397486181341137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2391266171598324120894091 3586899257397486181341137)
                  ·
                    refine ⟨2690174443048114636005853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3586899257397486181341137 2690174443048114636005853)
                    ·
                      refine ⟨1008815416143042988502195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2690174443048114636005853 1008815416143042988502195)
                      ·
                        rfl

theorem cell23_1964661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_1964661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964661 prefixEnd_1964661 := by exact prefixLift 1964661
  have htrace : WordTrace (prefixWord ++ tailWord_1964661) baseStart_1964661 baseEnd_1964661 := by
    simpa [prefixWord, tailWord_1964661, baseEnd_1964661] using wordTrace_append hprefix tailTrace_1964661
  have hstable : (prefixWord ++ tailWord_1964661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964661).length < 2 ^ (prefixWord ++ tailWord_1964661).sum := by decide
  have hdescent : baseEnd_1964661 < baseStart_1964661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964667 : List Nat := [1, 1, 1, 1, 1, 4, 2, 6, 1, 3, 2]
def baseStart_1964667 : Nat := 118140960795 + 1964667 * 2 ^ 59
def prefixEnd_1964667 : Nat := 4983230072969 + 3 ^ 40 * 1964667 * 2
def baseEnd_1964667 : Nat := 1008818497026969965027167

theorem tailTrace_1964667 : CollatzResearch.WordTrace tailWord_1964667 prefixEnd_1964667 1008818497026969965027167 := by
  unfold tailWord_1964667
  simp only [CollatzResearch.WordTrace]
  refine ⟨71657292373354472255132255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47771528248902981503421503 71657292373354472255132255)
  ·
    refine ⟨107485938560031708382698383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71657292373354472255132255 107485938560031708382698383)
    ·
      refine ⟨161228907840047562574047575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107485938560031708382698383 161228907840047562574047575)
      ·
        refine ⟨241843361760071343861071363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161228907840047562574047575 241843361760071343861071363)
        ·
          refine ⟨362765042640107015791607045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241843361760071343861071363 362765042640107015791607045)
          ·
            refine ⟨68018445495020065460926321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 362765042640107015791607045 68018445495020065460926321)
            ·
              refine ⟨51013834121265049095694741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68018445495020065460926321 51013834121265049095694741)
              ·
                refine ⟨2391273474434299176360691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51013834121265049095694741 2391273474434299176360691)
                ·
                  refine ⟨3586910211651448764541037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2391273474434299176360691 3586910211651448764541037)
                  ·
                    refine ⟨1345091329369293286702889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3586910211651448764541037 1345091329369293286702889)
                    ·
                      refine ⟨1008818497026969965027167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1345091329369293286702889 1008818497026969965027167)
                      ·
                        rfl

theorem cell23_1964667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 3, 2].length) (baseStart_1964667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964667 prefixEnd_1964667 := by exact prefixLift 1964667
  have htrace : WordTrace (prefixWord ++ tailWord_1964667) baseStart_1964667 baseEnd_1964667 := by
    simpa [prefixWord, tailWord_1964667, baseEnd_1964667] using wordTrace_append hprefix tailTrace_1964667
  have hstable : (prefixWord ++ tailWord_1964667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964667).length < 2 ^ (prefixWord ++ tailWord_1964667).sum := by decide
  have hdescent : baseEnd_1964667 < baseStart_1964667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964683 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 5]
def baseStart_1964683 : Nat := 118140960795 + 1964683 * 2 ^ 59
def prefixEnd_1964683 : Nat := 4983230072969 + 3 ^ 40 * 1964683 * 2
def baseEnd_1964683 : Nat := 1008826712717441902427093

theorem tailTrace_1964683 : CollatzResearch.WordTrace tailWord_1964683 prefixEnd_1964683 1008826712717441902427093 := by
  unfold tailWord_1964683
  simp only [CollatzResearch.WordTrace]
  refine ⟨71657875941296506987714703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47771917294197671325143135 71657875941296506987714703)
  ·
    refine ⟨107486813911944760481572055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71657875941296506987714703 107486813911944760481572055)
    ·
      refine ⟨161230220867917140722358083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107486813911944760481572055 161230220867917140722358083)
      ·
        refine ⟨241845331301875711083537125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161230220867917140722358083 241845331301875711083537125)
        ·
          refine ⟨45345999619101695828163211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 241845331301875711083537125 45345999619101695828163211)
          ·
            refine ⟨68018999428652543742244817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45345999619101695828163211 68018999428652543742244817)
            ·
              refine ⟨51014249571489407806683613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68018999428652543742244817 51014249571489407806683613)
              ·
                refine ⟨19130343589308527927506355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51014249571489407806683613 19130343589308527927506355)
                ·
                  refine ⟨28695515383962791891259533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19130343589308527927506355 28695515383962791891259533)
                  ·
                    refine ⟨10760818268986046959222325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28695515383962791891259533 10760818268986046959222325)
                    ·
                      refine ⟨1008826712717441902427093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10760818268986046959222325 1008826712717441902427093)
                      ·
                        rfl

theorem cell23_1964683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 5].length) (baseStart_1964683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964683 prefixEnd_1964683 := by exact prefixLift 1964683
  have htrace : WordTrace (prefixWord ++ tailWord_1964683) baseStart_1964683 baseEnd_1964683 := by
    simpa [prefixWord, tailWord_1964683, baseEnd_1964683] using wordTrace_append hprefix tailTrace_1964683
  have hstable : (prefixWord ++ tailWord_1964683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964683).length < 2 ^ (prefixWord ++ tailWord_1964683).sum := by decide
  have hdescent : baseEnd_1964683 < baseStart_1964683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964693 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 1, 5, 6]
def baseStart_1964693 : Nat := 118140960795 + 1964693 * 2 ^ 59
def prefixEnd_1964693 : Nat := 4983230072969 + 3 ^ 40 * 1964693 * 2
def baseEnd_1964693 : Nat := 1008831847523986863302047

theorem tailTrace_1964693 : CollatzResearch.WordTrace tailWord_1964693 prefixEnd_1964693 1008831847523986863302047 := by
  unfold tailWord_1964693
  simp only [CollatzResearch.WordTrace]
  refine ⟨71658240671260278695578733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47772160447506852463719155 71658240671260278695578733)
  ·
    refine ⟨26871840251722604510842025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71658240671260278695578733 26871840251722604510842025)
    ·
      refine ⟨20153880188791953383131519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26871840251722604510842025 20153880188791953383131519)
      ·
        refine ⟨30230820283187930074697279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20153880188791953383131519 30230820283187930074697279)
        ·
          refine ⟨45346230424781895112045919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30230820283187930074697279 45346230424781895112045919)
          ·
            refine ⟨68019345637172842668068879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45346230424781895112045919 68019345637172842668068879)
            ·
              refine ⟨102029018455759264002103319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68019345637172842668068879 102029018455759264002103319)
              ·
                refine ⟨153043527683638896003154979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102029018455759264002103319 153043527683638896003154979)
                ·
                  refine ⟨229565291525458344004732469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153043527683638896003154979 229565291525458344004732469)
                  ·
                    refine ⟨21521746080511719750443669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 229565291525458344004732469 21521746080511719750443669)
                    ·
                      refine ⟨1008831847523986863302047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21521746080511719750443669 1008831847523986863302047)
                      ·
                        rfl

theorem cell23_1964693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_1964693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964693 prefixEnd_1964693 := by exact prefixLift 1964693
  have htrace : WordTrace (prefixWord ++ tailWord_1964693) baseStart_1964693 baseEnd_1964693 := by
    simpa [prefixWord, tailWord_1964693, baseEnd_1964693] using wordTrace_append hprefix tailTrace_1964693
  have hstable : (prefixWord ++ tailWord_1964693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964693).length < 2 ^ (prefixWord ++ tailWord_1964693).sum := by decide
  have hdescent : baseEnd_1964693 < baseStart_1964693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964730 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 1, 5, 3]
def baseStart_1964730 : Nat := 118140960795 + 1964730 * 2 ^ 59
def prefixEnd_1964730 : Nat := 4983230072969 + 3 ^ 40 * 1964730 * 2
def baseEnd_1964730 : Nat := 1008850846308203218539377

theorem tailTrace_1964730 : CollatzResearch.WordTrace tailWord_1964730 prefixEnd_1964730 1008850846308203218539377 := by
  unfold tailWord_1964730
  simp only [CollatzResearch.WordTrace]
  refine ⟨17914897543031558503668911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47773060114750822676450429 17914897543031558503668911)
  ·
    refine ⟨26872346314547337755503367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17914897543031558503668911 26872346314547337755503367)
    ·
      refine ⟨40308519471821006633255051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26872346314547337755503367 40308519471821006633255051)
      ·
        refine ⟨60462779207731509949882577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40308519471821006633255051 60462779207731509949882577)
        ·
          refine ⟨45347084405798632462411933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60462779207731509949882577 45347084405798632462411933)
          ·
            refine ⟨17005156652174487173404475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45347084405798632462411933 17005156652174487173404475)
            ·
              refine ⟨25507734978261730760106713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17005156652174487173404475 25507734978261730760106713)
              ·
                refine ⟨19130801233696298070080035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25507734978261730760106713 19130801233696298070080035)
                ·
                  refine ⟨28696201850544447105120053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19130801233696298070080035 28696201850544447105120053)
                  ·
                    refine ⟨2690268923488541916105005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28696201850544447105120053 2690268923488541916105005)
                    ·
                      refine ⟨1008850846308203218539377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2690268923488541916105005 1008850846308203218539377)
                      ·
                        rfl

theorem cell23_1964730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 1, 5, 3].length) (baseStart_1964730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964730 prefixEnd_1964730 := by exact prefixLift 1964730
  have htrace : WordTrace (prefixWord ++ tailWord_1964730) baseStart_1964730 baseEnd_1964730 := by
    simpa [prefixWord, tailWord_1964730, baseEnd_1964730] using wordTrace_append hprefix tailTrace_1964730
  have hstable : (prefixWord ++ tailWord_1964730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964730).length < 2 ^ (prefixWord ++ tailWord_1964730).sum := by decide
  have hdescent : baseEnd_1964730 < baseStart_1964730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964742 : List Nat := [6, 1, 2, 1, 3, 1, 1, 2, 2, 1, 3]
def baseStart_1964742 : Nat := 118140960795 + 1964742 * 2 ^ 59
def prefixEnd_1964742 : Nat := 4983230072969 + 3 ^ 40 * 1964742 * 2
def baseEnd_1964742 : Nat := 1008857008076057171589323

theorem tailTrace_1964742 : CollatzResearch.WordTrace tailWord_1964742 prefixEnd_1964742 1008857008076057171589323 := by
  unfold tailWord_1964742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2239375870252586252003515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47773351898721840042741653 2239375870252586252003515)
  ·
    refine ⟨3359063805378879378005273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2239375870252586252003515 3359063805378879378005273)
    ·
      refine ⟨2519297854034159533503955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3359063805378879378005273 2519297854034159533503955)
      ·
        refine ⟨3778946781051239300255933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2519297854034159533503955 3778946781051239300255933)
        ·
          refine ⟨1417105042894214737595975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3778946781051239300255933 1417105042894214737595975)
          ·
            refine ⟨2125657564341322106393963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1417105042894214737595975 2125657564341322106393963)
            ·
              refine ⟨3188486346511983159590945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2125657564341322106393963 3188486346511983159590945)
              ·
                refine ⟨2391364759883987369693209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3188486346511983159590945 2391364759883987369693209)
                ·
                  refine ⟨1793523569912990527269907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2391364759883987369693209 1793523569912990527269907)
                  ·
                    refine ⟨2690285354869485790904861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1793523569912990527269907 2690285354869485790904861)
                    ·
                      refine ⟨1008857008076057171589323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2690285354869485790904861 1008857008076057171589323)
                      ·
                        rfl

theorem cell23_1964742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_1964742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964742 prefixEnd_1964742 := by exact prefixLift 1964742
  have htrace : WordTrace (prefixWord ++ tailWord_1964742) baseStart_1964742 baseEnd_1964742 := by
    simpa [prefixWord, tailWord_1964742, baseEnd_1964742] using wordTrace_append hprefix tailTrace_1964742
  have hstable : (prefixWord ++ tailWord_1964742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964742).length < 2 ^ (prefixWord ++ tailWord_1964742).sum := by decide
  have hdescent : baseEnd_1964742 < baseStart_1964742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964748 : List Nat := [2, 2, 1, 5, 1, 3, 1, 2, 2, 2, 2]
def baseStart_1964748 : Nat := 118140960795 + 1964748 * 2 ^ 59
def prefixEnd_1964748 : Nat := 4983230072969 + 3 ^ 40 * 1964748 * 2
def baseEnd_1964748 : Nat := 1008860088959984148114295

theorem tailTrace_1964748 : CollatzResearch.WordTrace tailWord_1964748 prefixEnd_1964748 1008860088959984148114295 := by
  unfold tailWord_1964748
  simp only [CollatzResearch.WordTrace]
  refine ⟨35830123343030511544415449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47773497790707348725887265 35830123343030511544415449)
  ·
    refine ⟨26872592507272883658311587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35830123343030511544415449 26872592507272883658311587)
    ·
      refine ⟨40308888760909325487467381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26872592507272883658311587 40308888760909325487467381)
      ·
        refine ⟨3778958321335249264450067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40308888760909325487467381 3778958321335249264450067)
        ·
          refine ⟨5668437482002873896675101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3778958321335249264450067 5668437482002873896675101)
          ·
            refine ⟨2125664055751077711253163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5668437482002873896675101 2125664055751077711253163)
            ·
              refine ⟨3188496083626616566879745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2125664055751077711253163 3188496083626616566879745)
              ·
                refine ⟨2391372062719962425159809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3188496083626616566879745 2391372062719962425159809)
                ·
                  refine ⟨1793529047039971818869857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2391372062719962425159809 1793529047039971818869857)
                  ·
                    refine ⟨1345146785279978864152393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1793529047039971818869857 1345146785279978864152393)
                    ·
                      refine ⟨1008860088959984148114295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1345146785279978864152393 1008860088959984148114295)
                      ·
                        rfl

theorem cell23_1964748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_1964748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964748 prefixEnd_1964748 := by exact prefixLift 1964748
  have htrace : WordTrace (prefixWord ++ tailWord_1964748) baseStart_1964748 baseEnd_1964748 := by
    simpa [prefixWord, tailWord_1964748, baseEnd_1964748] using wordTrace_append hprefix tailTrace_1964748
  have hstable : (prefixWord ++ tailWord_1964748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964748).length < 2 ^ (prefixWord ++ tailWord_1964748).sum := by decide
  have hdescent : baseEnd_1964748 < baseStart_1964748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964764 : List Nat := [2, 2, 5, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_1964764 : Nat := 118140960795 + 1964764 * 2 ^ 59
def prefixEnd_1964764 : Nat := 4983230072969 + 3 ^ 40 * 1964764 * 2
def baseEnd_1964764 : Nat := 1008868304650456085514221

theorem tailTrace_1964764 : CollatzResearch.WordTrace tailWord_1964764 prefixEnd_1964764 1008868304650456085514221 := by
  unfold tailWord_1964764
  simp only [CollatzResearch.WordTrace]
  refine ⟨35830415127001528910706673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47773886836002038547608897 35830415127001528910706673)
  ·
    refine ⟨26872811345251146683030005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35830415127001528910706673 26872811345251146683030005)
    ·
      refine ⟨2519326063617295001534063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26872811345251146683030005 2519326063617295001534063)
      ·
        refine ⟨3778989095425942502301095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2519326063617295001534063 3778989095425942502301095)
        ·
          refine ⟨5668483643138913753451643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3778989095425942502301095 5668483643138913753451643)
          ·
            refine ⟨8502725464708370630177465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5668483643138913753451643 8502725464708370630177465)
            ·
              refine ⟨6377044098531277972633099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8502725464708370630177465 6377044098531277972633099)
              ·
                refine ⟨9565566147796916958949649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6377044098531277972633099 9565566147796916958949649)
                ·
                  refine ⟨7174174610847687719212237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9565566147796916958949649 7174174610847687719212237)
                  ·
                    refine ⟨2690315479067882894704589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7174174610847687719212237 2690315479067882894704589)
                    ·
                      refine ⟨1008868304650456085514221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2690315479067882894704589 1008868304650456085514221)
                      ·
                        rfl

theorem cell23_1964764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_1964764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964764 prefixEnd_1964764 := by exact prefixLift 1964764
  have htrace : WordTrace (prefixWord ++ tailWord_1964764) baseStart_1964764 baseEnd_1964764 := by
    simpa [prefixWord, tailWord_1964764, baseEnd_1964764] using wordTrace_append hprefix tailTrace_1964764
  have hstable : (prefixWord ++ tailWord_1964764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964764).length < 2 ^ (prefixWord ++ tailWord_1964764).sum := by decide
  have hdescent : baseEnd_1964764 < baseStart_1964764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964810 : List Nat := [3, 1, 2, 2, 1, 2, 1, 3, 8]
def baseStart_1964810 : Nat := 118140960795 + 1964810 * 2 ^ 59
def prefixEnd_1964810 : Nat := 4983230072969 + 3 ^ 40 * 1964810 * 2
def baseEnd_1964810 : Nat := 112099102751173656171001

theorem tailTrace_1964810 : CollatzResearch.WordTrace tailWord_1964810 prefixEnd_1964810 112099102751173656171001 := by
  unfold tailWord_1964810
  simp only [CollatzResearch.WordTrace]
  refine ⟨17915627002959101919396971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47775005341224271785058589 17915627002959101919396971)
  ·
    refine ⟨26873440504438652879095457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17915627002959101919396971 26873440504438652879095457)
    ·
      refine ⟨20155080378328989659321593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26873440504438652879095457 20155080378328989659321593)
      ·
        refine ⟨15116310283746742244491195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20155080378328989659321593 15116310283746742244491195)
        ·
          refine ⟨22674465425620113366736793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15116310283746742244491195 22674465425620113366736793)
          ·
            refine ⟨17005849069215085025052595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22674465425620113366736793 17005849069215085025052595)
            ·
              refine ⟨25508773603822627537578893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17005849069215085025052595 25508773603822627537578893)
              ·
                refine ⟨9565790101433485326592085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25508773603822627537578893 9565790101433485326592085)
                ·
                  refine ⟨112099102751173656171001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9565790101433485326592085 112099102751173656171001)
                  ·
                    rfl

theorem cell23_1964810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 8].length) (baseStart_1964810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964810 prefixEnd_1964810 := by exact prefixLift 1964810
  have htrace : WordTrace (prefixWord ++ tailWord_1964810) baseStart_1964810 baseEnd_1964810 := by
    simpa [prefixWord, tailWord_1964810, baseEnd_1964810] using wordTrace_append hprefix tailTrace_1964810
  have hstable : (prefixWord ++ tailWord_1964810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964810).length < 2 ^ (prefixWord ++ tailWord_1964810).sum := by decide
  have hdescent : baseEnd_1964810 < baseStart_1964810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964887 : List Nat := [1, 1, 3, 2, 4, 1, 1, 3, 1, 6]
def baseStart_1964887 : Nat := 118140960795 + 1964887 * 2 ^ 59
def prefixEnd_1964887 : Nat := 4983230072969 + 3 ^ 40 * 1964887 * 2
def baseEnd_1964887 : Nat := 336310487590319701425385

theorem tailTrace_1964887 : CollatzResearch.WordTrace tailWord_1964887 prefixEnd_1964887 336310487590319701425385 := by
  unfold tailWord_1964887
  simp only [CollatzResearch.WordTrace]
  refine ⟨71665316432557449828140915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47776877621704966552093943 71665316432557449828140915)
  ·
    refine ⟨107497974648836174742211373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71665316432557449828140915 107497974648836174742211373)
    ·
      refine ⟨40311740493313565528329265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107497974648836174742211373 40311740493313565528329265)
      ·
        refine ⟨30233805369985174146246949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40311740493313565528329265 30233805369985174146246949)
        ·
          refine ⟨5668838506872220152421303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30233805369985174146246949 5668838506872220152421303)
          ·
            refine ⟨8503257760308330228631955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5668838506872220152421303 8503257760308330228631955)
            ·
              refine ⟨12754886640462495342947933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8503257760308330228631955 12754886640462495342947933)
              ·
                refine ⟨4783082490173435753605475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12754886640462495342947933 4783082490173435753605475)
                ·
                  refine ⟨7174623735260153630408213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4783082490173435753605475 7174623735260153630408213)
                  ·
                    refine ⟨336310487590319701425385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7174623735260153630408213 336310487590319701425385)
                    ·
                      rfl

theorem cell23_1964887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 6].length) (baseStart_1964887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964887 prefixEnd_1964887 := by exact prefixLift 1964887
  have htrace : WordTrace (prefixWord ++ tailWord_1964887) baseStart_1964887 baseEnd_1964887 := by
    simpa [prefixWord, tailWord_1964887, baseEnd_1964887] using wordTrace_append hprefix tailTrace_1964887
  have hstable : (prefixWord ++ tailWord_1964887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964887).length < 2 ^ (prefixWord ++ tailWord_1964887).sum := by decide
  have hdescent : baseEnd_1964887 < baseStart_1964887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964907 : List Nat := [1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 4]
def baseStart_1964907 : Nat := 118140960795 + 1964907 * 2 ^ 59
def prefixEnd_1964907 : Nat := 4983230072969 + 3 ^ 40 * 1964907 * 2
def baseEnd_1964907 : Nat := 1008941732384049026026063

theorem tailTrace_1964907 : CollatzResearch.WordTrace tailWord_1964907 prefixEnd_1964907 1008941732384049026026063 := by
  unfold tailWord_1964907
  simp only [CollatzResearch.WordTrace]
  refine ⟨71666045892484993243868975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47777363928323328829245983 71666045892484993243868975)
  ·
    refine ⟨107499068838727489865803463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71666045892484993243868975 107499068838727489865803463)
    ·
      refine ⟨161248603258091234798705195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107499068838727489865803463 161248603258091234798705195)
      ·
        refine ⟨241872904887136852198057793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161248603258091234798705195 241872904887136852198057793)
        ·
          refine ⟨181404678665352639148543345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241872904887136852198057793 181404678665352639148543345)
          ·
            refine ⟨136053508999014479361407509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181404678665352639148543345 136053508999014479361407509)
            ·
              refine ⟨6377508234328803720065977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 136053508999014479361407509 6377508234328803720065977)
              ·
                refine ⟨4783131175746602790049483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6377508234328803720065977 4783131175746602790049483)
                ·
                  refine ⟨7174696763619904185074225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4783131175746602790049483 7174696763619904185074225)
                  ·
                    refine ⟨5381022572714928138805669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7174696763619904185074225 5381022572714928138805669)
                    ·
                      refine ⟨1008941732384049026026063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5381022572714928138805669 1008941732384049026026063)
                      ·
                        rfl

theorem cell23_1964907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 4].length) (baseStart_1964907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964907 prefixEnd_1964907 := by exact prefixLift 1964907
  have htrace : WordTrace (prefixWord ++ tailWord_1964907) baseStart_1964907 baseEnd_1964907 := by
    simpa [prefixWord, tailWord_1964907, baseEnd_1964907] using wordTrace_append hprefix tailTrace_1964907
  have hstable : (prefixWord ++ tailWord_1964907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964907).length < 2 ^ (prefixWord ++ tailWord_1964907).sum := by decide
  have hdescent : baseEnd_1964907 < baseStart_1964907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964917 : List Nat := [1, 3, 4, 1, 1, 3, 10]
def baseStart_1964917 : Nat := 118140960795 + 1964917 * 2 ^ 59
def prefixEnd_1964917 : Nat := 4983230072969 + 3 ^ 40 * 1964917 * 2
def baseEnd_1964917 : Nat := 12456134162846839344457

theorem tailTrace_1964917 : CollatzResearch.WordTrace tailWord_1964917 prefixEnd_1964917 12456134162846839344457 := by
  unfold tailWord_1964917
  simp only [CollatzResearch.WordTrace]
  refine ⟨71666410622448764951733005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47777607081632509967822003 71666410622448764951733005)
  ·
    refine ⟨26874903983418286856899877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71666410622448764951733005 26874903983418286856899877)
    ·
      refine ⟨5039044496890928785668727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26874903983418286856899877 5039044496890928785668727)
      ·
        refine ⟨7558566745336393178503091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5039044496890928785668727 7558566745336393178503091)
        ·
          refine ⟨11337850118004589767754637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7558566745336393178503091 11337850118004589767754637)
          ·
            refine ⟨4251693794251721162907989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11337850118004589767754637 4251693794251721162907989)
            ·
              refine ⟨12456134162846839344457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4251693794251721162907989 12456134162846839344457)
              ·
                rfl

theorem cell23_1964917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 10].length) (baseStart_1964917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964917 prefixEnd_1964917 := by exact prefixLift 1964917
  have htrace : WordTrace (prefixWord ++ tailWord_1964917) baseStart_1964917 baseEnd_1964917 := by
    simpa [prefixWord, tailWord_1964917, baseEnd_1964917] using wordTrace_append hprefix tailTrace_1964917
  have hstable : (prefixWord ++ tailWord_1964917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964917).length < 2 ^ (prefixWord ++ tailWord_1964917).sum := by decide
  have hdescent : baseEnd_1964917 < baseStart_1964917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964921 : List Nat := [1, 2, 1, 3, 2, 5, 1, 2, 2, 4]
def baseStart_1964921 : Nat := 118140960795 + 1964921 * 2 ^ 59
def prefixEnd_1964921 : Nat := 4983230072969 + 3 ^ 40 * 1964921 * 2
def baseEnd_1964921 : Nat := 336316307037737323750333

theorem tailTrace_1964921 : CollatzResearch.WordTrace tailWord_1964921 prefixEnd_1964921 336316307037737323750333 := by
  unfold tailWord_1964921
  simp only [CollatzResearch.WordTrace]
  refine ⟨71666556514434273634878617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47777704342956182423252411 71666556514434273634878617)
  ·
    refine ⟨53749917385825705226158963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71666556514434273634878617 53749917385825705226158963)
    ·
      refine ⟨80624876078738557839238445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53749917385825705226158963 80624876078738557839238445)
      ·
        refine ⟨30234328529526959189714417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80624876078738557839238445 30234328529526959189714417)
        ·
          refine ⟨22675746397145219392285813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30234328529526959189714417 22675746397145219392285813)
          ·
            refine ⟨2125851224732364318026795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22675746397145219392285813 2125851224732364318026795)
            ·
              refine ⟨3188776837098546477040193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2125851224732364318026795 3188776837098546477040193)
              ·
                refine ⟨2391582627823909857780145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3188776837098546477040193 2391582627823909857780145)
                ·
                  refine ⟨1793686970867932393335109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2391582627823909857780145 1793686970867932393335109)
                  ·
                    refine ⟨336316307037737323750333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1793686970867932393335109 336316307037737323750333)
                    ·
                      rfl

theorem cell23_1964921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 2, 4].length) (baseStart_1964921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964921 prefixEnd_1964921 := by exact prefixLift 1964921
  have htrace : WordTrace (prefixWord ++ tailWord_1964921) baseStart_1964921 baseEnd_1964921 := by
    simpa [prefixWord, tailWord_1964921, baseEnd_1964921] using wordTrace_append hprefix tailTrace_1964921
  have hstable : (prefixWord ++ tailWord_1964921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964921).length < 2 ^ (prefixWord ++ tailWord_1964921).sum := by decide
  have hdescent : baseEnd_1964921 < baseStart_1964921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964927 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 3, 3, 3]
def baseStart_1964927 : Nat := 118140960795 + 1964927 * 2 ^ 59
def prefixEnd_1964927 : Nat := 4983230072969 + 3 ^ 40 * 1964927 * 2
def baseEnd_1964927 : Nat := 1008952001997138947775971

theorem tailTrace_1964927 : CollatzResearch.WordTrace tailWord_1964927 prefixEnd_1964927 1008952001997138947775971 := by
  unfold tailWord_1964927
  simp only [CollatzResearch.WordTrace]
  refine ⟨71666775352412536659597035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47777850234941691106398023 71666775352412536659597035)
  ·
    refine ⟨107500163028618804989395553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71666775352412536659597035 107500163028618804989395553)
    ·
      refine ⟨80625122271464103742046665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107500163028618804989395553 80625122271464103742046665)
      ·
        refine ⟨60468841703598077806534999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80625122271464103742046665 60468841703598077806534999)
        ·
          refine ⟨90703262555397116709802499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60468841703598077806534999 90703262555397116709802499)
          ·
            refine ⟨136054893833095675064703749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90703262555397116709802499 136054893833095675064703749)
            ·
              refine ⟨25510292593705439074631953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136054893833095675064703749 25510292593705439074631953)
              ·
                refine ⟨19132719445279079305973965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25510292593705439074631953 19132719445279079305973965)
                ·
                  refine ⟨7174769791979654739740237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19132719445279079305973965 7174769791979654739740237)
                  ·
                    refine ⟨2690538671992370527402589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7174769791979654739740237 2690538671992370527402589)
                    ·
                      refine ⟨1008952001997138947775971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2690538671992370527402589 1008952001997138947775971)
                      ·
                        rfl

theorem cell23_1964927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3, 3].length) (baseStart_1964927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964927 prefixEnd_1964927 := by exact prefixLift 1964927
  have htrace : WordTrace (prefixWord ++ tailWord_1964927) baseStart_1964927 baseEnd_1964927 := by
    simpa [prefixWord, tailWord_1964927, baseEnd_1964927] using wordTrace_append hprefix tailTrace_1964927
  have hstable : (prefixWord ++ tailWord_1964927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964927).length < 2 ^ (prefixWord ++ tailWord_1964927).sum := by decide
  have hdescent : baseEnd_1964927 < baseStart_1964927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964938 : List Nat := [3, 1, 2, 4, 1, 2, 3, 1, 2, 4]
def baseStart_1964938 : Nat := 118140960795 + 1964938 * 2 ^ 59
def prefixEnd_1964938 : Nat := 4983230072969 + 3 ^ 40 * 1964938 * 2
def baseEnd_1964938 : Nat := 336319216761446134912807

theorem tailTrace_1964938 : CollatzResearch.WordTrace tailWord_1964938 prefixEnd_1964938 336319216761446134912807 := by
  unfold tailWord_1964938
  simp only [CollatzResearch.WordTrace]
  refine ⟨17916794138843171384561867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47778117703581790358831645 17916794138843171384561867)
  ·
    refine ⟨26875191208264757076842801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17916794138843171384561867 26875191208264757076842801)
    ·
      refine ⟨20156393406198567807632101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26875191208264757076842801 20156393406198567807632101)
      ·
        refine ⟨3779323763662231463931019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20156393406198567807632101 3779323763662231463931019)
        ·
          refine ⟨5668985645493347195896529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3779323763662231463931019 5668985645493347195896529)
          ·
            refine ⟨4251739234120010396922397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5668985645493347195896529 4251739234120010396922397)
            ·
              refine ⟨1594402212795003898845899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4251739234120010396922397 1594402212795003898845899)
              ·
                refine ⟨2391603319192505848268849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1594402212795003898845899 2391603319192505848268849)
                ·
                  refine ⟨1793702489394379386201637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2391603319192505848268849 1793702489394379386201637)
                  ·
                    refine ⟨336319216761446134912807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1793702489394379386201637 336319216761446134912807)
                    ·
                      rfl

theorem cell23_1964938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_1964938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964938 prefixEnd_1964938 := by exact prefixLift 1964938
  have htrace : WordTrace (prefixWord ++ tailWord_1964938) baseStart_1964938 baseEnd_1964938 := by
    simpa [prefixWord, tailWord_1964938, baseEnd_1964938] using wordTrace_append hprefix tailTrace_1964938
  have hstable : (prefixWord ++ tailWord_1964938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964938).length < 2 ^ (prefixWord ++ tailWord_1964938).sum := by decide
  have hdescent : baseEnd_1964938 < baseStart_1964938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964957 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 1, 4, 5]
def baseStart_1964957 : Nat := 118140960795 + 1964957 * 2 ^ 59
def prefixEnd_1964957 : Nat := 4983230072969 + 3 ^ 40 * 1964957 * 2
def baseEnd_1964957 : Nat := 1008967406416773830400833

theorem tailTrace_1964957 : CollatzResearch.WordTrace tailWord_1964957 prefixEnd_1964957 1008967406416773830400833 := by
  unfold tailWord_1964957
  simp only [CollatzResearch.WordTrace]
  refine ⟨71667869542303851783189125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47778579694869234522126083 71667869542303851783189125)
  ·
    refine ⟨13437725539181972209347961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71667869542303851783189125 13437725539181972209347961)
    ·
      refine ⟨10078294154386479157010971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13437725539181972209347961 10078294154386479157010971)
      ·
        refine ⟨15117441231579718735516457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10078294154386479157010971 15117441231579718735516457)
        ·
          refine ⟨11338080923684789051637343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15117441231579718735516457 11338080923684789051637343)
          ·
            refine ⟨17007121385527183577456015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11338080923684789051637343 17007121385527183577456015)
            ·
              refine ⟨25510682078290775366184023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17007121385527183577456015 25510682078290775366184023)
              ·
                refine ⟨38266023117436163049276035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25510682078290775366184023 38266023117436163049276035)
                ·
                  refine ⟨57399034676154244573914053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38266023117436163049276035 57399034676154244573914053)
                  ·
                    refine ⟨10762319001778920857608885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57399034676154244573914053 10762319001778920857608885)
                    ·
                      refine ⟨1008967406416773830400833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10762319001778920857608885 1008967406416773830400833)
                      ·
                        rfl

theorem cell23_1964957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_1964957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964957 prefixEnd_1964957 := by exact prefixLift 1964957
  have htrace : WordTrace (prefixWord ++ tailWord_1964957) baseStart_1964957 baseEnd_1964957 := by
    simpa [prefixWord, tailWord_1964957, baseEnd_1964957] using wordTrace_append hprefix tailTrace_1964957
  have hstable : (prefixWord ++ tailWord_1964957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964957).length < 2 ^ (prefixWord ++ tailWord_1964957).sum := by decide
  have hdescent : baseEnd_1964957 < baseStart_1964957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964961 : List Nat := [1, 2, 3, 4, 1, 1, 1, 2, 4, 1, 3]
def baseStart_1964961 : Nat := 118140960795 + 1964961 * 2 ^ 59
def prefixEnd_1964961 : Nat := 4983230072969 + 3 ^ 40 * 1964961 * 2
def baseEnd_1964961 : Nat := 1008969460339391814750815

theorem tailTrace_1964961 : CollatzResearch.WordTrace tailWord_1964961 prefixEnd_1964961 1008969460339391814750815 := by
  unfold tailWord_1964961
  simp only [CollatzResearch.WordTrace]
  refine ⟨71668015434289360466334737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47778676956192906977556491 71668015434289360466334737)
  ·
    refine ⟨53751011575717020349751053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71668015434289360466334737 53751011575717020349751053)
    ·
      refine ⟨20156629340893882631156645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53751011575717020349751053 20156629340893882631156645)
      ·
        refine ⟨3779368001417602993341871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20156629340893882631156645 3779368001417602993341871)
        ·
          refine ⟨5669052002126404490012807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3779368001417602993341871 5669052002126404490012807)
          ·
            refine ⟨8503578003189606735019211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5669052002126404490012807 8503578003189606735019211)
            ·
              refine ⟨12755367004784410102528817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8503578003189606735019211 12755367004784410102528817)
              ·
                refine ⟨9566525253588307576896613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12755367004784410102528817 9566525253588307576896613)
                ·
                  refine ⟨1793723485047807670668115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9566525253588307576896613 1793723485047807670668115)
                  ·
                    refine ⟨2690585227571711506002173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1793723485047807670668115 2690585227571711506002173)
                    ·
                      refine ⟨1008969460339391814750815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2690585227571711506002173 1008969460339391814750815)
                      ·
                        rfl

theorem cell23_1964961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_1964961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964961 prefixEnd_1964961 := by exact prefixLift 1964961
  have htrace : WordTrace (prefixWord ++ tailWord_1964961) baseStart_1964961 baseEnd_1964961 := by
    simpa [prefixWord, tailWord_1964961, baseEnd_1964961] using wordTrace_append hprefix tailTrace_1964961
  have hstable : (prefixWord ++ tailWord_1964961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964961).length < 2 ^ (prefixWord ++ tailWord_1964961).sum := by decide
  have hdescent : baseEnd_1964961 < baseStart_1964961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964962 : List Nat := [3, 3, 1, 2, 2, 3, 1, 3, 1, 2, 2]
def baseStart_1964962 : Nat := 118140960795 + 1964962 * 2 ^ 59
def prefixEnd_1964962 : Nat := 4983230072969 + 3 ^ 40 * 1964962 * 2
def baseEnd_1964962 : Nat := 1008969973820046310838311

theorem tailTrace_1964962 : CollatzResearch.WordTrace tailWord_1964962 prefixEnd_1964962 1008969973820046310838311 := by
  unfold tailWord_1964962
  simp only [CollatzResearch.WordTrace]
  refine ⟨17917012976821434409280285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47778701271523825091414093 17917012976821434409280285)
  ·
    refine ⟨6718879866308037903480107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17917012976821434409280285 6718879866308037903480107)
    ·
      refine ⟨10078319799462056855220161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6718879866308037903480107 10078319799462056855220161)
      ·
        refine ⟨7558739849596542641415121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10078319799462056855220161 7558739849596542641415121)
        ·
          refine ⟨5669054887197406981061341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7558739849596542641415121 5669054887197406981061341)
          ·
            refine ⟨2125895582699027617898003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5669054887197406981061341 2125895582699027617898003)
            ·
              refine ⟨3188843374048541426847005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2125895582699027617898003 3188843374048541426847005)
              ·
                refine ⟨1195816265268203035067627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3188843374048541426847005 1195816265268203035067627)
                ·
                  refine ⟨1793724397902304552601441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1195816265268203035067627 1793724397902304552601441)
                  ·
                    refine ⟨1345293298426728414451081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1793724397902304552601441 1345293298426728414451081)
                    ·
                      refine ⟨1008969973820046310838311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1345293298426728414451081 1008969973820046310838311)
                      ·
                        rfl

theorem cell23_1964962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_1964962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964962 prefixEnd_1964962 := by exact prefixLift 1964962
  have htrace : WordTrace (prefixWord ++ tailWord_1964962) baseStart_1964962 baseEnd_1964962 := by
    simpa [prefixWord, tailWord_1964962, baseEnd_1964962] using wordTrace_append hprefix tailTrace_1964962
  have hstable : (prefixWord ++ tailWord_1964962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964962).length < 2 ^ (prefixWord ++ tailWord_1964962).sum := by decide
  have hdescent : baseEnd_1964962 < baseStart_1964962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964997 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 6, 2, 4]
def baseStart_1964997 : Nat := 118140960795 + 1964997 * 2 ^ 59
def prefixEnd_1964997 : Nat := 4983230072969 + 3 ^ 40 * 1964997 * 2
def baseEnd_1964997 : Nat := 1008987945642953673900649

theorem tailTrace_1964997 : CollatzResearch.WordTrace tailWord_1964997 prefixEnd_1964997 1008987945642953673900649 := by
  unfold tailWord_1964997
  simp only [CollatzResearch.WordTrace]
  refine ⟨71669328462158938614645245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47779552308105959076430163 71669328462158938614645245)
  ·
    refine ⟨26875998173309601980491967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71669328462158938614645245 26875998173309601980491967)
    ·
      refine ⟨40313997259964402970737951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26875998173309601980491967 40313997259964402970737951)
      ·
        refine ⟨60470995889946604456106927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40313997259964402970737951 60470995889946604456106927)
        ·
          refine ⟨90706493834919906684160391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60470995889946604456106927 90706493834919906684160391)
          ·
            refine ⟨136059740752379860026240587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90706493834919906684160391 136059740752379860026240587)
            ·
              refine ⟨204089611128569790039360881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136059740752379860026240587 204089611128569790039360881)
              ·
                refine ⟨153067208346427342529520661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204089611128569790039360881 153067208346427342529520661)
                ·
                  refine ⟨7175025391238781681071281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 153067208346427342529520661 7175025391238781681071281)
                  ·
                    refine ⟨5381269043429086260803461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7175025391238781681071281 5381269043429086260803461)
                    ·
                      refine ⟨1008987945642953673900649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5381269043429086260803461 1008987945642953673900649)
                      ·
                        rfl

theorem cell23_1964997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_1964997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1964997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1964997 prefixEnd_1964997 := by exact prefixLift 1964997
  have htrace : WordTrace (prefixWord ++ tailWord_1964997) baseStart_1964997 baseEnd_1964997 := by
    simpa [prefixWord, tailWord_1964997, baseEnd_1964997] using wordTrace_append hprefix tailTrace_1964997
  have hstable : (prefixWord ++ tailWord_1964997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964997).length < 2 ^ (prefixWord ++ tailWord_1964997).sum := by decide
  have hdescent : baseEnd_1964997 < baseStart_1964997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965041 : List Nat := [1, 2, 2, 2, 4, 2, 1, 4, 5]
def baseStart_1965041 : Nat := 118140960795 + 1965041 * 2 ^ 59
def prefixEnd_1965041 : Nat := 4983230072969 + 3 ^ 40 * 1965041 * 2
def baseEnd_1965041 : Nat := 112112282087972389083383

theorem tailTrace_1965041 : CollatzResearch.WordTrace tailWord_1965041 prefixEnd_1965041 112112282087972389083383 := by
  unfold tailWord_1965041
  simp only [CollatzResearch.WordTrace]
  refine ⟨71670933273999534129246977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47780622182666356086164651 71670933273999534129246977)
  ·
    refine ⟨53753199955499650596935233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71670933273999534129246977 53753199955499650596935233)
    ·
      refine ⟨40314899966624737947701425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53753199955499650596935233 40314899966624737947701425)
      ·
        refine ⟨30236174974968553460776069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40314899966624737947701425 30236174974968553460776069)
        ·
          refine ⟨5669282807806603773895513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30236174974968553460776069 5669282807806603773895513)
          ·
            refine ⟨4251962105854952830421635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5669282807806603773895513 4251962105854952830421635)
            ·
              refine ⟨6377943158782429245632453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4251962105854952830421635 6377943158782429245632453)
              ·
                refine ⟨1195864342271705483556085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6377943158782429245632453 1195864342271705483556085)
                ·
                  refine ⟨112112282087972389083383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1195864342271705483556085 112112282087972389083383)
                  ·
                    rfl

theorem cell23_1965041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 4, 5].length) (baseStart_1965041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965041 prefixEnd_1965041 := by exact prefixLift 1965041
  have htrace : WordTrace (prefixWord ++ tailWord_1965041) baseStart_1965041 baseEnd_1965041 := by
    simpa [prefixWord, tailWord_1965041, baseEnd_1965041] using wordTrace_append hprefix tailTrace_1965041
  have hstable : (prefixWord ++ tailWord_1965041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965041).length < 2 ^ (prefixWord ++ tailWord_1965041).sum := by decide
  have hdescent : baseEnd_1965041 < baseStart_1965041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965058 : List Nat := [3, 4, 1, 3, 1, 1, 1, 2, 7]
def baseStart_1965058 : Nat := 118140960795 + 1965058 * 2 ^ 59
def prefixEnd_1965058 : Nat := 4983230072969 + 3 ^ 40 * 1965058 * 2
def baseEnd_1965058 : Nat := 112113251995875326137541

theorem tailTrace_1965058 : CollatzResearch.WordTrace tailWord_1965058 prefixEnd_1965058 112113251995875326137541 := by
  unfold tailWord_1965058
  simp only [CollatzResearch.WordTrace]
  refine ⟨17917888328734486508153957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47781035543291964021743885 17917888328734486508153957)
  ·
    refine ⟨3359604061637716220278867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17917888328734486508153957 3359604061637716220278867)
    ·
      refine ⟨5039406092456574330418301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3359604061637716220278867 5039406092456574330418301)
      ·
        refine ⟨1889777284671215373906863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5039406092456574330418301 1889777284671215373906863)
        ·
          refine ⟨2834665927006823060860295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1889777284671215373906863 2834665927006823060860295)
          ·
            refine ⟨4251998890510234591290443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2834665927006823060860295 4251998890510234591290443)
            ·
              refine ⟨6377998335765351886935665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4251998890510234591290443 6377998335765351886935665)
              ·
                refine ⟨4783498751824013915201749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6377998335765351886935665 4783498751824013915201749)
                ·
                  refine ⟨112113251995875326137541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4783498751824013915201749 112113251995875326137541)
                  ·
                    rfl

theorem cell23_1965058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_1965058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965058 prefixEnd_1965058 := by exact prefixLift 1965058
  have htrace : WordTrace (prefixWord ++ tailWord_1965058) baseStart_1965058 baseEnd_1965058 := by
    simpa [prefixWord, tailWord_1965058, baseEnd_1965058] using wordTrace_append hprefix tailTrace_1965058
  have hstable : (prefixWord ++ tailWord_1965058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965058).length < 2 ^ (prefixWord ++ tailWord_1965058).sum := by decide
  have hdescent : baseEnd_1965058 < baseStart_1965058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965091 : List Nat := [1, 1, 1, 4, 3, 2, 1, 2, 2, 4, 2]
def baseStart_1965091 : Nat := 118140960795 + 1965091 * 2 ^ 59
def prefixEnd_1965091 : Nat := 4983230072969 + 3 ^ 40 * 1965091 * 2
def baseEnd_1965091 : Nat := 1009036212824476306125217

theorem tailTrace_1965091 : CollatzResearch.WordTrace tailWord_1965091 prefixEnd_1965091 1009036212824476306125217 := by
  unfold tailWord_1965091
  simp only [CollatzResearch.WordTrace]
  refine ⟨71672756923818392668567127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47781837949212261779044751 71672756923818392668567127)
  ·
    refine ⟨107509135385727589002850691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71672756923818392668567127 107509135385727589002850691)
    ·
      refine ⟨161263703078591383504276037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107509135385727589002850691 161263703078591383504276037)
      ·
        refine ⟨30236944327235884407051757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161263703078591383504276037 30236944327235884407051757)
        ·
          refine ⟨11338854122713456652644409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30236944327235884407051757 11338854122713456652644409)
          ·
            refine ⟨8504140592035092489483307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11338854122713456652644409 8504140592035092489483307)
            ·
              refine ⟨12756210888052638734224961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8504140592035092489483307 12756210888052638734224961)
              ·
                refine ⟨9567158166039479050668721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12756210888052638734224961 9567158166039479050668721)
                ·
                  refine ⟨7175368624529609288001541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9567158166039479050668721 7175368624529609288001541)
                  ·
                    refine ⟨1345381617099301741500289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7175368624529609288001541 1345381617099301741500289)
                    ·
                      refine ⟨1009036212824476306125217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1345381617099301741500289 1009036212824476306125217)
                      ·
                        rfl

theorem cell23_1965091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 4, 2].length) (baseStart_1965091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965091 prefixEnd_1965091 := by exact prefixLift 1965091
  have htrace : WordTrace (prefixWord ++ tailWord_1965091) baseStart_1965091 baseEnd_1965091 := by
    simpa [prefixWord, tailWord_1965091, baseEnd_1965091] using wordTrace_append hprefix tailTrace_1965091
  have hstable : (prefixWord ++ tailWord_1965091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965091).length < 2 ^ (prefixWord ++ tailWord_1965091).sum := by decide
  have hdescent : baseEnd_1965091 < baseStart_1965091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965114 : List Nat := [3, 1, 1, 1, 3, 1, 2, 5, 6]
def baseStart_1965114 : Nat := 118140960795 + 1965114 * 2 ^ 59
def prefixEnd_1965114 : Nat := 4983230072969 + 3 ^ 40 * 1965114 * 2
def baseEnd_1965114 : Nat := 112116446986614412904179

theorem tailTrace_1965114 : CollatzResearch.WordTrace tailWord_1965114 prefixEnd_1965114 112116446986614412904179 := by
  unfold tailWord_1965114
  simp only [CollatzResearch.WordTrace]
  refine ⟨17918398950683766899163599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47782397201823378397769597 17918398950683766899163599)
  ·
    refine ⟨26877598426025650348745399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17918398950683766899163599 26877598426025650348745399)
    ·
      refine ⟨40316397639038475523118099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26877598426025650348745399 40316397639038475523118099)
      ·
        refine ⟨60474596458557713284677149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40316397639038475523118099 60474596458557713284677149)
        ·
          refine ⟨22677973671959142481753931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60474596458557713284677149 22677973671959142481753931)
          ·
            refine ⟨34016960507938713722630897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22677973671959142481753931 34016960507938713722630897)
            ·
              refine ⟨25512720380954035291973173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34016960507938713722630897 25512720380954035291973173)
              ·
                refine ⟨2391817535714440808622485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25512720380954035291973173 2391817535714440808622485)
                ·
                  refine ⟨112116446986614412904179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2391817535714440808622485 112116446986614412904179)
                  ·
                    rfl

theorem cell23_1965114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 6].length) (baseStart_1965114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965114 prefixEnd_1965114 := by exact prefixLift 1965114
  have htrace : WordTrace (prefixWord ++ tailWord_1965114) baseStart_1965114 baseEnd_1965114 := by
    simpa [prefixWord, tailWord_1965114, baseEnd_1965114] using wordTrace_append hprefix tailTrace_1965114
  have hstable : (prefixWord ++ tailWord_1965114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965114).length < 2 ^ (prefixWord ++ tailWord_1965114).sum := by decide
  have hdescent : baseEnd_1965114 < baseStart_1965114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965118 : List Nat := [4, 2, 1, 3, 1, 1, 2, 2, 3, 4]
def baseStart_1965118 : Nat := 118140960795 + 1965118 * 2 ^ 59
def prefixEnd_1965118 : Nat := 4983230072969 + 3 ^ 40 * 1965118 * 2
def baseEnd_1965118 : Nat := 336350025600715900162531

theorem tailTrace_1965118 : CollatzResearch.WordTrace tailWord_1965118 prefixEnd_1965118 336350025600715900162531 := by
  unfold tailWord_1965118
  simp only [CollatzResearch.WordTrace]
  refine ⟨8959217711840072034975001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47782494463147050853200005 8959217711840072034975001)
  ·
    refine ⟨6719413283880054026231251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8959217711840072034975001 6719413283880054026231251)
    ·
      refine ⟨10079119925820081039346877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6719413283880054026231251 10079119925820081039346877)
      ·
        refine ⟨3779669972182530389755079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10079119925820081039346877 3779669972182530389755079)
        ·
          refine ⟨5669504958273795584632619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3779669972182530389755079 5669504958273795584632619)
          ·
            refine ⟨8504257437410693376948929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5669504958273795584632619 8504257437410693376948929)
            ·
              refine ⟨6378193078058020032711697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8504257437410693376948929 6378193078058020032711697)
              ·
                refine ⟨4783644808543515024533773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6378193078058020032711697 4783644808543515024533773)
                ·
                  refine ⟨1793866803203818134200165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4783644808543515024533773 1793866803203818134200165)
                  ·
                    refine ⟨336350025600715900162531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1793866803203818134200165 336350025600715900162531)
                    ·
                      rfl

theorem cell23_1965118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_1965118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965118 prefixEnd_1965118 := by exact prefixLift 1965118
  have htrace : WordTrace (prefixWord ++ tailWord_1965118) baseStart_1965118 baseEnd_1965118 := by
    simpa [prefixWord, tailWord_1965118, baseEnd_1965118] using wordTrace_append hprefix tailTrace_1965118
  have hstable : (prefixWord ++ tailWord_1965118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965118).length < 2 ^ (prefixWord ++ tailWord_1965118).sum := by decide
  have hdescent : baseEnd_1965118 < baseStart_1965118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965181 : List Nat := [1, 4, 1, 1, 3, 1, 3, 1, 3, 1, 4]
def baseStart_1965181 : Nat := 118140960795 + 1965181 * 2 ^ 59
def prefixEnd_1965181 : Nat := 4983230072969 + 3 ^ 40 * 1965181 * 2
def baseEnd_1965181 : Nat := 1009082426083380953999803

theorem tailTrace_1965181 : CollatzResearch.WordTrace tailWord_1965181 prefixEnd_1965181 1009082426083380953999803 := by
  unfold tailWord_1965181
  simp only [CollatzResearch.WordTrace]
  refine ⟨71676039493492338039343397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47784026328994892026228931 71676039493492338039343397)
  ·
    refine ⟨13439257405029813382376887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71676039493492338039343397 13439257405029813382376887)
    ·
      refine ⟨20158886107544720073565331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13439257405029813382376887 20158886107544720073565331)
      ·
        refine ⟨30238329161317080110347997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20158886107544720073565331 30238329161317080110347997)
        ·
          refine ⟨11339373435493905041380499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30238329161317080110347997 11339373435493905041380499)
          ·
            refine ⟨17009060153240857562070749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11339373435493905041380499 17009060153240857562070749)
            ·
              refine ⟨6378397557465321585776531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17009060153240857562070749 6378397557465321585776531)
              ·
                refine ⟨9567596336197982378664797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6378397557465321585776531 9567596336197982378664797)
                ·
                  refine ⟨3587848626074243391999299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9567596336197982378664797 3587848626074243391999299)
                  ·
                    refine ⟨5381772939111365087998949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3587848626074243391999299 5381772939111365087998949)
                    ·
                      refine ⟨1009082426083380953999803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5381772939111365087998949 1009082426083380953999803)
                      ·
                        rfl

theorem cell23_1965181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_1965181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965181 prefixEnd_1965181 := by exact prefixLift 1965181
  have htrace : WordTrace (prefixWord ++ tailWord_1965181) baseStart_1965181 baseEnd_1965181 := by
    simpa [prefixWord, tailWord_1965181, baseEnd_1965181] using wordTrace_append hprefix tailTrace_1965181
  have hstable : (prefixWord ++ tailWord_1965181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965181).length < 2 ^ (prefixWord ++ tailWord_1965181).sum := by decide
  have hdescent : baseEnd_1965181 < baseStart_1965181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965184 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 5]
def baseStart_1965184 : Nat := 118140960795 + 1965184 * 2 ^ 59
def prefixEnd_1965184 : Nat := 4983230072969 + 3 ^ 40 * 1965184 * 2
def baseEnd_1965184 : Nat := 1009083966525344442262289

theorem tailTrace_1965184 : CollatzResearch.WordTrace tailWord_1965184 prefixEnd_1965184 1009083966525344442262289 := by
  unfold tailWord_1965184
  simp only [CollatzResearch.WordTrace]
  refine ⟨35838074456240734775851303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47784099274987646367801737 35838074456240734775851303)
  ·
    refine ⟨53757111684361102163776955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35838074456240734775851303 53757111684361102163776955)
    ·
      refine ⟨80635667526541653245665433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53757111684361102163776955 80635667526541653245665433)
      ·
        refine ⟨60476750644906239934249075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80635667526541653245665433 60476750644906239934249075)
        ·
          refine ⟨90715125967359359901373613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60476750644906239934249075 90715125967359359901373613)
          ·
            refine ⟨34018172237759759963015105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90715125967359359901373613 34018172237759759963015105)
            ·
              refine ⟨25513629178319819972261329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34018172237759759963015105 25513629178319819972261329)
              ·
                refine ⟨19135221883739864979195997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25513629178319819972261329 19135221883739864979195997)
                ·
                  refine ⟨7175708206402449367198499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19135221883739864979195997 7175708206402449367198499)
                  ·
                    refine ⟨10763562309603674050797749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7175708206402449367198499 10763562309603674050797749)
                    ·
                      refine ⟨1009083966525344442262289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10763562309603674050797749 1009083966525344442262289)
                      ·
                        rfl

theorem cell23_1965184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_1965184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965184 prefixEnd_1965184 := by exact prefixLift 1965184
  have htrace : WordTrace (prefixWord ++ tailWord_1965184) baseStart_1965184 baseEnd_1965184 := by
    simpa [prefixWord, tailWord_1965184, baseEnd_1965184] using wordTrace_append hprefix tailTrace_1965184
  have hstable : (prefixWord ++ tailWord_1965184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965184).length < 2 ^ (prefixWord ++ tailWord_1965184).sum := by decide
  have hdescent : baseEnd_1965184 < baseStart_1965184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965185 : List Nat := [1, 2, 4, 2, 2, 2, 2, 1, 2, 3, 2]
def baseStart_1965185 : Nat := 118140960795 + 1965185 * 2 ^ 59
def prefixEnd_1965185 : Nat := 4983230072969 + 3 ^ 40 * 1965185 * 2
def baseEnd_1965185 : Nat := 1009084480005998938349785

theorem tailTrace_1965185 : CollatzResearch.WordTrace tailWord_1965185 prefixEnd_1965185 1009084480005998938349785 := by
  unfold tailWord_1965185
  simp only [CollatzResearch.WordTrace]
  refine ⟨71676185385477846722489009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47784123590318564481659339 71676185385477846722489009)
  ·
    refine ⟨53757139039108385041866757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71676185385477846722489009 53757139039108385041866757)
    ·
      refine ⟨10079463569832822195350017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53757139039108385041866757 10079463569832822195350017)
      ·
        refine ⟨7559597677374616646512513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10079463569832822195350017 7559597677374616646512513)
        ·
          refine ⟨5669698258030962484884385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7559597677374616646512513 5669698258030962484884385)
          ·
            refine ⟨4252273693523221863663289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5669698258030962484884385 4252273693523221863663289)
            ·
              refine ⟨3189205270142416397747467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4252273693523221863663289 3189205270142416397747467)
              ·
                refine ⟨4783807905213624596621201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3189205270142416397747467 4783807905213624596621201)
                ·
                  refine ⟨3587855928910218447465901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4783807905213624596621201 3587855928910218447465901)
                  ·
                    refine ⟨1345445973341331917799713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3587855928910218447465901 1345445973341331917799713)
                    ·
                      refine ⟨1009084480005998938349785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1345445973341331917799713 1009084480005998938349785)
                      ·
                        rfl

theorem cell23_1965185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_1965185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965185 prefixEnd_1965185 := by exact prefixLift 1965185
  have htrace : WordTrace (prefixWord ++ tailWord_1965185) baseStart_1965185 baseEnd_1965185 := by
    simpa [prefixWord, tailWord_1965185, baseEnd_1965185] using wordTrace_append hprefix tailTrace_1965185
  have hstable : (prefixWord ++ tailWord_1965185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965185).length < 2 ^ (prefixWord ++ tailWord_1965185).sum := by decide
  have hdescent : baseEnd_1965185 < baseStart_1965185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965204 : List Nat := [2, 4, 2, 15]
def baseStart_1965204 : Nat := 118140960795 + 1965204 * 2 ^ 59
def prefixEnd_1965204 : Nat := 4983230072969 + 3 ^ 40 * 1965204 * 2
def baseEnd_1965204 : Nat := 461405686391602361231

theorem tailTrace_1965204 : CollatzResearch.WordTrace tailWord_1965204 prefixEnd_1965204 461405686391602361231 := by
  unfold tailWord_1965204
  simp only [CollatzResearch.WordTrace]
  refine ⟨35838439186204506483715333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47784585581606008644953777 35838439186204506483715333)
  ·
    refine ⟨6719707347413344965696625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35838439186204506483715333 6719707347413344965696625)
    ·
      refine ⟨5039780510560008724272469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6719707347413344965696625 5039780510560008724272469)
      ·
        refine ⟨461405686391602361231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 5039780510560008724272469 461405686391602361231)
        ·
          rfl

theorem cell23_1965204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 15].length) (baseStart_1965204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965204 prefixEnd_1965204 := by exact prefixLift 1965204
  have htrace : WordTrace (prefixWord ++ tailWord_1965204) baseStart_1965204 baseEnd_1965204 := by
    simpa [prefixWord, tailWord_1965204, baseEnd_1965204] using wordTrace_append hprefix tailTrace_1965204
  have hstable : (prefixWord ++ tailWord_1965204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965204).length < 2 ^ (prefixWord ++ tailWord_1965204).sum := by decide
  have hdescent : baseEnd_1965204 < baseStart_1965204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965208 : List Nat := [2, 1, 2, 4, 2, 1, 1, 4, 2, 4]
def baseStart_1965208 : Nat := 118140960795 + 1965208 * 2 ^ 59
def prefixEnd_1965208 : Nat := 4983230072969 + 3 ^ 40 * 1965208 * 2
def baseEnd_1965208 : Nat := 336365430020350782787393

theorem tailTrace_1965208 : CollatzResearch.WordTrace tailWord_1965208 prefixEnd_1965208 336365430020350782787393 := by
  unfold tailWord_1965208
  simp only [CollatzResearch.WordTrace]
  refine ⟨35838512132197260825288139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47784682842929681100384185 35838512132197260825288139)
  ·
    refine ⟨53757768198295891237932209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35838512132197260825288139 53757768198295891237932209)
    ·
      refine ⟨40318326148721918428449157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53757768198295891237932209 40318326148721918428449157)
      ·
        refine ⟨7559686152885359705334217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40318326148721918428449157 7559686152885359705334217)
        ·
          refine ⟨5669764614664019779000663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7559686152885359705334217 5669764614664019779000663)
          ·
            refine ⟨8504646921996029668500995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5669764614664019779000663 8504646921996029668500995)
            ·
              refine ⟨12756970382994044502751493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8504646921996029668500995 12756970382994044502751493)
              ·
                refine ⟨2391931946811383344265905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12756970382994044502751493 2391931946811383344265905)
                ·
                  refine ⟨1793948960108537508199429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2391931946811383344265905 1793948960108537508199429)
                  ·
                    refine ⟨336365430020350782787393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1793948960108537508199429 336365430020350782787393)
                    ·
                      rfl

theorem cell23_1965208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 2, 4].length) (baseStart_1965208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965208 prefixEnd_1965208 := by exact prefixLift 1965208
  have htrace : WordTrace (prefixWord ++ tailWord_1965208) baseStart_1965208 baseEnd_1965208 := by
    simpa [prefixWord, tailWord_1965208, baseEnd_1965208] using wordTrace_append hprefix tailTrace_1965208
  have hstable : (prefixWord ++ tailWord_1965208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965208).length < 2 ^ (prefixWord ++ tailWord_1965208).sum := by decide
  have hdescent : baseEnd_1965208 < baseStart_1965208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965221 : List Nat := [1, 3, 1, 2, 1, 6, 1, 8]
def baseStart_1965221 : Nat := 118140960795 + 1965221 * 2 ^ 59
def prefixEnd_1965221 : Nat := 4983230072969 + 3 ^ 40 * 1965221 * 2
def baseEnd_1965221 : Nat := 37374183900354103611097

theorem tailTrace_1965221 : CollatzResearch.WordTrace tailWord_1965221 prefixEnd_1965221 37374183900354103611097 := by
  unfold tailWord_1965221
  simp only [CollatzResearch.WordTrace]
  refine ⟨71677498413347424870799517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47784998942231616580533011 71677498413347424870799517)
  ·
    refine ⟨26879061905005284326549819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71677498413347424870799517 26879061905005284326549819)
    ·
      refine ⟨40318592857507926489824729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26879061905005284326549819 40318592857507926489824729)
      ·
        refine ⟨30238944643130944867368547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40318592857507926489824729 30238944643130944867368547)
        ·
          refine ⟨45358416964696417301052821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30238944643130944867368547 45358416964696417301052821)
          ·
            refine ⟨2126175795220144560986851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45358416964696417301052821 2126175795220144560986851)
            ·
              refine ⟨3189263692830216841480277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2126175795220144560986851 3189263692830216841480277)
              ·
                refine ⟨37374183900354103611097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3189263692830216841480277 37374183900354103611097)
                ·
                  rfl

theorem cell23_1965221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 8].length) (baseStart_1965221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965221 prefixEnd_1965221 := by exact prefixLift 1965221
  have htrace : WordTrace (prefixWord ++ tailWord_1965221) baseStart_1965221 baseEnd_1965221 := by
    simpa [prefixWord, tailWord_1965221, baseEnd_1965221] using wordTrace_append hprefix tailTrace_1965221
  have hstable : (prefixWord ++ tailWord_1965221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965221).length < 2 ^ (prefixWord ++ tailWord_1965221).sum := by decide
  have hdescent : baseEnd_1965221 < baseStart_1965221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965231 : List Nat := [1, 1, 2, 1, 2, 3, 3, 3, 1, 3, 3]
def baseStart_1965231 : Nat := 118140960795 + 1965231 * 2 ^ 59
def prefixEnd_1965231 : Nat := 4983230072969 + 3 ^ 40 * 1965231 * 2
def baseEnd_1965231 : Nat := 1009108100116105758374573

theorem tailTrace_1965231 : CollatzResearch.WordTrace tailWord_1965231 prefixEnd_1965231 1009108100116105758374573 := by
  unfold tailWord_1965231
  simp only [CollatzResearch.WordTrace]
  refine ⟨71677863143311196578663547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47785242095540797719109031 71677863143311196578663547)
  ·
    refine ⟨107516794714966794867995321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71677863143311196578663547 107516794714966794867995321)
    ·
      refine ⟨80637596036225096150996491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107516794714966794867995321 80637596036225096150996491)
      ·
        refine ⟨120956394054337644226494737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80637596036225096150996491 120956394054337644226494737)
        ·
          refine ⟨90717295540753233169871053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120956394054337644226494737 90717295540753233169871053)
          ·
            refine ⟨34018985827782462438701645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90717295540753233169871053 34018985827782462438701645)
            ·
              refine ⟨12757119685418423414513117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34018985827782462438701645 12757119685418423414513117)
              ·
                refine ⟨4783919882031908780442419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12757119685418423414513117 4783919882031908780442419)
                ·
                  refine ⟨7175879823047863170663629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4783919882031908780442419 7175879823047863170663629)
                  ·
                    refine ⟨2690954933642948688998861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7175879823047863170663629 2690954933642948688998861)
                    ·
                      refine ⟨1009108100116105758374573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2690954933642948688998861 1009108100116105758374573)
                      ·
                        rfl

theorem cell23_1965231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 3, 3].length) (baseStart_1965231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965231 prefixEnd_1965231 := by exact prefixLift 1965231
  have htrace : WordTrace (prefixWord ++ tailWord_1965231) baseStart_1965231 baseEnd_1965231 := by
    simpa [prefixWord, tailWord_1965231, baseEnd_1965231] using wordTrace_append hprefix tailTrace_1965231
  have hstable : (prefixWord ++ tailWord_1965231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965231).length < 2 ^ (prefixWord ++ tailWord_1965231).sum := by decide
  have hdescent : baseEnd_1965231 < baseStart_1965231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965249 : List Nat := [1, 2, 6, 1, 1, 1, 1, 5, 1, 2, 2]
def baseStart_1965249 : Nat := 118140960795 + 1965249 * 2 ^ 59
def prefixEnd_1965249 : Nat := 4983230072969 + 3 ^ 40 * 1965249 * 2
def baseEnd_1965249 : Nat := 1009117342767886687949491

theorem tailTrace_1965249 : CollatzResearch.WordTrace tailWord_1965249 prefixEnd_1965249 1009117342767886687949491 := by
  unfold tailWord_1965249
  simp only [CollatzResearch.WordTrace]
  refine ⟨71678519657245985652818801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47785679771497323768545867 71678519657245985652818801)
  ·
    refine ⟨53758889742934489239614101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71678519657245985652818801 53758889742934489239614101)
    ·
      refine ⟨2519947956700054183106911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53758889742934489239614101 2519947956700054183106911)
      ·
        refine ⟨3779921935050081274660367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2519947956700054183106911 3779921935050081274660367)
        ·
          refine ⟨5669882902575121911990551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3779921935050081274660367 5669882902575121911990551)
          ·
            refine ⟨8504824353862682867985827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5669882902575121911990551 8504824353862682867985827)
            ·
              refine ⟨12757236530794024301978741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8504824353862682867985827 12757236530794024301978741)
              ·
                refine ⟨1195990924761939778310507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12757236530794024301978741 1195990924761939778310507)
                ·
                  refine ⟨1793986387142909667465761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1195990924761939778310507 1793986387142909667465761)
                  ·
                    refine ⟨1345489790357182250599321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1793986387142909667465761 1345489790357182250599321)
                    ·
                      refine ⟨1009117342767886687949491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1345489790357182250599321 1009117342767886687949491)
                      ·
                        rfl

theorem cell23_1965249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_1965249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965249 prefixEnd_1965249 := by exact prefixLift 1965249
  have htrace : WordTrace (prefixWord ++ tailWord_1965249) baseStart_1965249 baseEnd_1965249 := by
    simpa [prefixWord, tailWord_1965249, baseEnd_1965249] using wordTrace_append hprefix tailTrace_1965249
  have hstable : (prefixWord ++ tailWord_1965249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965249).length < 2 ^ (prefixWord ++ tailWord_1965249).sum := by decide
  have hdescent : baseEnd_1965249 < baseStart_1965249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965281 : List Nat := [1, 2, 3, 1, 3, 2, 2, 1, 2, 6]
def baseStart_1965281 : Nat := 118140960795 + 1965281 * 2 ^ 59
def prefixEnd_1965281 : Nat := 4983230072969 + 3 ^ 40 * 1965281 * 2
def baseEnd_1965281 : Nat := 336377924716276854249781

theorem tailTrace_1965281 : CollatzResearch.WordTrace tailWord_1965281 prefixEnd_1965281 336377924716276854249781 := by
  unfold tailWord_1965281
  simp only [CollatzResearch.WordTrace]
  refine ⟨71679686793130055117983697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47786457862086703411989131 71679686793130055117983697)
  ·
    refine ⟨53759765094847541338487773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71679686793130055117983697 53759765094847541338487773)
    ·
      refine ⟨20159911910567828001932915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53759765094847541338487773 20159911910567828001932915)
      ·
        refine ⟨30239867865851742002899373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20159911910567828001932915 30239867865851742002899373)
        ·
          refine ⟨11339950449694403251087265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30239867865851742002899373 11339950449694403251087265)
          ·
            refine ⟨8504962837270802438315449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11339950449694403251087265 8504962837270802438315449)
            ·
              refine ⟨6378722127953101828736587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8504962837270802438315449 6378722127953101828736587)
              ·
                refine ⟨9568083191929652743104881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6378722127953101828736587 9568083191929652743104881)
                ·
                  refine ⟨7176062393947239557328661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9568083191929652743104881 7176062393947239557328661)
                  ·
                    refine ⟨336377924716276854249781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7176062393947239557328661 336377924716276854249781)
                    ·
                      rfl

theorem cell23_1965281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_1965281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965281 prefixEnd_1965281 := by exact prefixLift 1965281
  have htrace : WordTrace (prefixWord ++ tailWord_1965281) baseStart_1965281 baseEnd_1965281 := by
    simpa [prefixWord, tailWord_1965281, baseEnd_1965281] using wordTrace_append hprefix tailTrace_1965281
  have hstable : (prefixWord ++ tailWord_1965281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965281).length < 2 ^ (prefixWord ++ tailWord_1965281).sum := by decide
  have hdescent : baseEnd_1965281 < baseStart_1965281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965300 : List Nat := [2, 6, 1, 2, 1, 2, 1, 3, 1, 2, 2]
def baseStart_1965300 : Nat := 118140960795 + 1965300 * 2 ^ 59
def prefixEnd_1965300 : Nat := 4983230072969 + 3 ^ 40 * 1965300 * 2
def baseEnd_1965300 : Nat := 1009143530281265988411757

theorem tailTrace_1965300 : CollatzResearch.WordTrace tailWord_1965300 prefixEnd_1965300 1009143530281265988411757 := by
  unfold tailWord_1965300
  simp only [CollatzResearch.WordTrace]
  refine ⟨35840189890030610681462677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47786919853374147575283569 35840189890030610681462677)
  ·
    refine ⟨1680008901095184875693563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35840189890030610681462677 1680008901095184875693563)
    ·
      refine ⟨2520013351642777313540345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1680008901095184875693563 2520013351642777313540345)
      ·
        refine ⟨1890010013732082985155259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2520013351642777313540345 1890010013732082985155259)
        ·
          refine ⟨2835015020598124477732889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1890010013732082985155259 2835015020598124477732889)
          ·
            refine ⟨2126261265448593358299667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2835015020598124477732889 2126261265448593358299667)
            ·
              refine ⟨3189391898172890037449501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2126261265448593358299667 3189391898172890037449501)
              ·
                refine ⟨1196021961814833764043563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3189391898172890037449501 1196021961814833764043563)
                ·
                  refine ⟨1794032942722250646065345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196021961814833764043563 1794032942722250646065345)
                  ·
                    refine ⟨1345524707041687984549009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1794032942722250646065345 1345524707041687984549009)
                    ·
                      refine ⟨1009143530281265988411757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1345524707041687984549009 1009143530281265988411757)
                      ·
                        rfl

theorem cell23_1965300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_1965300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965300 prefixEnd_1965300 := by exact prefixLift 1965300
  have htrace : WordTrace (prefixWord ++ tailWord_1965300) baseStart_1965300 baseEnd_1965300 := by
    simpa [prefixWord, tailWord_1965300, baseEnd_1965300] using wordTrace_append hprefix tailTrace_1965300
  have hstable : (prefixWord ++ tailWord_1965300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965300).length < 2 ^ (prefixWord ++ tailWord_1965300).sum := by decide
  have hdescent : baseEnd_1965300 < baseStart_1965300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965308 : List Nat := [2, 2, 2, 1, 5, 1, 1, 1, 2, 1, 5]
def baseStart_1965308 : Nat := 118140960795 + 1965308 * 2 ^ 59
def prefixEnd_1965308 : Nat := 4983230072969 + 3 ^ 40 * 1965308 * 2
def baseEnd_1965308 : Nat := 1009147638126501957111719

theorem tailTrace_1965308 : CollatzResearch.WordTrace tailWord_1965308 prefixEnd_1965308 1009147638126501957111719 := by
  unfold tailWord_1965308
  simp only [CollatzResearch.WordTrace]
  refine ⟨35840335782016119364608289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47787114376021492486144385 35840335782016119364608289)
  ·
    refine ⟨26880251836512089523456217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35840335782016119364608289 26880251836512089523456217)
    ·
      refine ⟨20160188877384067142592163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26880251836512089523456217 20160188877384067142592163)
      ·
        refine ⟨30240283316076100713888245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20160188877384067142592163 30240283316076100713888245)
        ·
          refine ⟨2835026560882134441927023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30240283316076100713888245 2835026560882134441927023)
          ·
            refine ⟨4252539841323201662890535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2835026560882134441927023 4252539841323201662890535)
            ·
              refine ⟨6378809761984802494335803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4252539841323201662890535 6378809761984802494335803)
              ·
                refine ⟨9568214642977203741503705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6378809761984802494335803 9568214642977203741503705)
                ·
                  refine ⟨7176160982232902806127779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9568214642977203741503705 7176160982232902806127779)
                  ·
                    refine ⟨10764241473349354209191669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7176160982232902806127779 10764241473349354209191669)
                    ·
                      refine ⟨1009147638126501957111719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10764241473349354209191669 1009147638126501957111719)
                      ·
                        rfl

theorem cell23_1965308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_1965308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965308 prefixEnd_1965308 := by exact prefixLift 1965308
  have htrace : WordTrace (prefixWord ++ tailWord_1965308) baseStart_1965308 baseEnd_1965308 := by
    simpa [prefixWord, tailWord_1965308, baseEnd_1965308] using wordTrace_append hprefix tailTrace_1965308
  have hstable : (prefixWord ++ tailWord_1965308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965308).length < 2 ^ (prefixWord ++ tailWord_1965308).sum := by decide
  have hdescent : baseEnd_1965308 < baseStart_1965308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965415 : List Nat := [1, 1, 5, 1, 4, 1, 1, 1, 1, 4, 3]
def baseStart_1965415 : Nat := 118140960795 + 1965415 * 2 ^ 59
def prefixEnd_1965415 : Nat := 4983230072969 + 3 ^ 40 * 1965415 * 2
def baseEnd_1965415 : Nat := 1009202580556533038473727

theorem tailTrace_1965415 : CollatzResearch.WordTrace tailWord_1965415 prefixEnd_1965415 1009202580556533038473727 := by
  unfold tailWord_1965415
  simp only [CollatzResearch.WordTrace]
  refine ⟨71684574174644596003361699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47789716116429730668907799 71684574174644596003361699)
  ·
    refine ⟨107526861261966894005042549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71684574174644596003361699 107526861261966894005042549)
    ·
      refine ⟨10080643243309396312972739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107526861261966894005042549 10080643243309396312972739)
      ·
        refine ⟨15120964864964094469459109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10080643243309396312972739 15120964864964094469459109)
        ·
          refine ⟨2835180912180767713023583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15120964864964094469459109 2835180912180767713023583)
          ·
            refine ⟨4252771368271151569535375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2835180912180767713023583 4252771368271151569535375)
            ·
              refine ⟨6379157052406727354303063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4252771368271151569535375 6379157052406727354303063)
              ·
                refine ⟨9568735578610091031454595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6379157052406727354303063 9568735578610091031454595)
                ·
                  refine ⟨14353103367915136547181893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9568735578610091031454595 14353103367915136547181893)
                  ·
                    refine ⟨2691206881484088102596605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14353103367915136547181893 2691206881484088102596605)
                    ·
                      refine ⟨1009202580556533038473727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2691206881484088102596605 1009202580556533038473727)
                      ·
                        rfl

theorem cell23_1965415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_1965415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965415 prefixEnd_1965415 := by exact prefixLift 1965415
  have htrace : WordTrace (prefixWord ++ tailWord_1965415) baseStart_1965415 baseEnd_1965415 := by
    simpa [prefixWord, tailWord_1965415, baseEnd_1965415] using wordTrace_append hprefix tailTrace_1965415
  have hstable : (prefixWord ++ tailWord_1965415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965415).length < 2 ^ (prefixWord ++ tailWord_1965415).sum := by decide
  have hdescent : baseEnd_1965415 < baseStart_1965415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965445 : List Nat := [1, 3, 1, 1, 3, 1, 3, 3, 3, 1, 3]
def baseStart_1965445 : Nat := 118140960795 + 1965445 * 2 ^ 59
def prefixEnd_1965445 : Nat := 4983230072969 + 3 ^ 40 * 1965445 * 2
def baseEnd_1965445 : Nat := 1009217984976167921098589

theorem tailTrace_1965445 : CollatzResearch.WordTrace tailWord_1965445 prefixEnd_1965445 1009217984976167921098589 := by
  unfold tailWord_1965445
  simp only [CollatzResearch.WordTrace]
  refine ⟨71685668364535911126953789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47790445576357274084635859 71685668364535911126953789)
  ·
    refine ⟨26882125636700966672607671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71685668364535911126953789 26882125636700966672607671)
    ·
      refine ⟨40323188455051450008911507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26882125636700966672607671 40323188455051450008911507)
      ·
        refine ⟨60484782682577175013367261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40323188455051450008911507 60484782682577175013367261)
        ·
          refine ⟨22681793505966440630012723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60484782682577175013367261 22681793505966440630012723)
          ·
            refine ⟨34022690258949660945019085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22681793505966440630012723 34022690258949660945019085)
            ·
              refine ⟨12758508847106122854382157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34022690258949660945019085 12758508847106122854382157)
              ·
                refine ⟨4784440817664796070393309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12758508847106122854382157 4784440817664796070393309)
                ·
                  refine ⟨1794165306624298526397491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4784440817664796070393309 1794165306624298526397491)
                  ·
                    refine ⟨2691247959936447789596237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1794165306624298526397491 2691247959936447789596237)
                    ·
                      refine ⟨1009217984976167921098589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2691247959936447789596237 1009217984976167921098589)
                      ·
                        rfl

theorem cell23_1965445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 3, 1, 3].length) (baseStart_1965445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965445 prefixEnd_1965445 := by exact prefixLift 1965445
  have htrace : WordTrace (prefixWord ++ tailWord_1965445) baseStart_1965445 baseEnd_1965445 := by
    simpa [prefixWord, tailWord_1965445, baseEnd_1965445] using wordTrace_append hprefix tailTrace_1965445
  have hstable : (prefixWord ++ tailWord_1965445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965445).length < 2 ^ (prefixWord ++ tailWord_1965445).sum := by decide
  have hdescent : baseEnd_1965445 < baseStart_1965445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965465 : List Nat := [1, 2, 1, 2, 1, 6, 2, 2, 1, 5]
def baseStart_1965465 : Nat := 118140960795 + 1965465 * 2 ^ 59
def prefixEnd_1965465 : Nat := 4983230072969 + 3 ^ 40 * 1965465 * 2
def baseEnd_1965465 : Nat := 336409418196419280949499

theorem tailTrace_1965465 : CollatzResearch.WordTrace tailWord_1965465 prefixEnd_1965465 336409418196419280949499 := by
  unfold tailWord_1965465
  simp only [CollatzResearch.WordTrace]
  refine ⟨71686397824463454542681849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47790931882975636361787899 71686397824463454542681849)
  ·
    refine ⟨53764798368347590907011387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71686397824463454542681849 53764798368347590907011387)
    ·
      refine ⟨80647197552521386360517081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53764798368347590907011387 80647197552521386360517081)
      ·
        refine ⟨60485398164391039770387811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80647197552521386360517081 60485398164391039770387811)
        ·
          refine ⟨90728097246586559655581717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60485398164391039770387811 90728097246586559655581717)
          ·
            refine ⟨4252879558433744983855393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90728097246586559655581717 4252879558433744983855393)
            ·
              refine ⟨3189659668825308737891545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4252879558433744983855393 3189659668825308737891545)
              ·
                refine ⟨2392244751618981553418659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3189659668825308737891545 2392244751618981553418659)
                ·
                  refine ⟨3588367127428472330127989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2392244751618981553418659 3588367127428472330127989)
                  ·
                    refine ⟨336409418196419280949499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3588367127428472330127989 336409418196419280949499)
                    ·
                      rfl

theorem cell23_1965465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 5].length) (baseStart_1965465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965465 prefixEnd_1965465 := by exact prefixLift 1965465
  have htrace : WordTrace (prefixWord ++ tailWord_1965465) baseStart_1965465 baseEnd_1965465 := by
    simpa [prefixWord, tailWord_1965465, baseEnd_1965465] using wordTrace_append hprefix tailTrace_1965465
  have hstable : (prefixWord ++ tailWord_1965465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965465).length < 2 ^ (prefixWord ++ tailWord_1965465).sum := by decide
  have hdescent : baseEnd_1965465 < baseStart_1965465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965495 : List Nat := [1, 1, 3, 1, 3, 2, 2, 4, 2, 4]
def baseStart_1965495 : Nat := 118140960795 + 1965495 * 2 ^ 59
def prefixEnd_1965495 : Nat := 4983230072969 + 3 ^ 40 * 1965495 * 2
def baseEnd_1965495 : Nat := 336414553002964241824453

theorem tailTrace_1965495 : CollatzResearch.WordTrace tailWord_1965495 prefixEnd_1965495 336414553002964241824453 := by
  unfold tailWord_1965495
  simp only [CollatzResearch.WordTrace]
  refine ⟨71687492014354769666273939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47791661342903179777515959 71687492014354769666273939)
  ·
    refine ⟨107531238021532154499410909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71687492014354769666273939 107531238021532154499410909)
    ·
      refine ⟨40324214258074557937279091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107531238021532154499410909 40324214258074557937279091)
      ·
        refine ⟨60486321387111836905918637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40324214258074557937279091 60486321387111836905918637)
        ·
          refine ⟨22682370520166938839719489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60486321387111836905918637 22682370520166938839719489)
          ·
            refine ⟨17011777890125204129789617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22682370520166938839719489 17011777890125204129789617)
            ·
              refine ⟨12758833417593903097342213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17011777890125204129789617 12758833417593903097342213)
              ·
                refine ⟨2392281265798856830751665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12758833417593903097342213 2392281265798856830751665)
                ·
                  refine ⟨1794210949349142623063749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2392281265798856830751665 1794210949349142623063749)
                  ·
                    refine ⟨336414553002964241824453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1794210949349142623063749 336414553002964241824453)
                    ·
                      rfl

theorem cell23_1965495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 2, 4].length) (baseStart_1965495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965495 prefixEnd_1965495 := by exact prefixLift 1965495
  have htrace : WordTrace (prefixWord ++ tailWord_1965495) baseStart_1965495 baseEnd_1965495 := by
    simpa [prefixWord, tailWord_1965495, baseEnd_1965495] using wordTrace_append hprefix tailTrace_1965495
  have hstable : (prefixWord ++ tailWord_1965495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965495).length < 2 ^ (prefixWord ++ tailWord_1965495).sum := by decide
  have hdescent : baseEnd_1965495 < baseStart_1965495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965535 : List Nat := [1, 1, 2, 3, 3, 1, 3, 2, 1, 3, 3]
def baseStart_1965535 : Nat := 118140960795 + 1965535 * 2 ^ 59
def prefixEnd_1965535 : Nat := 4983230072969 + 3 ^ 40 * 1965535 * 2
def baseEnd_1965535 : Nat := 1009264198235072568973175

theorem tailTrace_1965535 : CollatzResearch.WordTrace tailWord_1965535 prefixEnd_1965535 1009264198235072568973175 := by
  unfold tailWord_1965535
  simp only [CollatzResearch.WordTrace]
  refine ⟨71688950934209856497730059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47792633956139904331820039 71688950934209856497730059)
  ·
    refine ⟨107533426401314784746595089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71688950934209856497730059 107533426401314784746595089)
    ·
      refine ⟨80650069800986088559946317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107533426401314784746595089 80650069800986088559946317)
      ·
        refine ⟨30243776175369783209979869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80650069800986088559946317 30243776175369783209979869)
        ·
          refine ⟨11341416065763668703742451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30243776175369783209979869 11341416065763668703742451)
          ·
            refine ⟨17012124098645503055613677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11341416065763668703742451 17012124098645503055613677)
            ·
              refine ⟨6379546536992063645855129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17012124098645503055613677 6379546536992063645855129)
              ·
                refine ⟨4784659902744047734391347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6379546536992063645855129 4784659902744047734391347)
                ·
                  refine ⟨7176989854116071601587021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4784659902744047734391347 7176989854116071601587021)
                  ·
                    refine ⟨2691371195293526850595133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7176989854116071601587021 2691371195293526850595133)
                    ·
                      refine ⟨1009264198235072568973175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2691371195293526850595133 1009264198235072568973175)
                      ·
                        rfl

theorem cell23_1965535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_1965535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965535 prefixEnd_1965535 := by exact prefixLift 1965535
  have htrace : WordTrace (prefixWord ++ tailWord_1965535) baseStart_1965535 baseEnd_1965535 := by
    simpa [prefixWord, tailWord_1965535, baseEnd_1965535] using wordTrace_append hprefix tailTrace_1965535
  have hstable : (prefixWord ++ tailWord_1965535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965535).length < 2 ^ (prefixWord ++ tailWord_1965535).sum := by decide
  have hdescent : baseEnd_1965535 < baseStart_1965535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965539 : List Nat := [1, 1, 1, 6, 2, 2, 3, 1, 1, 2, 3]
def baseStart_1965539 : Nat := 118140960795 + 1965539 * 2 ^ 59
def prefixEnd_1965539 : Nat := 4983230072969 + 3 ^ 40 * 1965539 * 2
def baseEnd_1965539 : Nat := 1009266252157690553323157

theorem tailTrace_1965539 : CollatzResearch.WordTrace tailWord_1965539 prefixEnd_1965539 1009266252157690553323157 := by
  unfold tailWord_1965539
  simp only [CollatzResearch.WordTrace]
  refine ⟨71689096826195365180875671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47792731217463576787250447 71689096826195365180875671)
  ·
    refine ⟨107533645239293047771313507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71689096826195365180875671 107533645239293047771313507)
    ·
      refine ⟨161300467858939571656970261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107533645239293047771313507 161300467858939571656970261)
      ·
        refine ⟨7560959430887792421420481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 161300467858939571656970261 7560959430887792421420481)
        ·
          refine ⟨5670719573165844316065361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7560959430887792421420481 5670719573165844316065361)
          ·
            refine ⟨4253039679874383237049021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5670719573165844316065361 4253039679874383237049021)
            ·
              refine ⟨1594889879952893713893383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4253039679874383237049021 1594889879952893713893383)
              ·
                refine ⟨2392334819929340570840075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1594889879952893713893383 2392334819929340570840075)
                ·
                  refine ⟨3588502229894010856260113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2392334819929340570840075 3588502229894010856260113)
                  ·
                    refine ⟨2691376672420508142195085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3588502229894010856260113 2691376672420508142195085)
                    ·
                      refine ⟨1009266252157690553323157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2691376672420508142195085 1009266252157690553323157)
                      ·
                        rfl

theorem cell23_1965539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_1965539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965539 prefixEnd_1965539 := by exact prefixLift 1965539
  have htrace : WordTrace (prefixWord ++ tailWord_1965539) baseStart_1965539 baseEnd_1965539 := by
    simpa [prefixWord, tailWord_1965539, baseEnd_1965539] using wordTrace_append hprefix tailTrace_1965539
  have hstable : (prefixWord ++ tailWord_1965539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965539).length < 2 ^ (prefixWord ++ tailWord_1965539).sum := by decide
  have hdescent : baseEnd_1965539 < baseStart_1965539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965552 : List Nat := [2, 1, 1, 1, 3, 4, 1, 4, 2, 1, 3]
def baseStart_1965552 : Nat := 118140960795 + 1965552 * 2 ^ 59
def prefixEnd_1965552 : Nat := 4983230072969 + 3 ^ 40 * 1965552 * 2
def baseEnd_1965552 : Nat := 1009272927406199002460597

theorem tailTrace_1965552 : CollatzResearch.WordTrace tailWord_1965552 prefixEnd_1965552 1009272927406199002460597 := by
  unfold tailWord_1965552
  simp only [CollatzResearch.WordTrace]
  refine ⟨35844785487574134200549455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47793047316765512267399273 35844785487574134200549455)
  ·
    refine ⟨53767178231361201300824183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35844785487574134200549455 53767178231361201300824183)
    ·
      refine ⟨80650767347041801951236275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53767178231361201300824183 80650767347041801951236275)
      ·
        refine ⟨120976151020562702926854413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80650767347041801951236275 120976151020562702926854413)
        ·
          refine ⟨45366056632711013597570405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120976151020562702926854413 45366056632711013597570405)
          ·
            refine ⟨8506135618633315049544451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45366056632711013597570405 8506135618633315049544451)
            ·
              refine ⟨12759203427949972574316677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8506135618633315049544451 12759203427949972574316677)
              ·
                refine ⟨2392350642740619857684377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12759203427949972574316677 2392350642740619857684377)
                ·
                  refine ⟨1794262982055464893263283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2392350642740619857684377 1794262982055464893263283)
                  ·
                    refine ⟨2691394473083197339894925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1794262982055464893263283 2691394473083197339894925)
                    ·
                      refine ⟨1009272927406199002460597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2691394473083197339894925 1009272927406199002460597)
                      ·
                        rfl

theorem cell23_1965552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 2, 1, 3].length) (baseStart_1965552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965552 prefixEnd_1965552 := by exact prefixLift 1965552
  have htrace : WordTrace (prefixWord ++ tailWord_1965552) baseStart_1965552 baseEnd_1965552 := by
    simpa [prefixWord, tailWord_1965552, baseEnd_1965552] using wordTrace_append hprefix tailTrace_1965552
  have hstable : (prefixWord ++ tailWord_1965552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965552).length < 2 ^ (prefixWord ++ tailWord_1965552).sum := by decide
  have hdescent : baseEnd_1965552 < baseStart_1965552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965553 : List Nat := [1, 2, 2, 2, 3, 4, 2, 2, 1, 2, 2]
def baseStart_1965553 : Nat := 118140960795 + 1965553 * 2 ^ 59
def prefixEnd_1965553 : Nat := 4983230072969 + 3 ^ 40 * 1965553 * 2
def baseEnd_1965553 : Nat := 1009273440886853498548093

theorem tailTrace_1965553 : CollatzResearch.WordTrace tailWord_1965553 prefixEnd_1965553 1009273440886853498548093 := by
  unfold tailWord_1965553
  simp only [CollatzResearch.WordTrace]
  refine ⟨71689607448144645571885313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47793071632096430381256875 71689607448144645571885313)
  ·
    refine ⟨53767205586108484178913985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71689607448144645571885313 53767205586108484178913985)
    ·
      refine ⟨40325404189581363134185489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53767205586108484178913985 40325404189581363134185489)
      ·
        refine ⟨30244053142186022350639117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40325404189581363134185489 30244053142186022350639117)
        ·
          refine ⟨11341519928319758381489669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30244053142186022350639117 11341519928319758381489669)
          ·
            refine ⟨2126534986559954696529313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11341519928319758381489669 2126534986559954696529313)
            ·
              refine ⟨1594901239919966022396985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2126534986559954696529313 1594901239919966022396985)
              ·
                refine ⟨1196175929939974516797739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1594901239919966022396985 1196175929939974516797739)
                ·
                  refine ⟨1794263894909961775196609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196175929939974516797739 1794263894909961775196609)
                  ·
                    refine ⟨1345697921182471331397457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1794263894909961775196609 1345697921182471331397457)
                    ·
                      refine ⟨1009273440886853498548093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1345697921182471331397457 1009273440886853498548093)
                      ·
                        rfl

theorem cell23_1965553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 2, 1, 2, 2].length) (baseStart_1965553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965553 prefixEnd_1965553 := by exact prefixLift 1965553
  have htrace : WordTrace (prefixWord ++ tailWord_1965553) baseStart_1965553 baseEnd_1965553 := by
    simpa [prefixWord, tailWord_1965553, baseEnd_1965553] using wordTrace_append hprefix tailTrace_1965553
  have hstable : (prefixWord ++ tailWord_1965553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965553).length < 2 ^ (prefixWord ++ tailWord_1965553).sum := by decide
  have hdescent : baseEnd_1965553 < baseStart_1965553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965626 : List Nat := [3, 1, 1, 1, 3, 2, 5, 1, 2, 2, 2]
def baseStart_1965626 : Nat := 118140960795 + 1965626 * 2 ^ 59
def prefixEnd_1965626 : Nat := 4983230072969 + 3 ^ 40 * 1965626 * 2
def baseEnd_1965626 : Nat := 1009310924974631712935257

theorem tailTrace_1965626 : CollatzResearch.WordTrace tailWord_1965626 prefixEnd_1965626 1009310924974631712935257 := by
  unfold tailWord_1965626
  simp only [CollatzResearch.WordTrace]
  refine ⟨17923067494220044759823183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47794846651253452692861821 17923067494220044759823183)
  ·
    refine ⟨26884601241330067139734775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17923067494220044759823183 26884601241330067139734775)
    ·
      refine ⟨40326901861995100709602163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26884601241330067139734775 40326901861995100709602163)
      ·
        refine ⟨60490352792992651064403245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40326901861995100709602163 60490352792992651064403245)
        ·
          refine ⟨22683882297372244149151217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60490352792992651064403245 22683882297372244149151217)
          ·
            refine ⟨17012911723029183111863413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22683882297372244149151217 17012911723029183111863413)
            ·
              refine ⟨1594960474033985916737195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17012911723029183111863413 1594960474033985916737195)
              ·
                refine ⟨2392440711050978875105793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1594960474033985916737195 2392440711050978875105793)
                ·
                  refine ⟨1794330533288234156329345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2392440711050978875105793 1794330533288234156329345)
                  ·
                    refine ⟨1345747899966175617247009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1794330533288234156329345 1345747899966175617247009)
                    ·
                      refine ⟨1009310924974631712935257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1345747899966175617247009 1009310924974631712935257)
                      ·
                        rfl

theorem cell23_1965626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 2, 2, 2].length) (baseStart_1965626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965626 prefixEnd_1965626 := by exact prefixLift 1965626
  have htrace : WordTrace (prefixWord ++ tailWord_1965626) baseStart_1965626 baseEnd_1965626 := by
    simpa [prefixWord, tailWord_1965626, baseEnd_1965626] using wordTrace_append hprefix tailTrace_1965626
  have hstable : (prefixWord ++ tailWord_1965626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965626).length < 2 ^ (prefixWord ++ tailWord_1965626).sum := by decide
  have hdescent : baseEnd_1965626 < baseStart_1965626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965672 : List Nat := [2, 1, 4, 3, 1, 2, 1, 1, 1, 2, 5]
def baseStart_1965672 : Nat := 118140960795 + 1965672 * 2 ^ 59
def prefixEnd_1965672 : Nat := 4983230072969 + 3 ^ 40 * 1965672 * 2
def baseEnd_1965672 : Nat := 1009334545084738532960045

theorem tailTrace_1965672 : CollatzResearch.WordTrace tailWord_1965672 prefixEnd_1965672 1009334545084738532960045 := by
  unfold tailWord_1965672
  simp only [CollatzResearch.WordTrace]
  refine ⟨35846973867356764447733635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47795965156475685930311513 35846973867356764447733635)
  ·
    refine ⟨53770460801035146671600453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35846973867356764447733635 53770460801035146671600453)
    ·
      refine ⟨10081961400194090000925085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53770460801035146671600453 10081961400194090000925085)
      ·
        refine ⟨3780735525072783750346907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10081961400194090000925085 3780735525072783750346907)
        ·
          refine ⟨5671103287609175625520361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3780735525072783750346907 5671103287609175625520361)
          ·
            refine ⟨4253327465706881719140271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5671103287609175625520361 4253327465706881719140271)
            ·
              refine ⟨6379991198560322578710407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4253327465706881719140271 6379991198560322578710407)
              ·
                refine ⟨9569986797840483868065611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6379991198560322578710407 9569986797840483868065611)
                ·
                  refine ⟨14354980196760725802098417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9569986797840483868065611 14354980196760725802098417)
                  ·
                    refine ⟨10766235147570544351573813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14354980196760725802098417 10766235147570544351573813)
                    ·
                      refine ⟨1009334545084738532960045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10766235147570544351573813 1009334545084738532960045)
                      ·
                        rfl

theorem cell23_1965672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_1965672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965672 prefixEnd_1965672 := by exact prefixLift 1965672
  have htrace : WordTrace (prefixWord ++ tailWord_1965672) baseStart_1965672 baseEnd_1965672 := by
    simpa [prefixWord, tailWord_1965672, baseEnd_1965672] using wordTrace_append hprefix tailTrace_1965672
  have hstable : (prefixWord ++ tailWord_1965672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965672).length < 2 ^ (prefixWord ++ tailWord_1965672).sum := by decide
  have hdescent : baseEnd_1965672 < baseStart_1965672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965725 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 1, 2, 6]
def baseStart_1965725 : Nat := 118140960795 + 1965725 * 2 ^ 59
def prefixEnd_1965725 : Nat := 4983230072969 + 3 ^ 40 * 1965725 * 2
def baseEnd_1965725 : Nat := 1009361759559426825597301

theorem tailTrace_1965725 : CollatzResearch.WordTrace tailWord_1965725 prefixEnd_1965725 1009361759559426825597301 := by
  unfold tailWord_1965725
  simp only [CollatzResearch.WordTrace]
  refine ⟨71695880803521518947146629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47797253869014345964764419 71695880803521518947146629)
  ·
    refine ⟨13442977650660284802589993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71695880803521518947146629 13442977650660284802589993)
    ·
      refine ⟨10082233237995213601942495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13442977650660284802589993 10082233237995213601942495)
      ·
        refine ⟨15123349856992820402913743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10082233237995213601942495 15123349856992820402913743)
        ·
          refine ⟨22685024785489230604370615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15123349856992820402913743 22685024785489230604370615)
          ·
            refine ⟨34027537178233845906555923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22685024785489230604370615 34027537178233845906555923)
            ·
              refine ⟨51041305767350768859833885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34027537178233845906555923 51041305767350768859833885)
              ·
                refine ⟨19140489662756538322437707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51041305767350768859833885 19140489662756538322437707)
                ·
                  refine ⟨28710734494134807483656561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19140489662756538322437707 28710734494134807483656561)
                  ·
                    refine ⟨21533050870601105612742421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28710734494134807483656561 21533050870601105612742421)
                    ·
                      refine ⟨1009361759559426825597301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21533050870601105612742421 1009361759559426825597301)
                      ·
                        rfl

theorem cell23_1965725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_1965725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965725 prefixEnd_1965725 := by exact prefixLift 1965725
  have htrace : WordTrace (prefixWord ++ tailWord_1965725) baseStart_1965725 baseEnd_1965725 := by
    simpa [prefixWord, tailWord_1965725, baseEnd_1965725] using wordTrace_append hprefix tailTrace_1965725
  have hstable : (prefixWord ++ tailWord_1965725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965725).length < 2 ^ (prefixWord ++ tailWord_1965725).sum := by decide
  have hdescent : baseEnd_1965725 < baseStart_1965725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965775 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 5]
def baseStart_1965775 : Nat := 118140960795 + 1965775 * 2 ^ 59
def prefixEnd_1965775 : Nat := 4983230072969 + 3 ^ 40 * 1965775 * 2
def baseEnd_1965775 : Nat := 1009387433592151629972071

theorem tailTrace_1965775 : CollatzResearch.WordTrace tailWord_1965775 prefixEnd_1965775 1009387433592151629972071 := by
  unfold tailWord_1965775
  simp only [CollatzResearch.WordTrace]
  refine ⟨71697704453340377486466779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47798469635560251657644519 71697704453340377486466779)
  ·
    refine ⟨107546556680010566229700169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71697704453340377486466779 107546556680010566229700169)
    ·
      refine ⟨80659917510007924672275127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107546556680010566229700169 80659917510007924672275127)
      ·
        refine ⟨120989876265011887008412691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80659917510007924672275127 120989876265011887008412691)
        ·
          refine ⟨181484814397517830512619037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120989876265011887008412691 181484814397517830512619037)
          ·
            refine ⟨68056805399069186442232139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181484814397517830512619037 68056805399069186442232139)
            ·
              refine ⟨102085208098603779663348209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68056805399069186442232139 102085208098603779663348209)
              ·
                refine ⟨76563906073952834747511157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102085208098603779663348209 76563906073952834747511157)
                ·
                  refine ⟨7177866194433078257579171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76563906073952834747511157 7177866194433078257579171)
                  ·
                    refine ⟨10766799291649617386368757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7177866194433078257579171 10766799291649617386368757)
                    ·
                      refine ⟨1009387433592151629972071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10766799291649617386368757 1009387433592151629972071)
                      ·
                        rfl

theorem cell23_1965775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 5].length) (baseStart_1965775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965775 prefixEnd_1965775 := by exact prefixLift 1965775
  have htrace : WordTrace (prefixWord ++ tailWord_1965775) baseStart_1965775 baseEnd_1965775 := by
    simpa [prefixWord, tailWord_1965775, baseEnd_1965775] using wordTrace_append hprefix tailTrace_1965775
  have hstable : (prefixWord ++ tailWord_1965775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965775).length < 2 ^ (prefixWord ++ tailWord_1965775).sum := by decide
  have hdescent : baseEnd_1965775 < baseStart_1965775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965792 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 3]
def baseStart_1965792 : Nat := 118140960795 + 1965792 * 2 ^ 59
def prefixEnd_1965792 : Nat := 4983230072969 + 3 ^ 40 * 1965792 * 2
def baseEnd_1965792 : Nat := 1009396162763278063459493

theorem tailTrace_1965792 : CollatzResearch.WordTrace tailWord_1965792 prefixEnd_1965792 1009396162763278063459493 := by
  unfold tailWord_1965792
  simp only [CollatzResearch.WordTrace]
  refine ⟨35849162247139394694917815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47798882996185859593223753 35849162247139394694917815)
  ·
    refine ⟨53773743370709092042376723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35849162247139394694917815 53773743370709092042376723)
    ·
      refine ⟨80660615056063638063565085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53773743370709092042376723 80660615056063638063565085)
      ·
        refine ⟨30247730646023864273836907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80660615056063638063565085 30247730646023864273836907)
        ·
          refine ⟨45371595969035796410755361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30247730646023864273836907 45371595969035796410755361)
          ·
            refine ⟨34028696976776847308066521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45371595969035796410755361 34028696976776847308066521)
            ·
              refine ⟨25521522732582635481049891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34028696976776847308066521 25521522732582635481049891)
              ·
                refine ⟨38282284098873953221574837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25521522732582635481049891 38282284098873953221574837)
                ·
                  refine ⟨3588964134269433114522641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38282284098873953221574837 3588964134269433114522641)
                  ·
                    refine ⟨2691723100702074835891981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3588964134269433114522641 2691723100702074835891981)
                    ·
                      refine ⟨1009396162763278063459493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2691723100702074835891981 1009396162763278063459493)
                      ·
                        rfl

theorem cell23_1965792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_1965792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965792 prefixEnd_1965792 := by exact prefixLift 1965792
  have htrace : WordTrace (prefixWord ++ tailWord_1965792) baseStart_1965792 baseEnd_1965792 := by
    simpa [prefixWord, tailWord_1965792, baseEnd_1965792] using wordTrace_append hprefix tailTrace_1965792
  have hstable : (prefixWord ++ tailWord_1965792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965792).length < 2 ^ (prefixWord ++ tailWord_1965792).sum := by decide
  have hdescent : baseEnd_1965792 < baseStart_1965792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965806 : List Nat := [4, 1, 2, 1, 1, 2, 1, 4, 3, 2, 2]
def baseStart_1965806 : Nat := 118140960795 + 1965806 * 2 ^ 59
def prefixEnd_1965806 : Nat := 4983230072969 + 3 ^ 40 * 1965806 * 2
def baseEnd_1965806 : Nat := 1009403351492441008684429

theorem tailTrace_1965806 : CollatzResearch.WordTrace tailWord_1965806 prefixEnd_1965806 1009403351492441008684429 := by
  unfold tailWord_1965806
  simp only [CollatzResearch.WordTrace]
  refine ⟨8962354389528508722605659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47799223410818713187230181 8962354389528508722605659)
  ·
    refine ⟨13443531584292763083908489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8962354389528508722605659 13443531584292763083908489)
    ·
      refine ⟨10082648688219572312931367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13443531584292763083908489 10082648688219572312931367)
      ·
        refine ⟨15123973032329358469397051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10082648688219572312931367 15123973032329358469397051)
        ·
          refine ⟨22685959548494037704095577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15123973032329358469397051 22685959548494037704095577)
          ·
            refine ⟨17014469661370528278071683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22685959548494037704095577 17014469661370528278071683)
            ·
              refine ⟨25521704492055792417107525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17014469661370528278071683 25521704492055792417107525)
              ·
                refine ⟨4785319592260461078207661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25521704492055792417107525 4785319592260461078207661)
                ·
                  refine ⟨1794494847097672904327873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4785319592260461078207661 1794494847097672904327873)
                  ·
                    refine ⟨1345871135323254678245905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1794494847097672904327873 1345871135323254678245905)
                    ·
                      refine ⟨1009403351492441008684429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1345871135323254678245905 1009403351492441008684429)
                      ·
                        rfl

theorem cell23_1965806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_1965806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965806 prefixEnd_1965806 := by exact prefixLift 1965806
  have htrace : WordTrace (prefixWord ++ tailWord_1965806) baseStart_1965806 baseEnd_1965806 := by
    simpa [prefixWord, tailWord_1965806, baseEnd_1965806] using wordTrace_append hprefix tailTrace_1965806
  have hstable : (prefixWord ++ tailWord_1965806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965806).length < 2 ^ (prefixWord ++ tailWord_1965806).sum := by decide
  have hdescent : baseEnd_1965806 < baseStart_1965806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965809 : List Nat := [1, 2, 2, 2, 2, 3, 1, 4, 1, 2, 3]
def baseStart_1965809 : Nat := 118140960795 + 1965809 * 2 ^ 59
def prefixEnd_1965809 : Nat := 4983230072969 + 3 ^ 40 * 1965809 * 2
def baseEnd_1965809 : Nat := 1009404891934404496946915

theorem tailTrace_1965809 : CollatzResearch.WordTrace tailWord_1965809 prefixEnd_1965809 1009404891934404496946915 := by
  unfold tailWord_1965809
  simp only [CollatzResearch.WordTrace]
  refine ⟨71698944535217201293204481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47799296356811467528802987 71698944535217201293204481)
  ·
    refine ⟨53774208401412900969903361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71698944535217201293204481 53774208401412900969903361)
    ·
      refine ⟨40330656301059675727427521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53774208401412900969903361 40330656301059675727427521)
      ·
        refine ⟨30247992225794756795570641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40330656301059675727427521 30247992225794756795570641)
        ·
          refine ⟨22685994169346067596677981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30247992225794756795570641 22685994169346067596677981)
          ·
            refine ⟨8507247813504775348754243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22685994169346067596677981 8507247813504775348754243)
            ·
              refine ⟨12760871720257163023131365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8507247813504775348754243 12760871720257163023131365)
              ·
                refine ⟨2392663447548218066837131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12760871720257163023131365 2392663447548218066837131)
                ·
                  refine ⟨3588995171322327100255697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2392663447548218066837131 3588995171322327100255697)
                  ·
                    refine ⟨2691746378491745325191773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3588995171322327100255697 2691746378491745325191773)
                    ·
                      refine ⟨1009404891934404496946915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2691746378491745325191773 1009404891934404496946915)
                      ·
                        rfl

theorem cell23_1965809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_1965809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965809 prefixEnd_1965809 := by exact prefixLift 1965809
  have htrace : WordTrace (prefixWord ++ tailWord_1965809) baseStart_1965809 baseEnd_1965809 := by
    simpa [prefixWord, tailWord_1965809, baseEnd_1965809] using wordTrace_append hprefix tailTrace_1965809
  have hstable : (prefixWord ++ tailWord_1965809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965809).length < 2 ^ (prefixWord ++ tailWord_1965809).sum := by decide
  have hdescent : baseEnd_1965809 < baseStart_1965809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965823 : List Nat := [1, 1, 2, 2, 1, 3, 5, 3, 1, 2, 2]
def baseStart_1965823 : Nat := 118140960795 + 1965823 * 2 ^ 59
def prefixEnd_1965823 : Nat := 4983230072969 + 3 ^ 40 * 1965823 * 2
def baseEnd_1965823 : Nat := 1009412080663567442171851

theorem tailTrace_1965823 : CollatzResearch.WordTrace tailWord_1965823 prefixEnd_1965823 1009412080663567442171851 := by
  unfold tailWord_1965823
  simp only [CollatzResearch.WordTrace]
  refine ⟨71699455157166481684214123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47799636771444321122809415 71699455157166481684214123)
  ·
    refine ⟨107549182735749722526321185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71699455157166481684214123 107549182735749722526321185)
    ·
      refine ⟨80661887051812291894740889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107549182735749722526321185 80661887051812291894740889)
      ·
        refine ⟨60496415288859218921055667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80661887051812291894740889 60496415288859218921055667)
        ·
          refine ⟨90744622933288828381583501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60496415288859218921055667 90744622933288828381583501)
          ·
            refine ⟨34029233599983310643093813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90744622933288828381583501 34029233599983310643093813)
            ·
              refine ⟨3190240649998435372790045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34029233599983310643093813 3190240649998435372790045)
              ·
                refine ⟨1196340243749413264796267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3190240649998435372790045 1196340243749413264796267)
                ·
                  refine ⟨1794510365624119897194401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196340243749413264796267 1794510365624119897194401)
                  ·
                    refine ⟨1345882774218089922895801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1794510365624119897194401 1345882774218089922895801)
                    ·
                      refine ⟨1009412080663567442171851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1345882774218089922895801 1009412080663567442171851)
                      ·
                        rfl

theorem cell23_1965823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 3, 1, 2, 2].length) (baseStart_1965823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965823 prefixEnd_1965823 := by exact prefixLift 1965823
  have htrace : WordTrace (prefixWord ++ tailWord_1965823) baseStart_1965823 baseEnd_1965823 := by
    simpa [prefixWord, tailWord_1965823, baseEnd_1965823] using wordTrace_append hprefix tailTrace_1965823
  have hstable : (prefixWord ++ tailWord_1965823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965823).length < 2 ^ (prefixWord ++ tailWord_1965823).sum := by decide
  have hdescent : baseEnd_1965823 < baseStart_1965823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965826 : List Nat := [3, 4, 1, 1, 1, 1, 1, 5, 1, 2, 3]
def baseStart_1965826 : Nat := 118140960795 + 1965826 * 2 ^ 59
def prefixEnd_1965826 : Nat := 4983230072969 + 3 ^ 40 * 1965826 * 2
def baseEnd_1965826 : Nat := 1009413621105530930434337

theorem tailTrace_1965826 : CollatzResearch.WordTrace tailWord_1965826 prefixEnd_1965826 1009413621105530930434337 := by
  unfold tailWord_1965826
  simp only [CollatzResearch.WordTrace]
  refine ⟨17924891144038903299143333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47799709717437075464382221 17924891144038903299143333)
  ·
    refine ⟨3360917089507294368589375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17924891144038903299143333 3360917089507294368589375)
    ·
      refine ⟨5041375634260941552884063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3360917089507294368589375 5041375634260941552884063)
      ·
        refine ⟨7562063451391412329326095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5041375634260941552884063 7562063451391412329326095)
        ·
          refine ⟨11343095177087118493989143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7562063451391412329326095 11343095177087118493989143)
          ·
            refine ⟨17014642765630677740983715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11343095177087118493989143 17014642765630677740983715)
            ·
              refine ⟨25521964148446016611475573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17014642765630677740983715 25521964148446016611475573)
              ·
                refine ⟨2392684138916814057325835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25521964148446016611475573 2392684138916814057325835)
                ·
                  refine ⟨3589026208375221085988753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2392684138916814057325835 3589026208375221085988753)
                  ·
                    refine ⟨2691769656281415814491565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3589026208375221085988753 2691769656281415814491565)
                    ·
                      refine ⟨1009413621105530930434337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2691769656281415814491565 1009413621105530930434337)
                      ·
                        rfl

theorem cell23_1965826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_1965826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965826 prefixEnd_1965826 := by exact prefixLift 1965826
  have htrace : WordTrace (prefixWord ++ tailWord_1965826) baseStart_1965826 baseEnd_1965826 := by
    simpa [prefixWord, tailWord_1965826, baseEnd_1965826] using wordTrace_append hprefix tailTrace_1965826
  have hstable : (prefixWord ++ tailWord_1965826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965826).length < 2 ^ (prefixWord ++ tailWord_1965826).sum := by decide
  have hdescent : baseEnd_1965826 < baseStart_1965826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965856 : List Nat := [2, 1, 1, 5, 1, 1, 3, 3, 2, 1, 3]
def baseStart_1965856 : Nat := 118140960795 + 1965856 * 2 ^ 59
def prefixEnd_1965856 : Nat := 4983230072969 + 3 ^ 40 * 1965856 * 2
def baseEnd_1965856 : Nat := 1009429025525165813059199

theorem tailTrace_1965856 : CollatzResearch.WordTrace tailWord_1965856 prefixEnd_1965856 1009429025525165813059199 := by
  unfold tailWord_1965856
  simp only [CollatzResearch.WordTrace]
  refine ⟨35850329383023464160082711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47800439177364618880110281 35850329383023464160082711)
  ·
    refine ⟨53775494074535196240124067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35850329383023464160082711 53775494074535196240124067)
    ·
      refine ⟨80663241111802794360186101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53775494074535196240124067 80663241111802794360186101)
      ·
        refine ⟨7562178854231511971267447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80663241111802794360186101 7562178854231511971267447)
        ·
          refine ⟨11343268281347267956901171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7562178854231511971267447 11343268281347267956901171)
          ·
            refine ⟨17014902422020901935351757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11343268281347267956901171 17014902422020901935351757)
            ·
              refine ⟨6380588408257838225756909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17014902422020901935351757 6380588408257838225756909)
              ·
                refine ⟨2392720653096689334658841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6380588408257838225756909 2392720653096689334658841)
                ·
                  refine ⟨1794540489822517000994131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2392720653096689334658841 1794540489822517000994131)
                  ·
                    refine ⟨2691810734733775501491197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1794540489822517000994131 2691810734733775501491197)
                    ·
                      refine ⟨1009429025525165813059199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2691810734733775501491197 1009429025525165813059199)
                      ·
                        rfl

theorem cell23_1965856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_1965856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965856 prefixEnd_1965856 := by exact prefixLift 1965856
  have htrace : WordTrace (prefixWord ++ tailWord_1965856) baseStart_1965856 baseEnd_1965856 := by
    simpa [prefixWord, tailWord_1965856, baseEnd_1965856] using wordTrace_append hprefix tailTrace_1965856
  have hstable : (prefixWord ++ tailWord_1965856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965856).length < 2 ^ (prefixWord ++ tailWord_1965856).sum := by decide
  have hdescent : baseEnd_1965856 < baseStart_1965856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965909 : List Nat := [1, 3, 2, 2, 2, 3, 1, 1, 2, 2, 4]
def baseStart_1965909 : Nat := 118140960795 + 1965909 * 2 ^ 59
def prefixEnd_1965909 : Nat := 4983230072969 + 3 ^ 40 * 1965909 * 2
def baseEnd_1965909 : Nat := 1009456239999854105696455

theorem tailTrace_1965909 : CollatzResearch.WordTrace tailWord_1965909 prefixEnd_1965909 1009456239999854105696455 := by
  unfold tailWord_1965909
  simp only [CollatzResearch.WordTrace]
  refine ⟨71702591834854918371844781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47801727889903278914563187 71702591834854918371844781)
  ·
    refine ⟨26888471938070594389441793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71702591834854918371844781 26888471938070594389441793)
    ·
      refine ⟨20166353953552945792081345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26888471938070594389441793 20166353953552945792081345)
      ·
        refine ⟨15124765465164709344061009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20166353953552945792081345 15124765465164709344061009)
        ·
          refine ⟨11343574098873532008045757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15124765465164709344061009 11343574098873532008045757)
          ·
            refine ⟨4253840287077574503017159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11343574098873532008045757 4253840287077574503017159)
            ·
              refine ⟨6380760430616361754525739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4253840287077574503017159 6380760430616361754525739)
              ·
                refine ⟨9571140645924542631788609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6380760430616361754525739 9571140645924542631788609)
                ·
                  refine ⟨7178355484443406973841457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9571140645924542631788609 7178355484443406973841457)
                  ·
                    refine ⟨5383766613332555230381093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7178355484443406973841457 5383766613332555230381093)
                    ·
                      refine ⟨1009456239999854105696455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5383766613332555230381093 1009456239999854105696455)
                      ·
                        rfl

theorem cell23_1965909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_1965909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965909 prefixEnd_1965909 := by exact prefixLift 1965909
  have htrace : WordTrace (prefixWord ++ tailWord_1965909) baseStart_1965909 baseEnd_1965909 := by
    simpa [prefixWord, tailWord_1965909, baseEnd_1965909] using wordTrace_append hprefix tailTrace_1965909
  have hstable : (prefixWord ++ tailWord_1965909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965909).length < 2 ^ (prefixWord ++ tailWord_1965909).sum := by decide
  have hdescent : baseEnd_1965909 < baseStart_1965909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965989 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 6, 2, 3]
def baseStart_1965989 : Nat := 118140960795 + 1965989 * 2 ^ 59
def prefixEnd_1965989 : Nat := 4983230072969 + 3 ^ 40 * 1965989 * 2
def baseEnd_1965989 : Nat := 1009497318452213792696087

theorem tailTrace_1965989 : CollatzResearch.WordTrace tailWord_1965989 prefixEnd_1965989 1009497318452213792696087 := by
  unfold tailWord_1965989
  simp only [CollatzResearch.WordTrace]
  refine ⟨71705509674565092034757021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47803673116376728023171347 71705509674565092034757021)
  ·
    refine ⟨26889566127961909513033883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71705509674565092034757021 26889566127961909513033883)
    ·
      refine ⟨40334349191942864269550825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26889566127961909513033883 40334349191942864269550825)
      ·
        refine ⟨30250761893957148202163119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40334349191942864269550825 30250761893957148202163119)
        ·
          refine ⟨45376142840935722303244679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30250761893957148202163119 45376142840935722303244679)
          ·
            refine ⟨68064214261403583454867019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45376142840935722303244679 68064214261403583454867019)
            ·
              refine ⟨102096321392105375182300529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68064214261403583454867019 102096321392105375182300529)
              ·
                refine ⟨76572241044079031386725397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102096321392105375182300529 76572241044079031386725397)
                ·
                  refine ⟨3589323798941204596252753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76572241044079031386725397 3589323798941204596252753)
                  ·
                    refine ⟨2691992849205903447189565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3589323798941204596252753 2691992849205903447189565)
                    ·
                      refine ⟨1009497318452213792696087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2691992849205903447189565 1009497318452213792696087)
                      ·
                        rfl

theorem cell23_1965989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_1965989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1965989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1965989 prefixEnd_1965989 := by exact prefixLift 1965989
  have htrace : WordTrace (prefixWord ++ tailWord_1965989) baseStart_1965989 baseEnd_1965989 := by
    simpa [prefixWord, tailWord_1965989, baseEnd_1965989] using wordTrace_append hprefix tailTrace_1965989
  have hstable : (prefixWord ++ tailWord_1965989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965989).length < 2 ^ (prefixWord ++ tailWord_1965989).sum := by decide
  have hdescent : baseEnd_1965989 < baseStart_1965989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966009 : List Nat := [1, 2, 1, 4, 2, 1, 2, 4, 6]
def baseStart_1966009 : Nat := 118140960795 + 1966009 * 2 ^ 59
def prefixEnd_1966009 : Nat := 4983230072969 + 3 ^ 40 * 1966009 * 2
def baseEnd_1966009 : Nat := 112167509785033746049555

theorem tailTrace_1966009 : CollatzResearch.WordTrace tailWord_1966009 prefixEnd_1966009 112167509785033746049555 := by
  unfold tailWord_1966009
  simp only [CollatzResearch.WordTrace]
  refine ⟨71706239134492635450485081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47804159422995090300323387 71706239134492635450485081)
  ·
    refine ⟨53779679350869476587863811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71706239134492635450485081 53779679350869476587863811)
    ·
      refine ⟨80669519026304214881795717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53779679350869476587863811 80669519026304214881795717)
      ·
        refine ⟨15125534817432040290336697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80669519026304214881795717 15125534817432040290336697)
        ·
          refine ⟨11344151113074030217752523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15125534817432040290336697 11344151113074030217752523)
          ·
            refine ⟨17016226669611045326628785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11344151113074030217752523 17016226669611045326628785)
            ·
              refine ⟨12762170002208283994971589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17016226669611045326628785 12762170002208283994971589)
              ·
                refine ⟨2392906875414053249057173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12762170002208283994971589 2392906875414053249057173)
                ·
                  refine ⟨112167509785033746049555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2392906875414053249057173 112167509785033746049555)
                  ·
                    rfl

theorem cell23_1966009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 6].length) (baseStart_1966009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966009 prefixEnd_1966009 := by exact prefixLift 1966009
  have htrace : WordTrace (prefixWord ++ tailWord_1966009) baseStart_1966009 baseEnd_1966009 := by
    simpa [prefixWord, tailWord_1966009, baseEnd_1966009] using wordTrace_append hprefix tailTrace_1966009
  have hstable : (prefixWord ++ tailWord_1966009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966009).length < 2 ^ (prefixWord ++ tailWord_1966009).sum := by decide
  have hdescent : baseEnd_1966009 < baseStart_1966009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966013 : List Nat := [1, 4, 1, 2, 3, 3, 1, 1, 3, 4]
def baseStart_1966013 : Nat := 118140960795 + 1966013 * 2 ^ 59
def prefixEnd_1966013 : Nat := 4983230072969 + 3 ^ 40 * 1966013 * 2
def baseEnd_1966013 : Nat := 336503213995973899598659

theorem tailTrace_1966013 : CollatzResearch.WordTrace tailWord_1966013 prefixEnd_1966013 336503213995973899598659 := by
  unfold tailWord_1966013
  simp only [CollatzResearch.WordTrace]
  refine ⟨71706385026478144133630693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47804256684318762755753795 71706385026478144133630693)
  ·
    refine ⟨13444947192464652025055755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71706385026478144133630693 13444947192464652025055755)
    ·
      refine ⟨20167420788696978037583633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13444947192464652025055755 20167420788696978037583633)
      ·
        refine ⟨15125565591522733528187725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20167420788696978037583633 15125565591522733528187725)
        ·
          refine ⟨5672087096821025073070397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15125565591522733528187725 5672087096821025073070397)
          ·
            refine ⟨2127032661307884402401399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5672087096821025073070397 2127032661307884402401399)
            ·
              refine ⟨3190548991961826603602099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2127032661307884402401399 3190548991961826603602099)
              ·
                refine ⟨4785823487942739905403149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3190548991961826603602099 4785823487942739905403149)
                ·
                  refine ⟨1794683807978527464526181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4785823487942739905403149 1794683807978527464526181)
                  ·
                    refine ⟨336503213995973899598659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1794683807978527464526181 336503213995973899598659)
                    ·
                      rfl

theorem cell23_1966013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_1966013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966013 prefixEnd_1966013 := by exact prefixLift 1966013
  have htrace : WordTrace (prefixWord ++ tailWord_1966013) baseStart_1966013 baseEnd_1966013 := by
    simpa [prefixWord, tailWord_1966013, baseEnd_1966013] using wordTrace_append hprefix tailTrace_1966013
  have hstable : (prefixWord ++ tailWord_1966013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966013).length < 2 ^ (prefixWord ++ tailWord_1966013).sum := by decide
  have hdescent : baseEnd_1966013 < baseStart_1966013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966026 : List Nat := [3, 1, 2, 1, 2, 1, 6, 1, 6]
def baseStart_1966026 : Nat := 118140960795 + 1966026 * 2 ^ 59
def prefixEnd_1966026 : Nat := 4983230072969 + 3 ^ 40 * 1966026 * 2
def baseEnd_1966026 : Nat := 112168479692936683103713

theorem tailTrace_1966026 : CollatzResearch.WordTrace tailWord_1966026 prefixEnd_1966026 112168479692936683103713 := by
  unfold tailWord_1966026
  simp only [CollatzResearch.WordTrace]
  refine ⟨17926714793857761838463483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47804572783620698235902621 17926714793857761838463483)
  ·
    refine ⟨26890072190786642757695225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17926714793857761838463483 26890072190786642757695225)
    ·
      refine ⟨20167554143089982068271419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26890072190786642757695225 20167554143089982068271419)
      ·
        refine ⟨30251331214634973102407129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20167554143089982068271419 30251331214634973102407129)
        ·
          refine ⟨22688498410976229826805347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30251331214634973102407129 22688498410976229826805347)
          ·
            refine ⟨34032747616464344740208021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22688498410976229826805347 34032747616464344740208021)
            ·
              refine ⟨1595285044521766159697251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34032747616464344740208021 1595285044521766159697251)
              ·
                refine ⟨2392927566782649239545877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1595285044521766159697251 2392927566782649239545877)
                ·
                  refine ⟨112168479692936683103713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2392927566782649239545877 112168479692936683103713)
                  ·
                    rfl

theorem cell23_1966026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 6].length) (baseStart_1966026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966026 prefixEnd_1966026 := by exact prefixLift 1966026
  have htrace : WordTrace (prefixWord ++ tailWord_1966026) baseStart_1966026 baseEnd_1966026 := by
    simpa [prefixWord, tailWord_1966026, baseEnd_1966026] using wordTrace_append hprefix tailTrace_1966026
  have hstable : (prefixWord ++ tailWord_1966026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966026).length < 2 ^ (prefixWord ++ tailWord_1966026).sum := by decide
  have hdescent : baseEnd_1966026 < baseStart_1966026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966039 : List Nat := [1, 1, 3, 2, 1, 1, 5, 1, 3, 5]
def baseStart_1966039 : Nat := 118140960795 + 1966039 * 2 ^ 59
def prefixEnd_1966039 : Nat := 4983230072969 + 3 ^ 40 * 1966039 * 2
def baseEnd_1966039 : Nat := 336507664161646199023619

theorem tailTrace_1966039 : CollatzResearch.WordTrace tailWord_1966039 prefixEnd_1966039 336507664161646199023619 := by
  unfold tailWord_1966039
  simp only [CollatzResearch.WordTrace]
  refine ⟨71707333324383950574077171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47804888882922633716051447 71707333324383950574077171)
  ·
    refine ⟨107560999986575925861115757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71707333324383950574077171 107560999986575925861115757)
    ·
      refine ⟨40335374994965972197918409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107560999986575925861115757 40335374994965972197918409)
      ·
        refine ⟨30251531246224479148438807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40335374994965972197918409 30251531246224479148438807)
        ·
          refine ⟨45377296869336718722658211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30251531246224479148438807 45377296869336718722658211)
          ·
            refine ⟨68065945304005078083987317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45377296869336718722658211 68065945304005078083987317)
            ·
              refine ⟨6381182372250476070373811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68065945304005078083987317 6381182372250476070373811)
              ·
                refine ⟨9571773558375714105560717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6381182372250476070373811 9571773558375714105560717)
                ·
                  refine ⟨3589415084390892789585269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9571773558375714105560717 3589415084390892789585269)
                  ·
                    refine ⟨336507664161646199023619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3589415084390892789585269 336507664161646199023619)
                    ·
                      rfl

theorem cell23_1966039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 5].length) (baseStart_1966039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966039 prefixEnd_1966039 := by exact prefixLift 1966039
  have htrace : WordTrace (prefixWord ++ tailWord_1966039) baseStart_1966039 baseEnd_1966039 := by
    simpa [prefixWord, tailWord_1966039, baseEnd_1966039] using wordTrace_append hprefix tailTrace_1966039
  have hstable : (prefixWord ++ tailWord_1966039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966039).length < 2 ^ (prefixWord ++ tailWord_1966039).sum := by decide
  have hdescent : baseEnd_1966039 < baseStart_1966039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966079 : List Nat := [1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 5]
def baseStart_1966079 : Nat := 118140960795 + 1966079 * 2 ^ 59
def prefixEnd_1966079 : Nat := 4983230072969 + 3 ^ 40 * 1966079 * 2
def baseEnd_1966079 : Nat := 1009543531711118440570673

theorem tailTrace_1966079 : CollatzResearch.WordTrace tailWord_1966079 prefixEnd_1966079 1009543531711118440570673 := by
  unfold tailWord_1966079
  simp only [CollatzResearch.WordTrace]
  refine ⟨71708792244239037405533291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47805861496159358270355527 71708792244239037405533291)
  ·
    refine ⟨107563188366358556108299937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71708792244239037405533291 107563188366358556108299937)
    ·
      refine ⟨80672391274768917081224953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107563188366358556108299937 80672391274768917081224953)
      ·
        refine ⟨60504293456076687810918715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80672391274768917081224953 60504293456076687810918715)
        ·
          refine ⟨90756440184115031716378073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60504293456076687810918715 90756440184115031716378073)
          ·
            refine ⟨68067330138086273787283555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90756440184115031716378073 68067330138086273787283555)
            ·
              refine ⟨102100995207129410680925333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68067330138086273787283555 102100995207129410680925333)
              ·
                refine ⟨4785984150334191125668375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102100995207129410680925333 4785984150334191125668375)
                ·
                  refine ⟨7178976225501286688502563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4785984150334191125668375 7178976225501286688502563)
                  ·
                    refine ⟨10768464338251930032753845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7178976225501286688502563 10768464338251930032753845)
                    ·
                      refine ⟨1009543531711118440570673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10768464338251930032753845 1009543531711118440570673)
                      ·
                        rfl

theorem cell23_1966079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_1966079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966079 prefixEnd_1966079 := by exact prefixLift 1966079
  have htrace : WordTrace (prefixWord ++ tailWord_1966079) baseStart_1966079 baseEnd_1966079 := by
    simpa [prefixWord, tailWord_1966079, baseEnd_1966079] using wordTrace_append hprefix tailTrace_1966079
  have hstable : (prefixWord ++ tailWord_1966079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966079).length < 2 ^ (prefixWord ++ tailWord_1966079).sum := by decide
  have hdescent : baseEnd_1966079 < baseStart_1966079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966106 : List Nat := [3, 1, 1, 3, 1, 3, 2, 2, 1, 2, 4]
def baseStart_1966106 : Nat := 118140960795 + 1966106 * 2 ^ 59
def prefixEnd_1966106 : Nat := 4983230072969 + 3 ^ 40 * 1966106 * 2
def baseEnd_1966106 : Nat := 1009557395688789834933049

theorem tailTrace_1966106 : CollatzResearch.WordTrace tailWord_1966106 prefixEnd_1966106 1009557395688789834933049 := by
  unfold tailWord_1966106
  simp only [CollatzResearch.WordTrace]
  refine ⟨17927444253785305254191543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47806518010094147344510781 17927444253785305254191543)
  ·
    refine ⟨26891166380677957881287315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17927444253785305254191543 26891166380677957881287315)
    ·
      refine ⟨40336749571016936821930973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26891166380677957881287315 40336749571016936821930973)
      ·
        refine ⟨15126281089131351308224115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40336749571016936821930973 15126281089131351308224115)
        ·
          refine ⟨22689421633697026962336173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15126281089131351308224115 22689421633697026962336173)
          ·
            refine ⟨8508533112636385110876065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22689421633697026962336173 8508533112636385110876065)
            ·
              refine ⟨6381399834477288833157049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8508533112636385110876065 6381399834477288833157049)
              ·
                refine ⟨4786049875857966624867787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6381399834477288833157049 4786049875857966624867787)
                ·
                  refine ⟨7179074813786949937301681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4786049875857966624867787 7179074813786949937301681)
                  ·
                    refine ⟨5384306110340212452976261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7179074813786949937301681 5384306110340212452976261)
                    ·
                      refine ⟨1009557395688789834933049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5384306110340212452976261 1009557395688789834933049)
                      ·
                        rfl

theorem cell23_1966106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_1966106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966106 prefixEnd_1966106 := by exact prefixLift 1966106
  have htrace : WordTrace (prefixWord ++ tailWord_1966106) baseStart_1966106 baseEnd_1966106 := by
    simpa [prefixWord, tailWord_1966106, baseEnd_1966106] using wordTrace_append hprefix tailTrace_1966106
  have hstable : (prefixWord ++ tailWord_1966106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966106).length < 2 ^ (prefixWord ++ tailWord_1966106).sum := by decide
  have hdescent : baseEnd_1966106 < baseStart_1966106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966116 : List Nat := [2, 3, 1, 4, 2, 1, 10]
def baseStart_1966116 : Nat := 118140960795 + 1966116 * 2 ^ 59
def prefixEnd_1966116 : Nat := 4983230072969 + 3 ^ 40 * 1966116 * 2
def baseEnd_1966116 : Nat := 12463734944386849330963

theorem tailTrace_1966116 : CollatzResearch.WordTrace tailWord_1966116 prefixEnd_1966116 12463734944386849330963 := by
  unfold tailWord_1966116
  simp only [CollatzResearch.WordTrace]
  refine ⟨35855070872552496362315101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47806761163403328483086801 35855070872552496362315101)
  ·
    refine ⟨13445651577207186135868163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35855070872552496362315101 13445651577207186135868163)
    ·
      refine ⟨20168477365810779203802245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13445651577207186135868163 20168477365810779203802245)
      ·
        refine ⟨3781589506089521100712921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20168477365810779203802245 3781589506089521100712921)
        ·
          refine ⟨2836192129567140825534691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3781589506089521100712921 2836192129567140825534691)
          ·
            refine ⟨4254288194350711238302037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2836192129567140825534691 4254288194350711238302037)
            ·
              refine ⟨12463734944386849330963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4254288194350711238302037 12463734944386849330963)
              ·
                rfl

theorem cell23_1966116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 10].length) (baseStart_1966116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966116 prefixEnd_1966116 := by exact prefixLift 1966116
  have htrace : WordTrace (prefixWord ++ tailWord_1966116) baseStart_1966116 baseEnd_1966116 := by
    simpa [prefixWord, tailWord_1966116, baseEnd_1966116] using wordTrace_append hprefix tailTrace_1966116
  have hstable : (prefixWord ++ tailWord_1966116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966116).length < 2 ^ (prefixWord ++ tailWord_1966116).sum := by decide
  have hdescent : baseEnd_1966116 < baseStart_1966116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966120 : List Nat := [2, 1, 5, 3, 1, 1, 1, 1, 4, 4]
def baseStart_1966120 : Nat := 118140960795 + 1966120 * 2 ^ 59
def prefixEnd_1966120 : Nat := 4983230072969 + 3 ^ 40 * 1966120 * 2
def baseEnd_1966120 : Nat := 336521528139317593385995

theorem tailTrace_1966120 : CollatzResearch.WordTrace tailWord_1966120 prefixEnd_1966120 336521528139317593385995 := by
  unfold tailWord_1966120
  simp only [CollatzResearch.WordTrace]
  refine ⟨35855143818545250703887907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47806858424727000938517209 35855143818545250703887907)
  ·
    refine ⟨53782715727817876055831861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35855143818545250703887907 53782715727817876055831861)
    ·
      refine ⟨5042129599482925880234237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53782715727817876055831861 5042129599482925880234237)
      ·
        refine ⟨1890798599806097205087839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5042129599482925880234237 1890798599806097205087839)
        ·
          refine ⟨2836197899709145807631759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1890798599806097205087839 2836197899709145807631759)
          ·
            refine ⟨4254296849563718711447639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2836197899709145807631759 4254296849563718711447639)
            ·
              refine ⟨6381445274345578067171459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4254296849563718711447639 6381445274345578067171459)
              ·
                refine ⟨9572167911518367100757189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6381445274345578067171459 9572167911518367100757189)
                ·
                  refine ⟨1794781483409693831391973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9572167911518367100757189 1794781483409693831391973)
                  ·
                    refine ⟨336521528139317593385995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1794781483409693831391973 336521528139317593385995)
                    ·
                      rfl

theorem cell23_1966120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_1966120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966120 prefixEnd_1966120 := by exact prefixLift 1966120
  have htrace : WordTrace (prefixWord ++ tailWord_1966120) baseStart_1966120 baseEnd_1966120 := by
    simpa [prefixWord, tailWord_1966120, baseEnd_1966120] using wordTrace_append hprefix tailTrace_1966120
  have hstable : (prefixWord ++ tailWord_1966120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966120).length < 2 ^ (prefixWord ++ tailWord_1966120).sum := by decide
  have hdescent : baseEnd_1966120 < baseStart_1966120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966143 : List Nat := [1, 1, 2, 2, 3, 1, 2, 5, 2, 1, 3]
def baseStart_1966143 : Nat := 118140960795 + 1966143 * 2 ^ 59
def prefixEnd_1966143 : Nat := 4983230072969 + 3 ^ 40 * 1966143 * 2
def baseEnd_1966143 : Nat := 1009576394473006190170379

theorem tailTrace_1966143 : CollatzResearch.WordTrace tailWord_1966143 prefixEnd_1966143 1009576394473006190170379 := by
  unfold tailWord_1966143
  simp only [CollatzResearch.WordTrace]
  refine ⟨71711126516007176335863083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47807417677338117557242055 71711126516007176335863083)
  ·
    refine ⟨107566689774010764503794625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71711126516007176335863083 107566689774010764503794625)
    ·
      refine ⟨80675017330508073377845969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107566689774010764503794625 80675017330508073377845969)
      ·
        refine ⟨60506262997881055033384477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80675017330508073377845969 60506262997881055033384477)
        ·
          refine ⟨22689848624205395637519179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60506262997881055033384477 22689848624205395637519179)
          ·
            refine ⟨34034772936308093456278769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22689848624205395637519179 34034772936308093456278769)
            ·
              refine ⟨25526079702231070092209077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34034772936308093456278769 25526079702231070092209077)
              ·
                refine ⟨2393069972084162821144601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25526079702231070092209077 2393069972084162821144601)
                ·
                  refine ⟨1794802479063122115858451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2393069972084162821144601 1794802479063122115858451)
                  ·
                    refine ⟨2692203718594683173787677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1794802479063122115858451 2692203718594683173787677)
                    ·
                      refine ⟨1009576394473006190170379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2692203718594683173787677 1009576394473006190170379)
                      ·
                        rfl

theorem cell23_1966143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 2, 1, 3].length) (baseStart_1966143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966143 prefixEnd_1966143 := by exact prefixLift 1966143
  have htrace : WordTrace (prefixWord ++ tailWord_1966143) baseStart_1966143 baseEnd_1966143 := by
    simpa [prefixWord, tailWord_1966143, baseEnd_1966143] using wordTrace_append hprefix tailTrace_1966143
  have hstable : (prefixWord ++ tailWord_1966143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966143).length < 2 ^ (prefixWord ++ tailWord_1966143).sum := by decide
  have hdescent : baseEnd_1966143 < baseStart_1966143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966234 : List Nat := [3, 1, 1, 5, 2, 1, 2, 2, 2, 2, 2]
def baseStart_1966234 : Nat := 118140960795 + 1966234 * 2 ^ 59
def prefixEnd_1966234 : Nat := 4983230072969 + 3 ^ 40 * 1966234 * 2
def baseEnd_1966234 : Nat := 1009623121212565334132461

theorem tailTrace_1966234 : CollatzResearch.WordTrace tailWord_1966234 prefixEnd_1966234 1009623121212565334132461 := by
  unfold tailWord_1966234
  simp only [CollatzResearch.WordTrace]
  refine ⟨17928611389669374719356439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47809630372451665918283837 17928611389669374719356439)
  ·
    refine ⟨26892917084504062079034659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17928611389669374719356439 26892917084504062079034659)
    ·
      refine ⟨40339375626756093118551989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26892917084504062079034659 40339375626756093118551989)
      ·
        refine ⟨3781816465008383729864249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40339375626756093118551989 3781816465008383729864249)
        ·
          refine ⟨2836362348756287797398187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3781816465008383729864249 2836362348756287797398187)
          ·
            refine ⟨4254543523134431696097281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2836362348756287797398187 4254543523134431696097281)
            ·
              refine ⟨3190907642350823772072961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4254543523134431696097281 3190907642350823772072961)
              ·
                refine ⟨2393180731763117829054721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3190907642350823772072961 2393180731763117829054721)
                ·
                  refine ⟨1794885548822338371791041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2393180731763117829054721 1794885548822338371791041)
                  ·
                    refine ⟨1346164161616753778843281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1794885548822338371791041 1346164161616753778843281)
                    ·
                      refine ⟨1009623121212565334132461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1346164161616753778843281 1009623121212565334132461)
                      ·
                        rfl

theorem cell23_1966234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_1966234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966234 prefixEnd_1966234 := by exact prefixLift 1966234
  have htrace : WordTrace (prefixWord ++ tailWord_1966234) baseStart_1966234 baseEnd_1966234 := by
    simpa [prefixWord, tailWord_1966234, baseEnd_1966234] using wordTrace_append hprefix tailTrace_1966234
  have hstable : (prefixWord ++ tailWord_1966234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966234).length < 2 ^ (prefixWord ++ tailWord_1966234).sum := by decide
  have hdescent : baseEnd_1966234 < baseStart_1966234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966240 : List Nat := [2, 1, 1, 4, 2, 2, 4, 2, 5]
def baseStart_1966240 : Nat := 118140960795 + 1966240 * 2 ^ 59
def prefixEnd_1966240 : Nat := 4983230072969 + 3 ^ 40 * 1966240 * 2
def baseEnd_1966240 : Nat := 112180689121832478961937

theorem tailTrace_1966240 : CollatzResearch.WordTrace tailWord_1966240 prefixEnd_1966240 112180689121832478961937 := by
  unfold tailWord_1966240
  simp only [CollatzResearch.WordTrace]
  refine ⟨35857332198327880951072087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47809776264437174601429449 35857332198327880951072087)
  ·
    refine ⟨53785998297491821426608131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35857332198327880951072087 53785998297491821426608131)
    ·
      refine ⟨80678997446237732139912197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53785998297491821426608131 80678997446237732139912197)
      ·
        refine ⟨15127312021169574776233537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80678997446237732139912197 15127312021169574776233537)
        ·
          refine ⟨11345484015877181082175153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15127312021169574776233537 11345484015877181082175153)
          ·
            refine ⟨8509113011907885811631365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11345484015877181082175153 8509113011907885811631365)
            ·
              refine ⟨1595458689732728589680881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8509113011907885811631365 1595458689732728589680881)
              ·
                refine ⟨1196594017299546442260661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1595458689732728589680881 1196594017299546442260661)
                ·
                  refine ⟨112180689121832478961937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1196594017299546442260661 112180689121832478961937)
                  ·
                    rfl

theorem cell23_1966240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 2, 5].length) (baseStart_1966240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966240 prefixEnd_1966240 := by exact prefixLift 1966240
  have htrace : WordTrace (prefixWord ++ tailWord_1966240) baseStart_1966240 baseEnd_1966240 := by
    simpa [prefixWord, tailWord_1966240, baseEnd_1966240] using wordTrace_append hprefix tailTrace_1966240
  have hstable : (prefixWord ++ tailWord_1966240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966240).length < 2 ^ (prefixWord ++ tailWord_1966240).sum := by decide
  have hdescent : baseEnd_1966240 < baseStart_1966240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966274 : List Nat := [3, 5, 1, 1, 1, 2, 2, 3, 5]
def baseStart_1966274 : Nat := 118140960795 + 1966274 * 2 ^ 59
def prefixEnd_1966274 : Nat := 4983230072969 + 3 ^ 40 * 1966274 * 2
def baseEnd_1966274 : Nat := 112182628937638353070253

theorem tailTrace_1966274 : CollatzResearch.WordTrace tailWord_1966274 prefixEnd_1966274 112182628937638353070253 := by
  unfold tailWord_1966274
  simp only [CollatzResearch.WordTrace]
  refine ⟨17928976119633146427220469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47810602985688390472587917 17928976119633146427220469)
  ·
    refine ⟨1680841511215607477551919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17928976119633146427220469 1680841511215607477551919)
    ·
      refine ⟨2521262266823411216327879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1680841511215607477551919 2521262266823411216327879)
      ·
        refine ⟨3781893400235116824491819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2521262266823411216327879 3781893400235116824491819)
        ·
          refine ⟨5672840100352675236737729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3781893400235116824491819 5672840100352675236737729)
          ·
            refine ⟨4254630075264506427553297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5672840100352675236737729 4254630075264506427553297)
            ·
              refine ⟨3190972556448379820664973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4254630075264506427553297 3190972556448379820664973)
              ·
                refine ⟨1196614708668142432749365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3190972556448379820664973 1196614708668142432749365)
                ·
                  refine ⟨112182628937638353070253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1196614708668142432749365 112182628937638353070253)
                  ·
                    rfl

theorem cell23_1966274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_1966274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966274 prefixEnd_1966274 := by exact prefixLift 1966274
  have htrace : WordTrace (prefixWord ++ tailWord_1966274) baseStart_1966274 baseEnd_1966274 := by
    simpa [prefixWord, tailWord_1966274, baseEnd_1966274] using wordTrace_append hprefix tailTrace_1966274
  have hstable : (prefixWord ++ tailWord_1966274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966274).length < 2 ^ (prefixWord ++ tailWord_1966274).sum := by decide
  have hdescent : baseEnd_1966274 < baseStart_1966274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966290 : List Nat := [3, 2, 2, 2, 1, 2, 1, 2, 2, 4, 2]
def baseStart_1966290 : Nat := 118140960795 + 1966290 * 2 ^ 59
def prefixEnd_1966290 : Nat := 4983230072969 + 3 ^ 40 * 1966290 * 2
def baseEnd_1966290 : Nat := 1009651876129217115032203

theorem tailTrace_1966290 : CollatzResearch.WordTrace tailWord_1966290 prefixEnd_1966290 1009651876129217115032203 := by
  unfold tailWord_1966290
  simp only [CollatzResearch.WordTrace]
  refine ⟨17929122011618655110366081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47810992030983080294309549 17929122011618655110366081)
  ·
    refine ⟨13446841508713991332774561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17929122011618655110366081 13446841508713991332774561)
    ·
      refine ⟨10085131131535493499580921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13446841508713991332774561 10085131131535493499580921)
      ·
        refine ⟨7563848348651620124685691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10085131131535493499580921 7563848348651620124685691)
        ·
          refine ⟨11345772522977430187028537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7563848348651620124685691 11345772522977430187028537)
          ·
            refine ⟨8509329392233072640271403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11345772522977430187028537 8509329392233072640271403)
            ·
              refine ⟨12763994088349608960407105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8509329392233072640271403 12763994088349608960407105)
              ·
                refine ⟨9572995566262206720305329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12763994088349608960407105 9572995566262206720305329)
                ·
                  refine ⟨7179746674696655040228997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9572995566262206720305329 7179746674696655040228997)
                  ·
                    refine ⟨1346202501505622820042937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7179746674696655040228997 1346202501505622820042937)
                    ·
                      refine ⟨1009651876129217115032203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1346202501505622820042937 1009651876129217115032203)
                      ·
                        rfl

theorem cell23_1966290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_1966290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966290 prefixEnd_1966290 := by exact prefixLift 1966290
  have htrace : WordTrace (prefixWord ++ tailWord_1966290) baseStart_1966290 baseEnd_1966290 := by
    simpa [prefixWord, tailWord_1966290, baseEnd_1966290] using wordTrace_append hprefix tailTrace_1966290
  have hstable : (prefixWord ++ tailWord_1966290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966290).length < 2 ^ (prefixWord ++ tailWord_1966290).sum := by decide
  have hdescent : baseEnd_1966290 < baseStart_1966290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966316 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 6]
def baseStart_1966316 : Nat := 118140960795 + 1966316 * 2 ^ 59
def prefixEnd_1966316 : Nat := 4983230072969 + 3 ^ 40 * 1966316 * 2
def baseEnd_1966316 : Nat := 1009665226626234013307083

theorem tailTrace_1966316 : CollatzResearch.WordTrace tailWord_1966316 prefixEnd_1966316 1009665226626234013307083 := by
  unfold tailWord_1966316
  simp only [CollatzResearch.WordTrace]
  refine ⟨35858718172190213440955401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47811624229586951254607201 35858718172190213440955401)
  ·
    refine ⟨26894038629142660080716551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35858718172190213440955401 26894038629142660080716551)
    ·
      refine ⟨40341057943713990121074827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26894038629142660080716551 40341057943713990121074827)
      ·
        refine ⟨60511586915570985181612241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40341057943713990121074827 60511586915570985181612241)
        ·
          refine ⟨45383690186678238886209181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60511586915570985181612241 45383690186678238886209181)
          ·
            refine ⟨17018883820004339582328443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45383690186678238886209181 17018883820004339582328443)
            ·
              refine ⟨25528325730006509373492665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17018883820004339582328443 25528325730006509373492665)
              ·
                refine ⟨19146244297504882030119499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25528325730006509373492665 19146244297504882030119499)
                ·
                  refine ⟨28719366446257323045179249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19146244297504882030119499 28719366446257323045179249)
                  ·
                    refine ⟨21539524834692992283884437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28719366446257323045179249 21539524834692992283884437)
                    ·
                      refine ⟨1009665226626234013307083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21539524834692992283884437 1009665226626234013307083)
                      ·
                        rfl

theorem cell23_1966316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_1966316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966316 prefixEnd_1966316 := by exact prefixLift 1966316
  have htrace : WordTrace (prefixWord ++ tailWord_1966316) baseStart_1966316 baseEnd_1966316 := by
    simpa [prefixWord, tailWord_1966316, baseEnd_1966316] using wordTrace_append hprefix tailTrace_1966316
  have hstable : (prefixWord ++ tailWord_1966316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966316).length < 2 ^ (prefixWord ++ tailWord_1966316).sum := by decide
  have hdescent : baseEnd_1966316 < baseStart_1966316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966357 : List Nat := [1, 3, 2, 1, 2, 1, 2, 6, 1, 1, 3]
def baseStart_1966357 : Nat := 118140960795 + 1966357 * 2 ^ 59
def prefixEnd_1966357 : Nat := 4983230072969 + 3 ^ 40 * 1966357 * 2
def baseEnd_1966357 : Nat := 1009686279333068352894395

theorem tailTrace_1966357 : CollatzResearch.WordTrace tailWord_1966357 prefixEnd_1966357 1009686279333068352894395 := by
  unfold tailWord_1966357
  simp only [CollatzResearch.WordTrace]
  refine ⟨71718931737231890884153325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47812621158154593922768883 71718931737231890884153325)
  ·
    refine ⟨26894599401461959081557497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71718931737231890884153325 26894599401461959081557497)
    ·
      refine ⟨20170949551096469311168123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26894599401461959081557497 20170949551096469311168123)
      ·
        refine ⟨30256424326644703966752185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20170949551096469311168123 30256424326644703966752185)
        ·
          refine ⟨22692318244983527975064139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30256424326644703966752185 22692318244983527975064139)
          ·
            refine ⟨34038477367475291962596209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22692318244983527975064139 34038477367475291962596209)
            ·
              refine ⟨25528858025606468971947157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34038477367475291962596209 25528858025606468971947157)
              ·
                refine ⟨1196665219950303233060023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25528858025606468971947157 1196665219950303233060023)
                ·
                  refine ⟨1794997829925454849590035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196665219950303233060023 1794997829925454849590035)
                  ·
                    refine ⟨2692496744888182274385053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1794997829925454849590035 2692496744888182274385053)
                    ·
                      refine ⟨1009686279333068352894395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2692496744888182274385053 1009686279333068352894395)
                      ·
                        rfl

theorem cell23_1966357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 6, 1, 1, 3].length) (baseStart_1966357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966357 prefixEnd_1966357 := by exact prefixLift 1966357
  have htrace : WordTrace (prefixWord ++ tailWord_1966357) baseStart_1966357 baseEnd_1966357 := by
    simpa [prefixWord, tailWord_1966357, baseEnd_1966357] using wordTrace_append hprefix tailTrace_1966357
  have hstable : (prefixWord ++ tailWord_1966357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966357).length < 2 ^ (prefixWord ++ tailWord_1966357).sum := by decide
  have hdescent : baseEnd_1966357 < baseStart_1966357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966380 : List Nat := [2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 4]
def baseStart_1966380 : Nat := 118140960795 + 1966380 * 2 ^ 59
def prefixEnd_1966380 : Nat := 4983230072969 + 3 ^ 40 * 1966380 * 2
def baseEnd_1966380 : Nat := 1009698089388121762906789

theorem tailTrace_1966380 : CollatzResearch.WordTrace tailWord_1966380 prefixEnd_1966380 1009698089388121762906789 := by
  unfold tailWord_1966380
  simp only [CollatzResearch.WordTrace]
  refine ⟨35859885308074282906120297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47813180410765710541493729 35859885308074282906120297)
  ·
    refine ⟨26894913981055712179590223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35859885308074282906120297 26894913981055712179590223)
    ·
      refine ⟨40342370971583568269385335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26894913981055712179590223 40342370971583568269385335)
      ·
        refine ⟨60513556457375352404078003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40342370971583568269385335 60513556457375352404078003)
        ·
          refine ⟨90770334686063028606117005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60513556457375352404078003 90770334686063028606117005)
          ·
            refine ⟨34038875507273635727293877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90770334686063028606117005 34038875507273635727293877)
            ·
              refine ⟨3191144578806903349433801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34038875507273635727293877 3191144578806903349433801)
              ·
                refine ⟨2393358434105177512075351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3191144578806903349433801 2393358434105177512075351)
                ·
                  refine ⟨3590037651157766268113027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2393358434105177512075351 3590037651157766268113027)
                  ·
                    refine ⟨5385056476736649402169541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3590037651157766268113027 5385056476736649402169541)
                    ·
                      refine ⟨1009698089388121762906789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5385056476736649402169541 1009698089388121762906789)
                      ·
                        rfl

theorem cell23_1966380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 4].length) (baseStart_1966380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966380 prefixEnd_1966380 := by exact prefixLift 1966380
  have htrace : WordTrace (prefixWord ++ tailWord_1966380) baseStart_1966380 baseEnd_1966380 := by
    simpa [prefixWord, tailWord_1966380, baseEnd_1966380] using wordTrace_append hprefix tailTrace_1966380
  have hstable : (prefixWord ++ tailWord_1966380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966380).length < 2 ^ (prefixWord ++ tailWord_1966380).sum := by decide
  have hdescent : baseEnd_1966380 < baseStart_1966380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966420 : List Nat := [2, 4, 1, 1, 2, 4, 1, 8]
def baseStart_1966420 : Nat := 118140960795 + 1966420 * 2 ^ 59
def prefixEnd_1966420 : Nat := 4983230072969 + 3 ^ 40 * 1966420 * 2
def baseEnd_1966420 : Nat := 37396986244974133570615

theorem tailTrace_1966420 : CollatzResearch.WordTrace tailWord_1966420 prefixEnd_1966420 37396986244974133570615 := by
  unfold tailWord_1966420
  simp only [CollatzResearch.WordTrace]
  refine ⟨35860614768001826321848357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47814153024002435095797809 35860614768001826321848357)
  ·
    refine ⟨6723865269000342435346567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35860614768001826321848357 6723865269000342435346567)
    ·
      refine ⟨10085797903500513653019851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6723865269000342435346567 10085797903500513653019851)
      ·
        refine ⟨15128696855250770479529777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10085797903500513653019851 15128696855250770479529777)
        ·
          refine ⟨11346522641438077859647333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15128696855250770479529777 11346522641438077859647333)
          ·
            refine ⟨2127472995269639598683875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11346522641438077859647333 2127472995269639598683875)
            ·
              refine ⟨3191209492904459398025813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2127472995269639598683875 3191209492904459398025813)
              ·
                refine ⟨37396986244974133570615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3191209492904459398025813 37396986244974133570615)
                ·
                  rfl

theorem cell23_1966420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 8].length) (baseStart_1966420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966420 prefixEnd_1966420 := by exact prefixLift 1966420
  have htrace : WordTrace (prefixWord ++ tailWord_1966420) baseStart_1966420 baseEnd_1966420 := by
    simpa [prefixWord, tailWord_1966420, baseEnd_1966420] using wordTrace_append hprefix tailTrace_1966420
  have hstable : (prefixWord ++ tailWord_1966420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966420).length < 2 ^ (prefixWord ++ tailWord_1966420).sum := by decide
  have hdescent : baseEnd_1966420 < baseStart_1966420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966487 : List Nat := [1, 1, 3, 3, 1, 1, 5, 1, 1, 4, 2]
def baseStart_1966487 : Nat := 118140960795 + 1966487 * 2 ^ 59
def prefixEnd_1966487 : Nat := 4983230072969 + 3 ^ 40 * 1966487 * 2
def baseEnd_1966487 : Nat := 1009753031818152844268797

theorem tailTrace_1966487 : CollatzResearch.WordTrace tailWord_1966487 prefixEnd_1966487 1009753031818152844268797 := by
  unfold tailWord_1966487
  simp only [CollatzResearch.WordTrace]
  refine ⟨71723673226760923086385715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47815782151173948724257143 71723673226760923086385715)
  ·
    refine ⟨107585509840141384629578573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71723673226760923086385715 107585509840141384629578573)
    ·
      refine ⟨40344566190053019236091965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107585509840141384629578573 40344566190053019236091965)
      ·
        refine ⟨15129212321269882213534487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40344566190053019236091965 15129212321269882213534487)
        ·
          refine ⟨22693818481904823320301731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15129212321269882213534487 22693818481904823320301731)
          ·
            refine ⟨34040727722857234980452597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22693818481904823320301731 34040727722857234980452597)
            ·
              refine ⟨3191318224017865779417431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34040727722857234980452597 3191318224017865779417431)
              ·
                refine ⟨4786977336026798669126147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3191318224017865779417431 4786977336026798669126147)
                ·
                  refine ⟨7180466004040198003689221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4786977336026798669126147 7180466004040198003689221)
                  ·
                    refine ⟨1346337375757537125691729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7180466004040198003689221 1346337375757537125691729)
                    ·
                      refine ⟨1009753031818152844268797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1346337375757537125691729 1009753031818152844268797)
                      ·
                        rfl

theorem cell23_1966487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_1966487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966487 prefixEnd_1966487 := by exact prefixLift 1966487
  have htrace : WordTrace (prefixWord ++ tailWord_1966487) baseStart_1966487 baseEnd_1966487 := by
    simpa [prefixWord, tailWord_1966487, baseEnd_1966487] using wordTrace_append hprefix tailTrace_1966487
  have hstable : (prefixWord ++ tailWord_1966487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966487).length < 2 ^ (prefixWord ++ tailWord_1966487).sum := by decide
  have hdescent : baseEnd_1966487 < baseStart_1966487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966557 : List Nat := [1, 4, 3, 1, 1, 1, 4, 1, 2, 5]
def baseStart_1966557 : Nat := 118140960795 + 1966557 * 2 ^ 59
def prefixEnd_1966557 : Nat := 4983230072969 + 3 ^ 40 * 1966557 * 2
def baseEnd_1966557 : Nat := 336596325154655856797825

theorem tailTrace_1966557 : CollatzResearch.WordTrace tailWord_1966557 prefixEnd_1966557 336596325154655856797825 := by
  unfold tailWord_1966557
  simp only [CollatzResearch.WordTrace]
  refine ⟨71726226336507325041433925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47817484224338216694289283 71726226336507325041433925)
  ·
    refine ⟨13448667438095123445268861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71726226336507325041433925 13448667438095123445268861)
    ·
      refine ⟨5043250289285671291975823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13448667438095123445268861 5043250289285671291975823)
      ·
        refine ⟨7564875433928506937963735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5043250289285671291975823 7564875433928506937963735)
        ·
          refine ⟨11347313150892760406945603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7564875433928506937963735 11347313150892760406945603)
          ·
            refine ⟨17020969726339140610418405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11347313150892760406945603 17020969726339140610418405)
            ·
              refine ⟨3191431823688588864453451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17020969726339140610418405 3191431823688588864453451)
              ·
                refine ⟨4787147735532883296680177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3191431823688588864453451 4787147735532883296680177)
                ·
                  refine ⟨3590360801649662472510133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4787147735532883296680177 3590360801649662472510133)
                  ·
                    refine ⟨336596325154655856797825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3590360801649662472510133 336596325154655856797825)
                    ·
                      rfl

theorem cell23_1966557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_1966557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966557 prefixEnd_1966557 := by exact prefixLift 1966557
  have htrace : WordTrace (prefixWord ++ tailWord_1966557) baseStart_1966557 baseEnd_1966557 := by
    simpa [prefixWord, tailWord_1966557, baseEnd_1966557] using wordTrace_append hprefix tailTrace_1966557
  have hstable : (prefixWord ++ tailWord_1966557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966557).length < 2 ^ (prefixWord ++ tailWord_1966557).sum := by decide
  have hdescent : baseEnd_1966557 < baseStart_1966557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966577 : List Nat := [1, 2, 2, 2, 3, 1, 2, 2, 2, 4, 2]
def baseStart_1966577 : Nat := 118140960795 + 1966577 * 2 ^ 59
def prefixEnd_1966577 : Nat := 4983230072969 + 3 ^ 40 * 1966577 * 2
def baseEnd_1966577 : Nat := 1009799245077057492143383

theorem tailTrace_1966577 : CollatzResearch.WordTrace tailWord_1966577 prefixEnd_1966577 1009799245077057492143383 := by
  unfold tailWord_1966577
  simp only [CollatzResearch.WordTrace]
  refine ⟨71726955796434868457161985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47817970530956578971441323 71726955796434868457161985)
  ·
    refine ⟨53795216847326151342871489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71726955796434868457161985 53795216847326151342871489)
    ·
      refine ⟨40346412635494613507153617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53795216847326151342871489 40346412635494613507153617)
      ·
        refine ⟨30259809476620960130365213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40346412635494613507153617 30259809476620960130365213)
        ·
          refine ⟨11347428553732860048886955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30259809476620960130365213 11347428553732860048886955)
          ·
            refine ⟨17021142830599290073330433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11347428553732860048886955 17021142830599290073330433)
            ·
              refine ⟨12765857122949467554997825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17021142830599290073330433 12765857122949467554997825)
              ·
                refine ⟨9574392842212100666248369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12765857122949467554997825 9574392842212100666248369)
                ·
                  refine ⟨7180794631659075499686277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9574392842212100666248369 7180794631659075499686277)
                  ·
                    refine ⟨1346398993436076656191177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7180794631659075499686277 1346398993436076656191177)
                    ·
                      refine ⟨1009799245077057492143383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1346398993436076656191177 1009799245077057492143383)
                      ·
                        rfl

theorem cell23_1966577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 4, 2].length) (baseStart_1966577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966577 prefixEnd_1966577 := by exact prefixLift 1966577
  have htrace : WordTrace (prefixWord ++ tailWord_1966577) baseStart_1966577 baseEnd_1966577 := by
    simpa [prefixWord, tailWord_1966577, baseEnd_1966577] using wordTrace_append hprefix tailTrace_1966577
  have hstable : (prefixWord ++ tailWord_1966577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966577).length < 2 ^ (prefixWord ++ tailWord_1966577).sum := by decide
  have hdescent : baseEnd_1966577 < baseStart_1966577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966578 : List Nat := [3, 2, 1, 4, 3, 1, 2, 2, 5]
def baseStart_1966578 : Nat := 118140960795 + 1966578 * 2 ^ 59
def prefixEnd_1966578 : Nat := 4983230072969 + 3 ^ 40 * 1966578 * 2
def baseEnd_1966578 : Nat := 112199973173079109803431

theorem tailTrace_1966578 : CollatzResearch.WordTrace tailWord_1966578 prefixEnd_1966578 112199973173079109803431 := by
  unfold tailWord_1966578
  simp only [CollatzResearch.WordTrace]
  refine ⟨17931748067357811406987097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47817994846287497085298925 17931748067357811406987097)
  ·
    refine ⟨13448811050518358555240323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17931748067357811406987097 13448811050518358555240323)
    ·
      refine ⟨20173216575777537832860485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13448811050518358555240323 20173216575777537832860485)
      ·
        refine ⟨3782478107958288343661341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20173216575777537832860485 3782478107958288343661341)
        ·
          refine ⟨1418429290484358128873003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3782478107958288343661341 1418429290484358128873003)
          ·
            refine ⟨2127643935726537193309505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1418429290484358128873003 2127643935726537193309505)
            ·
              refine ⟨1595732951794902894982129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2127643935726537193309505 1595732951794902894982129)
              ·
                refine ⟨1196799713846177171236597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1595732951794902894982129 1196799713846177171236597)
                ·
                  refine ⟨112199973173079109803431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1196799713846177171236597 112199973173079109803431)
                  ·
                    rfl

theorem cell23_1966578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 2, 5].length) (baseStart_1966578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966578 prefixEnd_1966578 := by exact prefixLift 1966578
  have htrace : WordTrace (prefixWord ++ tailWord_1966578) baseStart_1966578 baseEnd_1966578 := by
    simpa [prefixWord, tailWord_1966578, baseEnd_1966578] using wordTrace_append hprefix tailTrace_1966578
  have hstable : (prefixWord ++ tailWord_1966578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966578).length < 2 ^ (prefixWord ++ tailWord_1966578).sum := by decide
  have hdescent : baseEnd_1966578 < baseStart_1966578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966583 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 12]
def baseStart_1966583 : Nat := 118140960795 + 1966583 * 2 ^ 59
def prefixEnd_1966583 : Nat := 4983230072969 + 3 ^ 40 * 1966583 * 2
def baseEnd_1966583 : Nat := 112200258440109385407595

theorem tailTrace_1966583 : CollatzResearch.WordTrace tailWord_1966583 prefixEnd_1966583 112200258440109385407595 := by
  unfold tailWord_1966583
  simp only [CollatzResearch.WordTrace]
  refine ⟨71727174634413131481880403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47818116422942087654586935 71727174634413131481880403)
  ·
    refine ⟨107590761951619697222820605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71727174634413131481880403 107590761951619697222820605)
    ·
      refine ⟨40346535731857386458557727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107590761951619697222820605 40346535731857386458557727)
      ·
        refine ⟨60519803597786079687836591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40346535731857386458557727 60519803597786079687836591)
        ·
          refine ⟨90779705396679119531754887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60519803597786079687836591 90779705396679119531754887)
          ·
            refine ⟨136169558095018679297632331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90779705396679119531754887 136169558095018679297632331)
            ·
              refine ⟨204254337142528018946448497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136169558095018679297632331 204254337142528018946448497)
              ·
                refine ⟨153190752856896014209836373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204254337142528018946448497 153190752856896014209836373)
                ·
                  refine ⟨112200258440109385407595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 153190752856896014209836373 112200258440109385407595)
                  ·
                    rfl

theorem cell23_1966583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 12].length) (baseStart_1966583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966583 prefixEnd_1966583 := by exact prefixLift 1966583
  have htrace : WordTrace (prefixWord ++ tailWord_1966583) baseStart_1966583 baseEnd_1966583 := by
    simpa [prefixWord, tailWord_1966583, baseEnd_1966583] using wordTrace_append hprefix tailTrace_1966583
  have hstable : (prefixWord ++ tailWord_1966583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966583).length < 2 ^ (prefixWord ++ tailWord_1966583).sum := by decide
  have hdescent : baseEnd_1966583 < baseStart_1966583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966621 : List Nat := [1, 4, 2, 2, 1, 3, 2, 3, 1, 4]
def baseStart_1966621 : Nat := 118140960795 + 1966621 * 2 ^ 59
def prefixEnd_1966621 : Nat := 4983230072969 + 3 ^ 40 * 1966621 * 2
def baseEnd_1966621 : Nat := 336607279408618439997727

theorem tailTrace_1966621 : CollatzResearch.WordTrace tailWord_1966621 prefixEnd_1966621 336607279408618439997727 := by
  unfold tailWord_1966621
  simp only [CollatzResearch.WordTrace]
  refine ⟨71728560608275463971763717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47819040405516975981175811 71728560608275463971763717)
  ·
    refine ⟨13449105114051649494705697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71728560608275463971763717 13449105114051649494705697)
    ·
      refine ⟨10086828835538737121029273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13449105114051649494705697 10086828835538737121029273)
      ·
        refine ⟨7565121626654052840771955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10086828835538737121029273 7565121626654052840771955)
        ·
          refine ⟨11347682439981079261157933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7565121626654052840771955 11347682439981079261157933)
          ·
            refine ⟨4255380914992904722934225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11347682439981079261157933 4255380914992904722934225)
            ·
              refine ⟨3191535686244678542200669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4255380914992904722934225 3191535686244678542200669)
              ·
                refine ⟨1196825882341754453325251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3191535686244678542200669 1196825882341754453325251)
                ·
                  refine ⟨1795238823512631679987877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196825882341754453325251 1795238823512631679987877)
                  ·
                    refine ⟨336607279408618439997727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1795238823512631679987877 336607279408618439997727)
                    ·
                      rfl

theorem cell23_1966621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_1966621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966621 prefixEnd_1966621 := by exact prefixLift 1966621
  have htrace : WordTrace (prefixWord ++ tailWord_1966621) baseStart_1966621 baseEnd_1966621 := by
    simpa [prefixWord, tailWord_1966621, baseEnd_1966621] using wordTrace_append hprefix tailTrace_1966621
  have hstable : (prefixWord ++ tailWord_1966621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966621).length < 2 ^ (prefixWord ++ tailWord_1966621).sum := by decide
  have hdescent : baseEnd_1966621 < baseStart_1966621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966634 : List Nat := [3, 1, 4, 1, 1, 4, 1, 2, 6]
def baseStart_1966634 : Nat := 118140960795 + 1966634 * 2 ^ 59
def prefixEnd_1966634 : Nat := 4983230072969 + 3 ^ 40 * 1966634 * 2
def baseEnd_1966634 : Nat := 112203168163818196570069

theorem tailTrace_1966634 : CollatzResearch.WordTrace tailWord_1966634 prefixEnd_1966634 112203168163818196570069 := by
  unfold tailWord_1966634
  simp only [CollatzResearch.WordTrace]
  refine ⟨17932258689307091797996739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47819356504818911461324637 17932258689307091797996739)
  ·
    refine ⟨26898388033960637696995109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17932258689307091797996739 26898388033960637696995109)
    ·
      refine ⟨5043447756367619568186583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26898388033960637696995109 5043447756367619568186583)
      ·
        refine ⟨7565171634551429352279875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5043447756367619568186583 7565171634551429352279875)
        ·
          refine ⟨11347757451827144028419813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7565171634551429352279875 11347757451827144028419813)
          ·
            refine ⟨2127704522217589505328715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11347757451827144028419813 2127704522217589505328715)
            ·
              refine ⟨3191556783326384257993073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2127704522217589505328715 3191556783326384257993073)
              ·
                refine ⟨2393667587494788193494805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3191556783326384257993073 2393667587494788193494805)
                ·
                  refine ⟨112203168163818196570069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2393667587494788193494805 112203168163818196570069)
                  ·
                    rfl

theorem cell23_1966634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 6].length) (baseStart_1966634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966634 prefixEnd_1966634 := by exact prefixLift 1966634
  have htrace : WordTrace (prefixWord ++ tailWord_1966634) baseStart_1966634 baseEnd_1966634 := by
    simpa [prefixWord, tailWord_1966634, baseEnd_1966634] using wordTrace_append hprefix tailTrace_1966634
  have hstable : (prefixWord ++ tailWord_1966634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966634).length < 2 ^ (prefixWord ++ tailWord_1966634).sum := by decide
  have hdescent : baseEnd_1966634 < baseStart_1966634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966667 : List Nat := [1, 1, 1, 1, 3, 1, 5, 4, 1, 1, 4]
def baseStart_1966667 : Nat := 118140960795 + 1966667 * 2 ^ 59
def prefixEnd_1966667 : Nat := 4983230072969 + 3 ^ 40 * 1966667 * 2
def baseEnd_1966667 : Nat := 1009845458335962140017969

theorem tailTrace_1966667 : CollatzResearch.WordTrace tailWord_1966667 prefixEnd_1966667 1009845458335962140017969 := by
  unfold tailWord_1966667
  simp only [CollatzResearch.WordTrace]
  refine ⟨71730238366108813827938255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47820158910739209218625503 71730238366108813827938255)
  ·
    refine ⟨107595357549163220741907383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71730238366108813827938255 107595357549163220741907383)
    ·
      refine ⟨161393036323744831112861075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107595357549163220741907383 161393036323744831112861075)
      ·
        refine ⟨242089554485617246669291613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161393036323744831112861075 242089554485617246669291613)
        ·
          refine ⟨90783582932106467500984355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242089554485617246669291613 90783582932106467500984355)
          ·
            refine ⟨136175374398159701251476533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90783582932106467500984355 136175374398159701251476533)
            ·
              refine ⟨12766441349827471992325925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136175374398159701251476533 12766441349827471992325925)
              ·
                refine ⟨2393707753092650998561111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12766441349827471992325925 2393707753092650998561111)
                ·
                  refine ⟨3590561629638976497841667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2393707753092650998561111 3590561629638976497841667)
                  ·
                    refine ⟨5385842444458464746762501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3590561629638976497841667 5385842444458464746762501)
                    ·
                      refine ⟨1009845458335962140017969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5385842444458464746762501 1009845458335962140017969)
                      ·
                        rfl

theorem cell23_1966667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 1, 4].length) (baseStart_1966667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966667 prefixEnd_1966667 := by exact prefixLift 1966667
  have htrace : WordTrace (prefixWord ++ tailWord_1966667) baseStart_1966667 baseEnd_1966667 := by
    simpa [prefixWord, tailWord_1966667, baseEnd_1966667] using wordTrace_append hprefix tailTrace_1966667
  have hstable : (prefixWord ++ tailWord_1966667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966667).length < 2 ^ (prefixWord ++ tailWord_1966667).sum := by decide
  have hdescent : baseEnd_1966667 < baseStart_1966667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966677 : List Nat := [1, 3, 2, 2, 1, 1, 3, 2, 4, 4]
def baseStart_1966677 : Nat := 118140960795 + 1966677 * 2 ^ 59
def prefixEnd_1966677 : Nat := 4983230072969 + 3 ^ 40 * 1966677 * 2
def baseEnd_1966677 : Nat := 336616864380835700297641

theorem tailTrace_1966677 : CollatzResearch.WordTrace tailWord_1966677 prefixEnd_1966677 336616864380835700297641 := by
  unfold tailWord_1966677
  simp only [CollatzResearch.WordTrace]
  refine ⟨71730603096072585535802285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47820402064048390357201523 71730603096072585535802285)
  ·
    refine ⟨26898976161027219575925857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71730603096072585535802285 26898976161027219575925857)
    ·
      refine ⟨20174232120770414681944393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26898976161027219575925857 20174232120770414681944393)
      ·
        refine ⟨15130674090577811011458295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20174232120770414681944393 15130674090577811011458295)
        ·
          refine ⟨22696011135866716517187443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15130674090577811011458295 22696011135866716517187443)
          ·
            refine ⟨34044016703800074775781165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22696011135866716517187443 34044016703800074775781165)
            ·
              refine ⟨12766506263925028040917937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34044016703800074775781165 12766506263925028040917937)
              ·
                refine ⟨9574879697943771030688453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12766506263925028040917937 9574879697943771030688453)
                ·
                  refine ⟨1795289943364457068254085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9574879697943771030688453 1795289943364457068254085)
                  ·
                    refine ⟨336616864380835700297641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1795289943364457068254085 336616864380835700297641)
                    ·
                      rfl

theorem cell23_1966677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_1966677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966677 prefixEnd_1966677 := by exact prefixLift 1966677
  have htrace : WordTrace (prefixWord ++ tailWord_1966677) baseStart_1966677 baseEnd_1966677 := by
    simpa [prefixWord, tailWord_1966677, baseEnd_1966677] using wordTrace_append hprefix tailTrace_1966677
  have hstable : (prefixWord ++ tailWord_1966677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966677).length < 2 ^ (prefixWord ++ tailWord_1966677).sum := by decide
  have hdescent : baseEnd_1966677 < baseStart_1966677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966722 : List Nat := [3, 4, 3, 1, 1, 1, 2, 1, 2, 3, 2]
def baseStart_1966722 : Nat := 118140960795 + 1966722 * 2 ^ 59
def prefixEnd_1966722 : Nat := 4983230072969 + 3 ^ 40 * 1966722 * 2
def baseEnd_1966722 : Nat := 1009873699771959424830217

theorem tailTrace_1966722 : CollatzResearch.WordTrace tailWord_1966722 prefixEnd_1966722 1009873699771959424830217 := by
  unfold tailWord_1966722
  simp only [CollatzResearch.WordTrace]
  refine ⟨17933061095227389555297605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47821496253939705480793613 17933061095227389555297605)
  ·
    refine ⟨3362448955355135541618301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17933061095227389555297605 3362448955355135541618301)
    ·
      refine ⟨1260918358258175828106863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3362448955355135541618301 1260918358258175828106863)
      ·
        refine ⟨1891377537387263742160295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1260918358258175828106863 1891377537387263742160295)
        ·
          refine ⟨2837066306080895613240443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1891377537387263742160295 2837066306080895613240443)
          ·
            refine ⟨4255599459121343419860665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2837066306080895613240443 4255599459121343419860665)
            ·
              refine ⟨3191699594341007564895499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4255599459121343419860665 3191699594341007564895499)
              ·
                refine ⟨4787549391511511347343249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3191699594341007564895499 4787549391511511347343249)
                ·
                  refine ⟨3590662043633633510507437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4787549391511511347343249 3590662043633633510507437)
                  ·
                    refine ⟨1346498266362612566440289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3590662043633633510507437 1346498266362612566440289)
                    ·
                      refine ⟨1009873699771959424830217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1346498266362612566440289 1009873699771959424830217)
                      ·
                        rfl

theorem cell23_1966722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_1966722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966722 prefixEnd_1966722 := by exact prefixLift 1966722
  have htrace : WordTrace (prefixWord ++ tailWord_1966722) baseStart_1966722 baseEnd_1966722 := by
    simpa [prefixWord, tailWord_1966722, baseEnd_1966722] using wordTrace_append hprefix tailTrace_1966722
  have hstable : (prefixWord ++ tailWord_1966722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966722).length < 2 ^ (prefixWord ++ tailWord_1966722).sum := by decide
  have hdescent : baseEnd_1966722 < baseStart_1966722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966734 : List Nat := [4, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3]
def baseStart_1966734 : Nat := 118140960795 + 1966734 * 2 ^ 59
def prefixEnd_1966734 : Nat := 4983230072969 + 3 ^ 40 * 1966734 * 2
def baseEnd_1966734 : Nat := 1009879861539813377880161

theorem tailTrace_1966734 : CollatzResearch.WordTrace tailWord_1966734 prefixEnd_1966734 1009879861539813377880161 := by
  unfold tailWord_1966734
  simp only [CollatzResearch.WordTrace]
  refine ⟨8966585257108260533828407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47821788037910722847084837 8966585257108260533828407)
  ·
    refine ⟨13449877885662390800742611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8966585257108260533828407 13449877885662390800742611)
    ·
      refine ⟨20174816828493586201113917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13449877885662390800742611 20174816828493586201113917)
      ·
        refine ⟨7565556310685094825417719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20174816828493586201113917 7565556310685094825417719)
        ·
          refine ⟨11348334466027642238126579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7565556310685094825417719 11348334466027642238126579)
          ·
            refine ⟨17022501699041463357189869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11348334466027642238126579 17022501699041463357189869)
            ·
              refine ⟨6383438137140548758946201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17022501699041463357189869 6383438137140548758946201)
              ·
                refine ⟨4787578602855411569209651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6383438137140548758946201 4787578602855411569209651)
                ·
                  refine ⟨7181367904283117353814477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4787578602855411569209651 7181367904283117353814477)
                  ·
                    refine ⟨2693012964106169007680429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7181367904283117353814477 2693012964106169007680429)
                    ·
                      refine ⟨1009879861539813377880161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2693012964106169007680429 1009879861539813377880161)
                      ·
                        rfl

theorem cell23_1966734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_1966734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966734 prefixEnd_1966734 := by exact prefixLift 1966734
  have htrace : WordTrace (prefixWord ++ tailWord_1966734) baseStart_1966734 baseEnd_1966734 := by
    simpa [prefixWord, tailWord_1966734, baseEnd_1966734] using wordTrace_append hprefix tailTrace_1966734
  have hstable : (prefixWord ++ tailWord_1966734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966734).length < 2 ^ (prefixWord ++ tailWord_1966734).sum := by decide
  have hdescent : baseEnd_1966734 < baseStart_1966734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966738 : List Nat := [3, 2, 3, 1, 2, 2, 3, 1, 1, 2, 3]
def baseStart_1966738 : Nat := 118140960795 + 1966738 * 2 ^ 59
def prefixEnd_1966738 : Nat := 4983230072969 + 3 ^ 40 * 1966738 * 2
def baseEnd_1966738 : Nat := 1009881915462431362230143

theorem tailTrace_1966738 : CollatzResearch.WordTrace tailWord_1966738 prefixEnd_1966738 1009881915462431362230143 := by
  unfold tailWord_1966738
  simp only [CollatzResearch.WordTrace]
  refine ⟨17933206987212898238443217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47821885299234395302515245 17933206987212898238443217)
  ·
    refine ⟨13449905240409673678832413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17933206987212898238443217 13449905240409673678832413)
    ·
      refine ⟨5043714465153627629562155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13449905240409673678832413 5043714465153627629562155)
      ·
        refine ⟨7565571697730441444343233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5043714465153627629562155 7565571697730441444343233)
        ·
          refine ⟨5674178773297831083257425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7565571697730441444343233 5674178773297831083257425)
          ·
            refine ⟨4255634079973373312443069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5674178773297831083257425 4255634079973373312443069)
            ·
              refine ⟨1595862779990014992166151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4255634079973373312443069 1595862779990014992166151)
              ·
                refine ⟨2393794169985022488249227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1595862779990014992166151 2393794169985022488249227)
                ·
                  refine ⟨3590691254977533732373841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2393794169985022488249227 3590691254977533732373841)
                  ·
                    refine ⟨2693018441233150299280381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3590691254977533732373841 2693018441233150299280381)
                    ·
                      refine ⟨1009881915462431362230143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2693018441233150299280381 1009881915462431362230143)
                      ·
                        rfl

theorem cell23_1966738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_1966738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966738 prefixEnd_1966738 := by exact prefixLift 1966738
  have htrace : WordTrace (prefixWord ++ tailWord_1966738) baseStart_1966738 baseEnd_1966738 := by
    simpa [prefixWord, tailWord_1966738, baseEnd_1966738] using wordTrace_append hprefix tailTrace_1966738
  have hstable : (prefixWord ++ tailWord_1966738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966738).length < 2 ^ (prefixWord ++ tailWord_1966738).sum := by decide
  have hdescent : baseEnd_1966738 < baseStart_1966738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966752 : List Nat := [2, 1, 1, 4, 4, 2, 2, 2, 1, 2, 2]
def baseStart_1966752 : Nat := 118140960795 + 1966752 * 2 ^ 59
def prefixEnd_1966752 : Nat := 4983230072969 + 3 ^ 40 * 1966752 * 2
def baseEnd_1966752 : Nat := 1009889104191594307455079

theorem tailTrace_1966752 : CollatzResearch.WordTrace tailWord_1966752 prefixEnd_1966752 1009889104191594307455079 := by
  unfold tailWord_1966752
  simp only [CollatzResearch.WordTrace]
  refine ⟨35866669285400436672391255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47822225713867248896521673 35866669285400436672391255)
  ·
    refine ⟨53800003928100655008586883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35866669285400436672391255 53800003928100655008586883)
    ·
      refine ⟨80700005892150982512880325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53800003928100655008586883 80700005892150982512880325)
      ·
        refine ⟨15131251104778309221165061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80700005892150982512880325 15131251104778309221165061)
        ·
          refine ⟨2837109582145932978968449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15131251104778309221165061 2837109582145932978968449)
          ·
            refine ⟨2127832186609449734226337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2837109582145932978968449 2127832186609449734226337)
            ·
              refine ⟨1595874139957087300669753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2127832186609449734226337 1595874139957087300669753)
              ·
                refine ⟨1196905604967815475502315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1595874139957087300669753 1196905604967815475502315)
                ·
                  refine ⟨1795358407451723213253473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196905604967815475502315 1795358407451723213253473)
                  ·
                    refine ⟨1346518805588792409940105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1795358407451723213253473 1346518805588792409940105)
                    ·
                      refine ⟨1009889104191594307455079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1346518805588792409940105 1009889104191594307455079)
                      ·
                        rfl

theorem cell23_1966752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_1966752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966752 prefixEnd_1966752 := by exact prefixLift 1966752
  have htrace : WordTrace (prefixWord ++ tailWord_1966752) baseStart_1966752 baseEnd_1966752 := by
    simpa [prefixWord, tailWord_1966752, baseEnd_1966752] using wordTrace_append hprefix tailTrace_1966752
  have hstable : (prefixWord ++ tailWord_1966752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966752).length < 2 ^ (prefixWord ++ tailWord_1966752).sum := by decide
  have hdescent : baseEnd_1966752 < baseStart_1966752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966767 : List Nat := [1, 1, 2, 1, 2, 6, 1, 1, 2, 6]
def baseStart_1966767 : Nat := 118140960795 + 1966767 * 2 ^ 59
def prefixEnd_1966767 : Nat := 4983230072969 + 3 ^ 40 * 1966767 * 2
def baseEnd_1966767 : Nat := 336632268800470582922503

theorem tailTrace_1966767 : CollatzResearch.WordTrace tailWord_1966767 prefixEnd_1966767 336632268800470582922503 := by
  unfold tailWord_1966767
  simp only [CollatzResearch.WordTrace]
  refine ⟨71733885665746530906578555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47822590443831020604385703 71733885665746530906578555)
  ·
    refine ⟨107600828498619796359867833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71733885665746530906578555 107600828498619796359867833)
    ·
      refine ⟨80700621373964847269900875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107600828498619796359867833 80700621373964847269900875)
      ·
        refine ⟨121050932060947270904851313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80700621373964847269900875 121050932060947270904851313)
        ·
          refine ⟨90788199045710453178638485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121050932060947270904851313 90788199045710453178638485)
          ·
            refine ⟨4255696830267677492748679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90788199045710453178638485 4255696830267677492748679)
            ·
              refine ⟨6383545245401516239123019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4255696830267677492748679 6383545245401516239123019)
              ·
                refine ⟨9575317868102274358684529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6383545245401516239123019 9575317868102274358684529)
                ·
                  refine ⟨7181488401076705769013397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9575317868102274358684529 7181488401076705769013397)
                  ·
                    refine ⟨336632268800470582922503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7181488401076705769013397 336632268800470582922503)
                    ·
                      rfl

theorem cell23_1966767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 6].length) (baseStart_1966767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966767 prefixEnd_1966767 := by exact prefixLift 1966767
  have htrace : WordTrace (prefixWord ++ tailWord_1966767) baseStart_1966767 baseEnd_1966767 := by
    simpa [prefixWord, tailWord_1966767, baseEnd_1966767] using wordTrace_append hprefix tailTrace_1966767
  have hstable : (prefixWord ++ tailWord_1966767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966767).length < 2 ^ (prefixWord ++ tailWord_1966767).sum := by decide
  have hdescent : baseEnd_1966767 < baseStart_1966767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966777 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 4, 4, 3]
def baseStart_1966777 : Nat := 118140960795 + 1966777 * 2 ^ 59
def prefixEnd_1966777 : Nat := 4983230072969 + 3 ^ 40 * 1966777 * 2
def baseEnd_1966777 : Nat := 1009901941207956709642463

theorem tailTrace_1966777 : CollatzResearch.WordTrace tailWord_1966777 prefixEnd_1966777 1009901941207956709642463 := by
  unfold tailWord_1966777
  simp only [CollatzResearch.WordTrace]
  refine ⟨71734250395710302614442585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47822833597140201742961723 71734250395710302614442585)
  ·
    refine ⟨53800687796782726960831939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71734250395710302614442585 53800687796782726960831939)
    ·
      refine ⟨80701031695174090441247909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53800687796782726960831939 80701031695174090441247909)
      ·
        refine ⟨15131443442845141957733983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80701031695174090441247909 15131443442845141957733983)
        ·
          refine ⟨22697165164267712936600975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15131443442845141957733983 22697165164267712936600975)
          ·
            refine ⟨34045747746401569404901463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22697165164267712936600975 34045747746401569404901463)
            ·
              refine ⟨51068621619602354107352195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34045747746401569404901463 51068621619602354107352195)
              ·
                refine ⟨76602932429403531161028293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51068621619602354107352195 76602932429403531161028293)
                ·
                  refine ⟨14363049830513162092692805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76602932429403531161028293 14363049830513162092692805)
                  ·
                    refine ⟨2693071843221217892379901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14363049830513162092692805 2693071843221217892379901)
                    ·
                      refine ⟨1009901941207956709642463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2693071843221217892379901 1009901941207956709642463)
                      ·
                        rfl

theorem cell23_1966777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_1966777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966777 prefixEnd_1966777 := by exact prefixLift 1966777
  have htrace : WordTrace (prefixWord ++ tailWord_1966777) baseStart_1966777 baseEnd_1966777 := by
    simpa [prefixWord, tailWord_1966777, baseEnd_1966777] using wordTrace_append hprefix tailTrace_1966777
  have hstable : (prefixWord ++ tailWord_1966777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966777).length < 2 ^ (prefixWord ++ tailWord_1966777).sum := by decide
  have hdescent : baseEnd_1966777 < baseStart_1966777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966808 : List Nat := [2, 1, 2, 2, 3, 2, 3, 2, 2, 2, 2]
def baseStart_1966808 : Nat := 118140960795 + 1966808 * 2 ^ 59
def prefixEnd_1966808 : Nat := 4983230072969 + 3 ^ 40 * 1966808 * 2
def baseEnd_1966808 : Nat := 1009917859108246088354821

theorem tailTrace_1966808 : CollatzResearch.WordTrace tailWord_1966808 prefixEnd_1966808 1009917859108246088354821 := by
  unfold tailWord_1966808
  simp only [CollatzResearch.WordTrace]
  refine ⟨35867690529298997454410539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47823587372398663272547385 35867690529298997454410539)
  ·
    refine ⟨53801535793948496181615809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35867690529298997454410539 53801535793948496181615809)
    ·
      refine ⟨40351151845461372136211857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53801535793948496181615809 40351151845461372136211857)
      ·
        refine ⟨30263363884096029102158893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40351151845461372136211857 30263363884096029102158893)
        ·
          refine ⟨11348761456536010913309585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30263363884096029102158893 11348761456536010913309585)
          ·
            refine ⟨8511571092402008184982189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11348761456536010913309585 8511571092402008184982189)
            ·
              refine ⟨3191839159650753069368321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8511571092402008184982189 3191839159650753069368321)
              ·
                refine ⟨2393879369738064802026241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3191839159650753069368321 2393879369738064802026241)
                ·
                  refine ⟨1795409527303548601519681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2393879369738064802026241 1795409527303548601519681)
                  ·
                    refine ⟨1346557145477661451139761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1795409527303548601519681 1346557145477661451139761)
                    ·
                      refine ⟨1009917859108246088354821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1346557145477661451139761 1009917859108246088354821)
                      ·
                        rfl

theorem cell23_1966808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 2, 2, 2].length) (baseStart_1966808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966808 prefixEnd_1966808 := by exact prefixLift 1966808
  have htrace : WordTrace (prefixWord ++ tailWord_1966808) baseStart_1966808 baseEnd_1966808 := by
    simpa [prefixWord, tailWord_1966808, baseEnd_1966808] using wordTrace_append hprefix tailTrace_1966808
  have hstable : (prefixWord ++ tailWord_1966808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966808).length < 2 ^ (prefixWord ++ tailWord_1966808).sum := by decide
  have hdescent : baseEnd_1966808 < baseStart_1966808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966901 : List Nat := [1, 3, 3, 1, 3, 1, 1, 3, 2, 2, 3]
def baseStart_1966901 : Nat := 118140960795 + 1966901 * 2 ^ 59
def prefixEnd_1966901 : Nat := 4983230072969 + 3 ^ 40 * 1966901 * 2
def baseEnd_1966901 : Nat := 1009965612809114224491893

theorem tailTrace_1966901 : CollatzResearch.WordTrace tailWord_1966901 prefixEnd_1966901 1009965612809114224491893 := by
  unfold tailWord_1966901
  simp only [CollatzResearch.WordTrace]
  refine ⟨71738773047261071791956557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47825848698174047861304371 71738773047261071791956557)
  ·
    refine ⟨26902039892722901921983709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71738773047261071791956557 26902039892722901921983709)
    ·
      refine ⟨10088264959771088220743891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26902039892722901921983709 10088264959771088220743891)
      ·
        refine ⟨15132397439656632331115837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10088264959771088220743891 15132397439656632331115837)
        ·
          refine ⟨5674649039871237124168439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15132397439656632331115837 5674649039871237124168439)
          ·
            refine ⟨8511973559806855686252659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5674649039871237124168439 8511973559806855686252659)
            ·
              refine ⟨12767960339710283529378989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8511973559806855686252659 12767960339710283529378989)
              ·
                refine ⟨4787985127391356323517121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12767960339710283529378989 4787985127391356323517121)
                ·
                  refine ⟨3590988845543517242637841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4787985127391356323517121 3590988845543517242637841)
                  ·
                    refine ⟨2693241634157637931978381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3590988845543517242637841 2693241634157637931978381)
                    ·
                      refine ⟨1009965612809114224491893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2693241634157637931978381 1009965612809114224491893)
                      ·
                        rfl

theorem cell23_1966901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_1966901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966901 prefixEnd_1966901 := by exact prefixLift 1966901
  have htrace : WordTrace (prefixWord ++ tailWord_1966901) baseStart_1966901 baseEnd_1966901 := by
    simpa [prefixWord, tailWord_1966901, baseEnd_1966901] using wordTrace_append hprefix tailTrace_1966901
  have hstable : (prefixWord ++ tailWord_1966901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966901).length < 2 ^ (prefixWord ++ tailWord_1966901).sum := by decide
  have hdescent : baseEnd_1966901 < baseStart_1966901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966927 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 5]
def baseStart_1966927 : Nat := 118140960795 + 1966927 * 2 ^ 59
def prefixEnd_1966927 : Nat := 4983230072969 + 3 ^ 40 * 1966927 * 2
def baseEnd_1966927 : Nat := 1009978963306131122766773

theorem tailTrace_1966927 : CollatzResearch.WordTrace tailWord_1966927 prefixEnd_1966927 1009978963306131122766773 := by
  unfold tailWord_1966927
  simp only [CollatzResearch.WordTrace]
  refine ⟨71739721345166878232403035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47826480896777918821602023 71739721345166878232403035)
  ·
    refine ⟨107609582017750317348604553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71739721345166878232403035 107609582017750317348604553)
    ·
      refine ⟨80707186513312738011453415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107609582017750317348604553 80707186513312738011453415)
      ·
        refine ⟨121060779769969107017180123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80707186513312738011453415 121060779769969107017180123)
        ·
          refine ⟨181591169654953660525770185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121060779769969107017180123 181591169654953660525770185)
          ·
            refine ⟨136193377241215245394327639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181591169654953660525770185 136193377241215245394327639)
            ·
              refine ⟨204290065861822868091491459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136193377241215245394327639 204290065861822868091491459)
              ·
                refine ⟨306435098792734302137237189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204290065861822868091491459 306435098792734302137237189)
                ·
                  refine ⟨57456581023637681650731973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 306435098792734302137237189 57456581023637681650731973)
                  ·
                    refine ⟨10773108941932065309512245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57456581023637681650731973 10773108941932065309512245)
                    ·
                      refine ⟨1009978963306131122766773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10773108941932065309512245 1009978963306131122766773)
                      ·
                        rfl

theorem cell23_1966927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 5].length) (baseStart_1966927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966927 prefixEnd_1966927 := by exact prefixLift 1966927
  have htrace : WordTrace (prefixWord ++ tailWord_1966927) baseStart_1966927 baseEnd_1966927 := by
    simpa [prefixWord, tailWord_1966927, baseEnd_1966927] using wordTrace_append hprefix tailTrace_1966927
  have hstable : (prefixWord ++ tailWord_1966927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966927).length < 2 ^ (prefixWord ++ tailWord_1966927).sum := by decide
  have hdescent : baseEnd_1966927 < baseStart_1966927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966948 : List Nat := [2, 3, 1, 1, 4, 2, 1, 2, 3, 1, 3]
def baseStart_1966948 : Nat := 118140960795 + 1966948 * 2 ^ 59
def prefixEnd_1966948 : Nat := 4983230072969 + 3 ^ 40 * 1966948 * 2
def baseEnd_1966948 : Nat := 1009989746399875540604177

theorem tailTrace_1966948 : CollatzResearch.WordTrace tailWord_1966948 prefixEnd_1966948 1009989746399875540604177 := by
  unfold tailWord_1966948
  simp only [CollatzResearch.WordTrace]
  refine ⟨35870243639045399409458749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47826991518727199212611665 35870243639045399409458749)
  ·
    refine ⟨13451341364642024778547031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35870243639045399409458749 13451341364642024778547031)
    ·
      refine ⟨20177012046963037167820547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13451341364642024778547031 20177012046963037167820547)
      ·
        refine ⟨30265518070444555751730821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20177012046963037167820547 30265518070444555751730821)
        ·
          refine ⟨5674784638208354203449529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30265518070444555751730821 5674784638208354203449529)
          ·
            refine ⟨4256088478656265652587147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5674784638208354203449529 4256088478656265652587147)
            ·
              refine ⟨6384132717984398478880721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4256088478656265652587147 6384132717984398478880721)
              ·
                refine ⟨4788099538488298859160541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6384132717984398478880721 4788099538488298859160541)
                ·
                  refine ⟨1795537326933112072185203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4788099538488298859160541 1795537326933112072185203)
                  ·
                    refine ⟨2693305990399668108277805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1795537326933112072185203 2693305990399668108277805)
                    ·
                      refine ⟨1009989746399875540604177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2693305990399668108277805 1009989746399875540604177)
                      ·
                        rfl

theorem cell23_1966948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_1966948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966948 prefixEnd_1966948 := by exact prefixLift 1966948
  have htrace : WordTrace (prefixWord ++ tailWord_1966948) baseStart_1966948 baseEnd_1966948 := by
    simpa [prefixWord, tailWord_1966948, baseEnd_1966948] using wordTrace_append hprefix tailTrace_1966948
  have hstable : (prefixWord ++ tailWord_1966948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966948).length < 2 ^ (prefixWord ++ tailWord_1966948).sum := by decide
  have hdescent : baseEnd_1966948 < baseStart_1966948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966965 : List Nat := [1, 3, 4, 1, 1, 2, 1, 5, 1, 1, 3]
def baseStart_1966965 : Nat := 118140960795 + 1966965 * 2 ^ 59
def prefixEnd_1966965 : Nat := 4983230072969 + 3 ^ 40 * 1966965 * 2
def baseEnd_1966965 : Nat := 1009998475571001974091599

theorem tailTrace_1966965 : CollatzResearch.WordTrace tailWord_1966965 prefixEnd_1966965 1009998475571001974091599 := by
  unfold tailWord_1966965
  simp only [CollatzResearch.WordTrace]
  refine ⟨71741107319029210722286349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47827404879352807148190899 71741107319029210722286349)
  ·
    refine ⟨26902915244635954020857381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71741107319029210722286349 26902915244635954020857381)
    ·
      refine ⟨5044296608369241378910759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26902915244635954020857381 5044296608369241378910759)
      ·
        refine ⟨7566444912553862068366139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5044296608369241378910759 7566444912553862068366139)
        ·
          refine ⟨11349667368830793102549209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7566444912553862068366139 11349667368830793102549209)
          ·
            refine ⟨8512250526623094826911907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11349667368830793102549209 8512250526623094826911907)
            ·
              refine ⟨12768375789934642240367861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8512250526623094826911907 12768375789934642240367861)
              ·
                refine ⟨1197035230306372710034487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12768375789934642240367861 1197035230306372710034487)
                ·
                  refine ⟨1795552845459559065051731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1197035230306372710034487 1795552845459559065051731)
                  ·
                    refine ⟨2693329268189338597577597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1795552845459559065051731 2693329268189338597577597)
                    ·
                      refine ⟨1009998475571001974091599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2693329268189338597577597 1009998475571001974091599)
                      ·
                        rfl

theorem cell23_1966965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_1966965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966965 prefixEnd_1966965 := by exact prefixLift 1966965
  have htrace : WordTrace (prefixWord ++ tailWord_1966965) baseStart_1966965 baseEnd_1966965 := by
    simpa [prefixWord, tailWord_1966965, baseEnd_1966965] using wordTrace_append hprefix tailTrace_1966965
  have hstable : (prefixWord ++ tailWord_1966965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966965).length < 2 ^ (prefixWord ++ tailWord_1966965).sum := by decide
  have hdescent : baseEnd_1966965 < baseStart_1966965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966981 : List Nat := [1, 3, 1, 1, 3, 4, 1, 1, 4, 4]
def baseStart_1966981 : Nat := 118140960795 + 1966981 * 2 ^ 59
def prefixEnd_1966981 : Nat := 4983230072969 + 3 ^ 40 * 1966981 * 2
def baseEnd_1966981 : Nat := 336668897087157970497175

theorem tailTrace_1966981 : CollatzResearch.WordTrace tailWord_1966981 prefixEnd_1966981 336668897087157970497175 := by
  unfold tailWord_1966981
  simp only [CollatzResearch.WordTrace]
  refine ⟨71741690886971245454868797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47827793924647496969912531 71741690886971245454868797)
  ·
    refine ⟨26903134082614217045575799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71741690886971245454868797 26903134082614217045575799)
    ·
      refine ⟨40354701123921325568363699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26903134082614217045575799 40354701123921325568363699)
      ·
        refine ⟨60532051685881988352545549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40354701123921325568363699 60532051685881988352545549)
        ·
          refine ⟨22699519382205745632204581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60532051685881988352545549 22699519382205745632204581)
          ·
            refine ⟨4256159884163577306038359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22699519382205745632204581 4256159884163577306038359)
            ·
              refine ⟨6384239826245365959057539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4256159884163577306038359 6384239826245365959057539)
              ·
                refine ⟨9576359739368048938586309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6384239826245365959057539 9576359739368048938586309)
                ·
                  refine ⟨1795567451131509175984933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9576359739368048938586309 1795567451131509175984933)
                  ·
                    refine ⟨336668897087157970497175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1795567451131509175984933 336668897087157970497175)
                    ·
                      rfl

theorem cell23_1966981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 4, 4].length) (baseStart_1966981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966981 prefixEnd_1966981 := by exact prefixLift 1966981
  have htrace : WordTrace (prefixWord ++ tailWord_1966981) baseStart_1966981 baseEnd_1966981 := by
    simpa [prefixWord, tailWord_1966981, baseEnd_1966981] using wordTrace_append hprefix tailTrace_1966981
  have hstable : (prefixWord ++ tailWord_1966981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966981).length < 2 ^ (prefixWord ++ tailWord_1966981).sum := by decide
  have hdescent : baseEnd_1966981 < baseStart_1966981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966988 : List Nat := [2, 2, 1, 2, 1, 2, 3, 3, 3, 2, 2]
def baseStart_1966988 : Nat := 118140960795 + 1966988 * 2 ^ 59
def prefixEnd_1966988 : Nat := 4983230072969 + 3 ^ 40 * 1966988 * 2
def baseEnd_1966988 : Nat := 1010010285626055384103993

theorem tailTrace_1966988 : CollatzResearch.WordTrace tailWord_1966988 prefixEnd_1966988 1010010285626055384103993 := by
  unfold tailWord_1966988
  simp only [CollatzResearch.WordTrace]
  refine ⟨35870973098972942825186809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47827964131963923766915745 35870973098972942825186809)
  ·
    refine ⟨26903229824229707118890107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35870973098972942825186809 26903229824229707118890107)
    ·
      refine ⟨40354844736344560678335161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26903229824229707118890107 40354844736344560678335161)
      ·
        refine ⟨30266133552258420508751371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40354844736344560678335161 30266133552258420508751371)
        ·
          refine ⟨45399200328387630763127057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30266133552258420508751371 45399200328387630763127057)
          ·
            refine ⟨34049400246290723072345293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45399200328387630763127057 34049400246290723072345293)
            ·
              refine ⟨12768525092359021152129485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34049400246290723072345293 12768525092359021152129485)
              ·
                refine ⟨4788196909634632932048557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12768525092359021152129485 4788196909634632932048557)
                ·
                  refine ⟨1795573841112987349518209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4788196909634632932048557 1795573841112987349518209)
                  ·
                    refine ⟨1346680380834740512138657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1795573841112987349518209 1346680380834740512138657)
                    ·
                      refine ⟨1010010285626055384103993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1346680380834740512138657 1010010285626055384103993)
                      ·
                        rfl

theorem cell23_1966988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 3, 2, 2].length) (baseStart_1966988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1966988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1966988 prefixEnd_1966988 := by exact prefixLift 1966988
  have htrace : WordTrace (prefixWord ++ tailWord_1966988) baseStart_1966988 baseEnd_1966988 := by
    simpa [prefixWord, tailWord_1966988, baseEnd_1966988] using wordTrace_append hprefix tailTrace_1966988
  have hstable : (prefixWord ++ tailWord_1966988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966988).length < 2 ^ (prefixWord ++ tailWord_1966988).sum := by decide
  have hdescent : baseEnd_1966988 < baseStart_1966988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967028 : List Nat := [2, 5, 2, 1, 1, 3, 9]
def baseStart_1967028 : Nat := 118140960795 + 1967028 * 2 ^ 59
def prefixEnd_1967028 : Nat := 4983230072969 + 3 ^ 40 * 1967028 * 2
def baseEnd_1967028 : Nat := 12469516356200434908689

theorem tailTrace_1967028 : CollatzResearch.WordTrace tailWord_1967028 prefixEnd_1967028 12469516356200434908689 := by
  unfold tailWord_1967028
  simp only [CollatzResearch.WordTrace]
  refine ⟨35871702558900486240914869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47828936745200648321219825 35871702558900486240914869)
  ·
    refine ⟨3362972114896920585085769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35871702558900486240914869 3362972114896920585085769)
    ·
      refine ⟨2522229086172690438814327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3362972114896920585085769 2522229086172690438814327)
      ·
        refine ⟨3783343629259035658221491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2522229086172690438814327 3783343629259035658221491)
        ·
          refine ⟨5675015443888553487332237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3783343629259035658221491 5675015443888553487332237)
          ·
            refine ⟨2128130791458207557749589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5675015443888553487332237 2128130791458207557749589)
            ·
              refine ⟨12469516356200434908689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2128130791458207557749589 12469516356200434908689)
              ·
                rfl

theorem cell23_1967028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 9].length) (baseStart_1967028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967028 prefixEnd_1967028 := by exact prefixLift 1967028
  have htrace : WordTrace (prefixWord ++ tailWord_1967028) baseStart_1967028 baseEnd_1967028 := by
    simpa [prefixWord, tailWord_1967028, baseEnd_1967028] using wordTrace_append hprefix tailTrace_1967028
  have hstable : (prefixWord ++ tailWord_1967028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967028).length < 2 ^ (prefixWord ++ tailWord_1967028).sum := by decide
  have hdescent : baseEnd_1967028 < baseStart_1967028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967034 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 2, 2, 5]
def baseStart_1967034 : Nat := 118140960795 + 1967034 * 2 ^ 59
def prefixEnd_1967034 : Nat := 4983230072969 + 3 ^ 40 * 1967034 * 2
def baseEnd_1967034 : Nat := 1010033905736162204128781

theorem tailTrace_1967034 : CollatzResearch.WordTrace tailWord_1967034 prefixEnd_1967034 1010033905736162204128781 := by
  unfold tailWord_1967034
  simp only [CollatzResearch.WordTrace]
  refine ⟨17935905988944808876637039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47829082637186157004365437 17935905988944808876637039)
  ·
    refine ⟨26903858983417213314955559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17935905988944808876637039 26903858983417213314955559)
    ·
      refine ⟨40355788475125819972433339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26903858983417213314955559 40355788475125819972433339)
      ·
        refine ⟨60533682712688729958650009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40355788475125819972433339 60533682712688729958650009)
        ·
          refine ⟨45400262034516547468987507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60533682712688729958650009 45400262034516547468987507)
          ·
            refine ⟨68100393051774821203481261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45400262034516547468987507 68100393051774821203481261)
            ·
              refine ⟨25537647394415557951305473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68100393051774821203481261 25537647394415557951305473)
              ·
                refine ⟨19153235545811668463479105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25537647394415557951305473 19153235545811668463479105)
                ·
                  refine ⟨14364926659358751347609329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19153235545811668463479105 14364926659358751347609329)
                  ·
                    refine ⟨10773694994519063510706997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14364926659358751347609329 10773694994519063510706997)
                    ·
                      refine ⟨1010033905736162204128781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10773694994519063510706997 1010033905736162204128781)
                      ·
                        rfl

theorem cell23_1967034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_1967034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967034 prefixEnd_1967034 := by exact prefixLift 1967034
  have htrace : WordTrace (prefixWord ++ tailWord_1967034) baseStart_1967034 baseEnd_1967034 := by
    simpa [prefixWord, tailWord_1967034, baseEnd_1967034] using wordTrace_append hprefix tailTrace_1967034
  have hstable : (prefixWord ++ tailWord_1967034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967034).length < 2 ^ (prefixWord ++ tailWord_1967034).sum := by decide
  have hdescent : baseEnd_1967034 < baseStart_1967034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967038 : List Nat := [4, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3]
def baseStart_1967038 : Nat := 118140960795 + 1967038 * 2 ^ 59
def prefixEnd_1967038 : Nat := 4983230072969 + 3 ^ 40 * 1967038 * 2
def baseEnd_1967038 : Nat := 1010035959658780188478763

theorem tailTrace_1967038 : CollatzResearch.WordTrace tailWord_1967038 prefixEnd_1967038 1010035959658780188478763 := by
  unfold tailWord_1967038
  simp only [CollatzResearch.WordTrace]
  refine ⟨8967971230970593023711721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47829179898509829459795845 8967971230970593023711721)
  ·
    refine ⟨6725978423227944767783791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8967971230970593023711721 6725978423227944767783791)
    ·
      refine ⟨10088967634841917151675687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6725978423227944767783791 10088967634841917151675687)
      ·
        refine ⟨15133451452262875727513531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10088967634841917151675687 15133451452262875727513531)
        ·
          refine ⟨22700177178394313591270297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15133451452262875727513531 22700177178394313591270297)
          ·
            refine ⟨17025132883795735193452723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22700177178394313591270297 17025132883795735193452723)
            ·
              refine ⟨25537699325693602790179085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17025132883795735193452723 25537699325693602790179085)
              ·
                refine ⟨9576637247135101046317157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25537699325693602790179085 9576637247135101046317157)
                ·
                  refine ⟨1795619483837831446184467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9576637247135101046317157 1795619483837831446184467)
                  ·
                    refine ⟨2693429225756747169276701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1795619483837831446184467 2693429225756747169276701)
                    ·
                      refine ⟨1010035959658780188478763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2693429225756747169276701 1010035959658780188478763)
                      ·
                        rfl

theorem cell23_1967038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_1967038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967038 prefixEnd_1967038 := by exact prefixLift 1967038
  have htrace : WordTrace (prefixWord ++ tailWord_1967038) baseStart_1967038 baseEnd_1967038 := by
    simpa [prefixWord, tailWord_1967038, baseEnd_1967038] using wordTrace_append hprefix tailTrace_1967038
  have hstable : (prefixWord ++ tailWord_1967038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967038).length < 2 ^ (prefixWord ++ tailWord_1967038).sum := by decide
  have hdescent : baseEnd_1967038 < baseStart_1967038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967055 : List Nat := [1, 1, 2, 1, 1, 6, 4, 1, 2, 1, 3]
def baseStart_1967055 : Nat := 118140960795 + 1967055 * 2 ^ 59
def prefixEnd_1967055 : Nat := 4983230072969 + 3 ^ 40 * 1967055 * 2
def baseEnd_1967055 : Nat := 1010044688829906621966185

theorem tailTrace_1967055 : CollatzResearch.WordTrace tailWord_1967055 prefixEnd_1967055 1010044688829906621966185 := by
  unfold tailWord_1967055
  simp only [CollatzResearch.WordTrace]
  refine ⟨71744389888703156093062619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47829593259135437395375079 71744389888703156093062619)
  ·
    refine ⟨107616584833054734139593929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71744389888703156093062619 107616584833054734139593929)
    ·
      refine ⟨80712438624791050604695447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107616584833054734139593929 80712438624791050604695447)
      ·
        refine ⟨121068657937186575907043171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80712438624791050604695447 121068657937186575907043171)
        ·
          refine ⟨181602986905779863860564757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121068657937186575907043171 181602986905779863860564757)
          ·
            refine ⟨8512640011208431118463973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 181602986905779863860564757 8512640011208431118463973)
            ·
              refine ⟨1596120002101580834711995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8512640011208431118463973 1596120002101580834711995)
              ·
                refine ⟨2394180003152371252067993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1596120002101580834711995 2394180003152371252067993)
                ·
                  refine ⟨1795635002364278439050995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2394180003152371252067993 1795635002364278439050995)
                  ·
                    refine ⟨2693452503546417658576493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1795635002364278439050995 2693452503546417658576493)
                    ·
                      refine ⟨1010044688829906621966185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2693452503546417658576493 1010044688829906621966185)
                      ·
                        rfl

theorem cell23_1967055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 2, 1, 3].length) (baseStart_1967055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967055 prefixEnd_1967055 := by exact prefixLift 1967055
  have htrace : WordTrace (prefixWord ++ tailWord_1967055) baseStart_1967055 baseEnd_1967055 := by
    simpa [prefixWord, tailWord_1967055, baseEnd_1967055] using wordTrace_append hprefix tailTrace_1967055
  have hstable : (prefixWord ++ tailWord_1967055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967055).length < 2 ^ (prefixWord ++ tailWord_1967055).sum := by decide
  have hdescent : baseEnd_1967055 < baseStart_1967055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967065 : List Nat := [1, 2, 1, 2, 5, 1, 3, 2, 1, 3, 2]
def baseStart_1967065 : Nat := 118140960795 + 1967065 * 2 ^ 59
def prefixEnd_1967065 : Nat := 4983230072969 + 3 ^ 40 * 1967065 * 2
def baseEnd_1967065 : Nat := 1010049823636451582841139

theorem tailTrace_1967065 : CollatzResearch.WordTrace tailWord_1967065 prefixEnd_1967065 1010049823636451582841139 := by
  unfold tailWord_1967065
  simp only [CollatzResearch.WordTrace]
  refine ⟨71744754618666927800926649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47829836412444618533951099 71744754618666927800926649)
  ·
    refine ⟨53808565964000195850694987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71744754618666927800926649 53808565964000195850694987)
    ·
      refine ⟨80712848946000293776042481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53808565964000195850694987 80712848946000293776042481)
      ·
        refine ⟨60534636709500220332031861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80712848946000293776042481 60534636709500220332031861)
        ·
          refine ⟨5675122191515645656127987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60534636709500220332031861 5675122191515645656127987)
          ·
            refine ⟨8512683287273468484191981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5675122191515645656127987 8512683287273468484191981)
            ·
              refine ⟨3192256232727550681571993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8512683287273468484191981 3192256232727550681571993)
              ·
                refine ⟨2394192174545663011178995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3192256232727550681571993 2394192174545663011178995)
                ·
                  refine ⟨3591288261818494516768493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2394192174545663011178995 3591288261818494516768493)
                  ·
                    refine ⟨1346733098181935443788185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3591288261818494516768493 1346733098181935443788185)
                    ·
                      refine ⟨1010049823636451582841139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1346733098181935443788185 1010049823636451582841139)
                      ·
                        rfl

theorem cell23_1967065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 3, 2].length) (baseStart_1967065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967065 prefixEnd_1967065 := by exact prefixLift 1967065
  have htrace : WordTrace (prefixWord ++ tailWord_1967065) baseStart_1967065 baseEnd_1967065 := by
    simpa [prefixWord, tailWord_1967065, baseEnd_1967065] using wordTrace_append hprefix tailTrace_1967065
  have hstable : (prefixWord ++ tailWord_1967065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967065).length < 2 ^ (prefixWord ++ tailWord_1967065).sum := by decide
  have hdescent : baseEnd_1967065 < baseStart_1967065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967082 : List Nat := [3, 1, 3, 1, 2, 3, 3, 1, 1, 3, 2]
def baseStart_1967082 : Nat := 118140960795 + 1967082 * 2 ^ 59
def prefixEnd_1967082 : Nat := 4983230072969 + 3 ^ 40 * 1967082 * 2
def baseEnd_1967082 : Nat := 1010058552807578016328561

theorem tailTrace_1967082 : CollatzResearch.WordTrace tailWord_1967082 prefixEnd_1967082 1010058552807578016328561 := by
  unfold tailWord_1967082
  simp only [CollatzResearch.WordTrace]
  refine ⟨17936343664901334926073875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47830249773070226469530333 17936343664901334926073875)
  ·
    refine ⟨26904515497352002389110813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17936343664901334926073875 26904515497352002389110813)
    ·
      refine ⟨10089193311507000895916555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26904515497352002389110813 10089193311507000895916555)
      ·
        refine ⟨15133789967260501343874833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10089193311507000895916555 15133789967260501343874833)
        ·
          refine ⟨11350342475445376007906125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15133789967260501343874833 11350342475445376007906125)
          ·
            refine ⟨4256378428292016002964797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11350342475445376007906125 4256378428292016002964797)
            ·
              refine ⟨1596141910609506001111799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4256378428292016002964797 1596141910609506001111799)
              ·
                refine ⟨2394212865914259001667699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1596141910609506001111799 2394212865914259001667699)
                ·
                  refine ⟨3591319298871388502501549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2394212865914259001667699 3591319298871388502501549)
                  ·
                    refine ⟨1346744737076770688438081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3591319298871388502501549 1346744737076770688438081)
                    ·
                      refine ⟨1010058552807578016328561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1346744737076770688438081 1010058552807578016328561)
                      ·
                        rfl

theorem cell23_1967082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_1967082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967082 prefixEnd_1967082 := by exact prefixLift 1967082
  have htrace : WordTrace (prefixWord ++ tailWord_1967082) baseStart_1967082 baseEnd_1967082 := by
    simpa [prefixWord, tailWord_1967082, baseEnd_1967082] using wordTrace_append hprefix tailTrace_1967082
  have hstable : (prefixWord ++ tailWord_1967082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967082).length < 2 ^ (prefixWord ++ tailWord_1967082).sum := by decide
  have hdescent : baseEnd_1967082 < baseStart_1967082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967146 : List Nat := [3, 1, 4, 1, 4, 1, 1, 2, 2, 2, 2]
def baseStart_1967146 : Nat := 118140960795 + 1967146 * 2 ^ 59
def prefixEnd_1967146 : Nat := 4983230072969 + 3 ^ 40 * 1967146 * 2
def baseEnd_1967146 : Nat := 1010091415569465765928267

theorem tailTrace_1967146 : CollatzResearch.WordTrace tailWord_1967146 prefixEnd_1967146 1010091415569465765928267 := by
  unfold tailWord_1967146
  simp only [CollatzResearch.WordTrace]
  refine ⟨17936927232843369658656323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47831805954248985756416861 17936927232843369658656323)
  ·
    refine ⟨26905390849265054487984485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17936927232843369658656323 26905390849265054487984485)
    ·
      refine ⟨5044760784237197716497091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26905390849265054487984485 5044760784237197716497091)
      ·
        refine ⟨7567141176355796574745637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5044760784237197716497091 7567141176355796574745637)
        ·
          refine ⟨1418838970566711857764807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7567141176355796574745637 1418838970566711857764807)
          ·
            refine ⟨2128258455850067786647211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1418838970566711857764807 2128258455850067786647211)
            ·
              refine ⟨3192387683775101679970817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2128258455850067786647211 3192387683775101679970817)
              ·
                refine ⟨2394290762831326259978113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3192387683775101679970817 2394290762831326259978113)
                ·
                  refine ⟨1795718072123494694983585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2394290762831326259978113 1795718072123494694983585)
                  ·
                    refine ⟨1346788554092621021237689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1795718072123494694983585 1346788554092621021237689)
                    ·
                      refine ⟨1010091415569465765928267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1346788554092621021237689 1010091415569465765928267)
                      ·
                        rfl

theorem cell23_1967146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_1967146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967146 prefixEnd_1967146 := by exact prefixLift 1967146
  have htrace : WordTrace (prefixWord ++ tailWord_1967146) baseStart_1967146 baseEnd_1967146 := by
    simpa [prefixWord, tailWord_1967146, baseEnd_1967146] using wordTrace_append hprefix tailTrace_1967146
  have hstable : (prefixWord ++ tailWord_1967146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967146).length < 2 ^ (prefixWord ++ tailWord_1967146).sum := by decide
  have hdescent : baseEnd_1967146 < baseStart_1967146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967168 : List Nat := [2, 1, 1, 2, 2, 3, 1, 3, 2, 4, 2]
def baseStart_1967168 : Nat := 118140960795 + 1967168 * 2 ^ 59
def prefixEnd_1967168 : Nat := 4983230072969 + 3 ^ 40 * 1967168 * 2
def baseEnd_1967168 : Nat := 1010102712143864679853165

theorem tailTrace_1967168 : CollatzResearch.WordTrace tailWord_1967168 prefixEnd_1967168 1010102712143864679853165 := by
  unfold tailWord_1967168
  simp only [CollatzResearch.WordTrace]
  refine ⟨35874255668646888195963079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47832340891529184261284105 35874255668646888195963079)
  ·
    refine ⟨53811383502970332293944619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35874255668646888195963079 53811383502970332293944619)
    ·
      refine ⟨80717075254455498440916929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53811383502970332293944619 80717075254455498440916929)
      ·
        refine ⟨60537806440841623830687697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80717075254455498440916929 60537806440841623830687697)
        ·
          refine ⟨45403354830631217873015773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60537806440841623830687697 45403354830631217873015773)
          ·
            refine ⟨17026258061486706702380915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45403354830631217873015773 17026258061486706702380915)
            ·
              refine ⟨25539387092230060053571373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17026258061486706702380915 25539387092230060053571373)
              ·
                refine ⟨9577270159586272520089265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25539387092230060053571373 9577270159586272520089265)
                ·
                  refine ⟨7182952619689704390066949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9577270159586272520089265 7182952619689704390066949)
                  ·
                    refine ⟨1346803616191819573137553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7182952619689704390066949 1346803616191819573137553)
                    ·
                      refine ⟨1010102712143864679853165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1346803616191819573137553 1010102712143864679853165)
                      ·
                        rfl

theorem cell23_1967168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 2, 4, 2].length) (baseStart_1967168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967168 prefixEnd_1967168 := by exact prefixLift 1967168
  have htrace : WordTrace (prefixWord ++ tailWord_1967168) baseStart_1967168 baseEnd_1967168 := by
    simpa [prefixWord, tailWord_1967168, baseEnd_1967168] using wordTrace_append hprefix tailTrace_1967168
  have hstable : (prefixWord ++ tailWord_1967168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967168).length < 2 ^ (prefixWord ++ tailWord_1967168).sum := by decide
  have hdescent : baseEnd_1967168 < baseStart_1967168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967171 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 3, 4, 3]
def baseStart_1967171 : Nat := 118140960795 + 1967171 * 2 ^ 59
def prefixEnd_1967171 : Nat := 4983230072969 + 3 ^ 40 * 1967171 * 2
def baseEnd_1967171 : Nat := 1010104252585828168115651

theorem tailTrace_1967171 : CollatzResearch.WordTrace tailWord_1967171 prefixEnd_1967171 1010104252585828168115651 := by
  unfold tailWord_1967171
  simp only [CollatzResearch.WordTrace]
  refine ⟨71748620756282907904285367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47832413837521938602856911 71748620756282907904285367)
  ·
    refine ⟨107622931134424361856428051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71748620756282907904285367 107622931134424361856428051)
    ·
      refine ⟨161434396701636542784642077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107622931134424361856428051 161434396701636542784642077)
      ·
        refine ⟨60537898763113703544240779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161434396701636542784642077 60537898763113703544240779)
        ·
          refine ⟨90806848144670555316361169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60537898763113703544240779 90806848144670555316361169)
          ·
            refine ⟨68105136108502916487270877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90806848144670555316361169 68105136108502916487270877)
            ·
              refine ⟨25539426040688593682726579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68105136108502916487270877 25539426040688593682726579)
              ·
                refine ⟨38309139061032890524089869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25539426040688593682726579 38309139061032890524089869)
                ·
                  refine ⟨14365927147887333946533701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38309139061032890524089869 14365927147887333946533701)
                  ·
                    refine ⟨2693611340228875114975069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14365927147887333946533701 2693611340228875114975069)
                    ·
                      refine ⟨1010104252585828168115651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2693611340228875114975069 1010104252585828168115651)
                      ·
                        rfl

theorem cell23_1967171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 4, 3].length) (baseStart_1967171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967171 prefixEnd_1967171 := by exact prefixLift 1967171
  have htrace : WordTrace (prefixWord ++ tailWord_1967171) baseStart_1967171 baseEnd_1967171 := by
    simpa [prefixWord, tailWord_1967171, baseEnd_1967171] using wordTrace_append hprefix tailTrace_1967171
  have hstable : (prefixWord ++ tailWord_1967171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967171).length < 2 ^ (prefixWord ++ tailWord_1967171).sum := by decide
  have hdescent : baseEnd_1967171 < baseStart_1967171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967178 : List Nat := [3, 1, 2, 1, 1, 2, 4, 2, 3, 4]
def baseStart_1967178 : Nat := 118140960795 + 1967178 * 2 ^ 59
def prefixEnd_1967178 : Nat := 4983230072969 + 3 ^ 40 * 1967178 * 2
def baseEnd_1967178 : Nat := 336702615650136546909373

theorem tailTrace_1967178 : CollatzResearch.WordTrace tailWord_1967178 prefixEnd_1967178 336702615650136546909373 := by
  unfold tailWord_1967178
  simp only [CollatzResearch.WordTrace]
  refine ⟨17937219016814387024947547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47832584044838365399860125 17937219016814387024947547)
  ·
    refine ⟨26905828525221580537421321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17937219016814387024947547 26905828525221580537421321)
    ·
      refine ⟨20179371393916185403065991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26905828525221580537421321 20179371393916185403065991)
      ·
        refine ⟨30269057090874278104598987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20179371393916185403065991 30269057090874278104598987)
        ·
          refine ⟨45403585636311417156898481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30269057090874278104598987 45403585636311417156898481)
          ·
            refine ⟨34052689227233562867673861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45403585636311417156898481 34052689227233562867673861)
            ·
              refine ⟨6384879230106293037688849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34052689227233562867673861 6384879230106293037688849)
              ·
                refine ⟨4788659422579719778266637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6384879230106293037688849 4788659422579719778266637)
                ·
                  refine ⟨1795747283467394916849989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4788659422579719778266637 1795747283467394916849989)
                  ·
                    refine ⟨336702615650136546909373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1795747283467394916849989 336702615650136546909373)
                    ·
                      rfl

theorem cell23_1967178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_1967178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967178 prefixEnd_1967178 := by exact prefixLift 1967178
  have htrace : WordTrace (prefixWord ++ tailWord_1967178) baseStart_1967178 baseEnd_1967178 := by
    simpa [prefixWord, tailWord_1967178, baseEnd_1967178] using wordTrace_append hprefix tailTrace_1967178
  have hstable : (prefixWord ++ tailWord_1967178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967178).length < 2 ^ (prefixWord ++ tailWord_1967178).sum := by decide
  have hdescent : baseEnd_1967178 < baseStart_1967178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967188 : List Nat := [2, 4, 1, 1, 1, 1, 4, 1, 1, 4, 3]
def baseStart_1967188 : Nat := 118140960795 + 1967188 * 2 ^ 59
def prefixEnd_1967188 : Nat := 4983230072969 + 3 ^ 40 * 1967188 * 2
def baseEnd_1967188 : Nat := 1010112981756954601603073

theorem tailTrace_1967188 : CollatzResearch.WordTrace tailWord_1967188 prefixEnd_1967188 1010112981756954601603073 := by
  unfold tailWord_1967188
  simp only [CollatzResearch.WordTrace]
  refine ⟨35874620398610659903827109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47832827198147546538436145 35874620398610659903827109)
  ·
    refine ⟨6726491324739498731967583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35874620398610659903827109 6726491324739498731967583)
    ·
      refine ⟨10089736987109248097951375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6726491324739498731967583 10089736987109248097951375)
      ·
        refine ⟨15134605480663872146927063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10089736987109248097951375 15134605480663872146927063)
        ·
          refine ⟨22701908220995808220390595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15134605480663872146927063 22701908220995808220390595)
          ·
            refine ⟨34052862331493712330585893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22701908220995808220390595 34052862331493712330585893)
            ·
              refine ⟨6384911687155071061984855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34052862331493712330585893 6384911687155071061984855)
              ·
                refine ⟨9577367530732606592977283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6384911687155071061984855 9577367530732606592977283)
                ·
                  refine ⟨14366051296098909889465925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9577367530732606592977283 14366051296098909889465925)
                  ·
                    refine ⟨2693634618018545604274861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14366051296098909889465925 2693634618018545604274861)
                    ·
                      refine ⟨1010112981756954601603073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2693634618018545604274861 1010112981756954601603073)
                      ·
                        rfl

theorem cell23_1967188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_1967188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967188 prefixEnd_1967188 := by exact prefixLift 1967188
  have htrace : WordTrace (prefixWord ++ tailWord_1967188) baseStart_1967188 baseEnd_1967188 := by
    simpa [prefixWord, tailWord_1967188, baseEnd_1967188] using wordTrace_append hprefix tailTrace_1967188
  have hstable : (prefixWord ++ tailWord_1967188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967188).length < 2 ^ (prefixWord ++ tailWord_1967188).sum := by decide
  have hdescent : baseEnd_1967188 < baseStart_1967188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967212 : List Nat := [2, 2, 1, 1, 3, 2, 5, 2, 1, 4]
def baseStart_1967212 : Nat := 118140960795 + 1967212 * 2 ^ 59
def prefixEnd_1967212 : Nat := 4983230072969 + 3 ^ 40 * 1967212 * 2
def baseEnd_1967212 : Nat := 336708435097554169234321

theorem tailTrace_1967212 : CollatzResearch.WordTrace tailWord_1967212 prefixEnd_1967212 336708435097554169234321 := by
  unfold tailWord_1967212
  simp only [CollatzResearch.WordTrace]
  refine ⟨35875058074567185953263945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47833410766089581271018593 35875058074567185953263945)
  ·
    refine ⟨26906293555925389464947959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35875058074567185953263945 26906293555925389464947959)
    ·
      refine ⟨40359440333888084197421939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26906293555925389464947959 40359440333888084197421939)
      ·
        refine ⟨60539160500832126296132909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40359440333888084197421939 60539160500832126296132909)
        ·
          refine ⟨22702185187812047361049841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60539160500832126296132909 22702185187812047361049841)
          ·
            refine ⟨17026638890859035520787381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22702185187812047361049841 17026638890859035520787381)
            ·
              refine ⟨1596247396018034580073817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17026638890859035520787381 1596247396018034580073817)
              ·
                refine ⟨1197185547013525935055363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1596247396018034580073817 1197185547013525935055363)
                ·
                  refine ⟨1795778320520288902583045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1197185547013525935055363 1795778320520288902583045)
                  ·
                    refine ⟨336708435097554169234321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1795778320520288902583045 336708435097554169234321)
                    ·
                      rfl

theorem cell23_1967212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2, 1, 4].length) (baseStart_1967212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967212 prefixEnd_1967212 := by exact prefixLift 1967212
  have htrace : WordTrace (prefixWord ++ tailWord_1967212) baseStart_1967212 baseEnd_1967212 := by
    simpa [prefixWord, tailWord_1967212, baseEnd_1967212] using wordTrace_append hprefix tailTrace_1967212
  have hstable : (prefixWord ++ tailWord_1967212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967212).length < 2 ^ (prefixWord ++ tailWord_1967212).sum := by decide
  have hdescent : baseEnd_1967212 < baseStart_1967212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967251 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 3, 6]
def baseStart_1967251 : Nat := 118140960795 + 1967251 * 2 ^ 59
def prefixEnd_1967251 : Nat := 4983230072969 + 3 ^ 40 * 1967251 * 2
def baseEnd_1967251 : Nat := 336715110346062618371761

theorem tailTrace_1967251 : CollatzResearch.WordTrace tailWord_1967251 prefixEnd_1967251 336715110346062618371761 := by
  unfold tailWord_1967251
  simp only [CollatzResearch.WordTrace]
  refine ⟨71751538595993081567197607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47834359063995387711465071 71751538595993081567197607)
  ·
    refine ⟨107627307893989622350796411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71751538595993081567197607 107627307893989622350796411)
    ·
      refine ⟨161440961840984433526194617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107627307893989622350796411 161440961840984433526194617)
      ·
        refine ⟨121080721380738325144645963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161440961840984433526194617 121080721380738325144645963)
        ·
          refine ⟨181621082071107487716968945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121080721380738325144645963 181621082071107487716968945)
          ·
            refine ⟨136215811553330615787726709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181621082071107487716968945 136215811553330615787726709)
            ·
              refine ⟨12770232333124745230099379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136215811553330615787726709 12770232333124745230099379)
              ·
                refine ⟨19155348499687117845149069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12770232333124745230099379 19155348499687117845149069)
                ·
                  refine ⟨7183255687382669191930901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19155348499687117845149069 7183255687382669191930901)
                  ·
                    refine ⟨336715110346062618371761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7183255687382669191930901 336715110346062618371761)
                    ·
                      rfl

theorem cell23_1967251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 6].length) (baseStart_1967251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967251 prefixEnd_1967251 := by exact prefixLift 1967251
  have htrace : WordTrace (prefixWord ++ tailWord_1967251) baseStart_1967251 baseEnd_1967251 := by
    simpa [prefixWord, tailWord_1967251, baseEnd_1967251] using wordTrace_append hprefix tailTrace_1967251
  have hstable : (prefixWord ++ tailWord_1967251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967251).length < 2 ^ (prefixWord ++ tailWord_1967251).sum := by decide
  have hdescent : baseEnd_1967251 < baseStart_1967251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967269 : List Nat := [1, 3, 1, 2, 1, 4, 4, 2, 1, 1, 3]
def baseStart_1967269 : Nat := 118140960795 + 1967269 * 2 ^ 59
def prefixEnd_1967269 : Nat := 4983230072969 + 3 ^ 40 * 1967269 * 2
def baseEnd_1967269 : Nat := 1010154573689968784690201

theorem tailTrace_1967269 : CollatzResearch.WordTrace tailWord_1967269 prefixEnd_1967269 1010154573689968784690201 := by
  unfold tailWord_1967269
  simp only [CollatzResearch.WordTrace]
  refine ⟨71752195109927870641352861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47834796739951913760901907 71752195109927870641352861)
  ·
    refine ⟨26907073166222951490507323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71752195109927870641352861 26907073166222951490507323)
    ·
      refine ⟨40360609749334427235760985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26907073166222951490507323 40360609749334427235760985)
      ·
        refine ⟨30270457312000820426820739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40360609749334427235760985 30270457312000820426820739)
        ·
          refine ⟨45405685968001230640231109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30270457312000820426820739 45405685968001230640231109)
          ·
            refine ⟨8513566119000230745043333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45405685968001230640231109 8513566119000230745043333)
            ·
              refine ⟨1596293647312543264695625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8513566119000230745043333 1596293647312543264695625)
              ·
                refine ⟨1197220235484407448521719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1596293647312543264695625 1197220235484407448521719)
                ·
                  refine ⟨1795830353226611172782579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1197220235484407448521719 1795830353226611172782579)
                  ·
                    refine ⟨2693745529839916759173869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1795830353226611172782579 2693745529839916759173869)
                    ·
                      refine ⟨1010154573689968784690201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2693745529839916759173869 1010154573689968784690201)
                      ·
                        rfl

theorem cell23_1967269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 2, 1, 1, 3].length) (baseStart_1967269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967269 prefixEnd_1967269 := by exact prefixLift 1967269
  have htrace : WordTrace (prefixWord ++ tailWord_1967269) baseStart_1967269 baseEnd_1967269 := by
    simpa [prefixWord, tailWord_1967269, baseEnd_1967269] using wordTrace_append hprefix tailTrace_1967269
  have hstable : (prefixWord ++ tailWord_1967269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967269).length < 2 ^ (prefixWord ++ tailWord_1967269).sum := by decide
  have hdescent : baseEnd_1967269 < baseStart_1967269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967286 : List Nat := [5, 1, 3, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_1967286 : Nat := 118140960795 + 1967286 * 2 ^ 59
def prefixEnd_1967286 : Nat := 4983230072969 + 3 ^ 40 * 1967286 * 2
def baseEnd_1967286 : Nat := 1010163302861095218177623

theorem tailTrace_1967286 : CollatzResearch.WordTrace tailWord_1967286 prefixEnd_1967286 1010163302861095218177623 := by
  unfold tailWord_1967286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4484550946929142659045107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47835210100577521696481141 4484550946929142659045107)
  ·
    refine ⟨6726826420393713988567661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4484550946929142659045107 6726826420393713988567661)
    ·
      refine ⟨2522559907647642745712873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6726826420393713988567661 2522559907647642745712873)
      ·
        refine ⟨1891919930735732059284655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2522559907647642745712873 1891919930735732059284655)
        ·
          refine ⟨2837879896103598088926983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1891919930735732059284655 2837879896103598088926983)
          ·
            refine ⟨4256819844155397133390475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2837879896103598088926983 4256819844155397133390475)
            ·
              refine ⟨6385229766233095700085713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4256819844155397133390475 6385229766233095700085713)
              ·
                refine ⟨4788922324674821775064285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6385229766233095700085713 4788922324674821775064285)
                ·
                  refine ⟨1795845871753058165649107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4788922324674821775064285 1795845871753058165649107)
                  ·
                    refine ⟨2693768807629587248473661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1795845871753058165649107 2693768807629587248473661)
                    ·
                      refine ⟨1010163302861095218177623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2693768807629587248473661 1010163302861095218177623)
                      ·
                        rfl

theorem cell23_1967286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_1967286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967286 prefixEnd_1967286 := by exact prefixLift 1967286
  have htrace : WordTrace (prefixWord ++ tailWord_1967286) baseStart_1967286 baseEnd_1967286 := by
    simpa [prefixWord, tailWord_1967286, baseEnd_1967286] using wordTrace_append hprefix tailTrace_1967286
  have hstable : (prefixWord ++ tailWord_1967286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967286).length < 2 ^ (prefixWord ++ tailWord_1967286).sum := by decide
  have hdescent : baseEnd_1967286 < baseStart_1967286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967292 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 5, 2, 2]
def baseStart_1967292 : Nat := 118140960795 + 1967292 * 2 ^ 59
def prefixEnd_1967292 : Nat := 4983230072969 + 3 ^ 40 * 1967292 * 2
def baseEnd_1967292 : Nat := 1010166383745022194702595

theorem tailTrace_1967292 : CollatzResearch.WordTrace tailWord_1967292 prefixEnd_1967292 1010166383745022194702595 := by
  unfold tailWord_1967292
  simp only [CollatzResearch.WordTrace]
  refine ⟨35876516994422272784720065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47835355992563030379626753 35876516994422272784720065)
  ·
    refine ⟨26907387745816704588540049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35876516994422272784720065 26907387745816704588540049)
    ·
      refine ⟨20180540809362528441405037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26907387745816704588540049 20180540809362528441405037)
      ·
        refine ⟨7567702803510948165526889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20180540809362528441405037 7567702803510948165526889)
        ·
          refine ⟨5675777102633211124145167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7567702803510948165526889 5675777102633211124145167)
          ·
            refine ⟨8513665653949816686217751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5675777102633211124145167 8513665653949816686217751)
            ·
              refine ⟨12770498480924725029326627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8513665653949816686217751 12770498480924725029326627)
              ·
                refine ⟨19155747721387087543989941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12770498480924725029326627 19155747721387087543989941)
                ·
                  refine ⟨1795851348880039457249057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19155747721387087543989941 1795851348880039457249057)
                  ·
                    refine ⟨1346888511660029592936793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1795851348880039457249057 1346888511660029592936793)
                    ·
                      refine ⟨1010166383745022194702595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1346888511660029592936793 1010166383745022194702595)
                      ·
                        rfl

theorem cell23_1967292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_1967292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967292 prefixEnd_1967292 := by exact prefixLift 1967292
  have htrace : WordTrace (prefixWord ++ tailWord_1967292) baseStart_1967292 baseEnd_1967292 := by
    simpa [prefixWord, tailWord_1967292, baseEnd_1967292] using wordTrace_append hprefix tailTrace_1967292
  have hstable : (prefixWord ++ tailWord_1967292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967292).length < 2 ^ (prefixWord ++ tailWord_1967292).sum := by decide
  have hdescent : baseEnd_1967292 < baseStart_1967292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967311 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 1, 9]
def baseStart_1967311 : Nat := 118140960795 + 1967311 * 2 ^ 59
def prefixEnd_1967311 : Nat := 4983230072969 + 3 ^ 40 * 1967311 * 2
def baseEnd_1967311 : Nat := 336725379959152540121669

theorem tailTrace_1967311 : CollatzResearch.WordTrace tailWord_1967311 prefixEnd_1967311 336725379959152540121669 := by
  unfold tailWord_1967311
  simp only [CollatzResearch.WordTrace]
  refine ⟨71753726975775711814381787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47835817983850474542921191 71753726975775711814381787)
  ·
    refine ⟨107630590463663567721572681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71753726975775711814381787 107630590463663567721572681)
    ·
      refine ⟨80722942847747675791179511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107630590463663567721572681 80722942847747675791179511)
      ·
        refine ⟨121084414271621513686769267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80722942847747675791179511 121084414271621513686769267)
        ·
          refine ⟨181626621407432270530153901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121084414271621513686769267 181626621407432270530153901)
          ·
            refine ⟨68109983027787101448807713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181626621407432270530153901 68109983027787101448807713)
            ·
              refine ⟨51082487270840326086605785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68109983027787101448807713 51082487270840326086605785)
              ·
                refine ⟨38311865453130244564954339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51082487270840326086605785 38311865453130244564954339)
                ·
                  refine ⟨57467798179695366847431509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38311865453130244564954339 57467798179695366847431509)
                  ·
                    refine ⟨336725379959152540121669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 57467798179695366847431509 336725379959152540121669)
                    ·
                      rfl

theorem cell23_1967311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 9].length) (baseStart_1967311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967311 prefixEnd_1967311 := by exact prefixLift 1967311
  have htrace : WordTrace (prefixWord ++ tailWord_1967311) baseStart_1967311 baseEnd_1967311 := by
    simpa [prefixWord, tailWord_1967311, baseEnd_1967311] using wordTrace_append hprefix tailTrace_1967311
  have hstable : (prefixWord ++ tailWord_1967311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967311).length < 2 ^ (prefixWord ++ tailWord_1967311).sum := by decide
  have hdescent : baseEnd_1967311 < baseStart_1967311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967342 : List Nat := [4, 1, 2, 1, 1, 1, 2, 5, 2, 1, 3]
def baseStart_1967342 : Nat := 118140960795 + 1967342 * 2 ^ 59
def prefixEnd_1967342 : Nat := 4983230072969 + 3 ^ 40 * 1967342 * 2
def baseEnd_1967342 : Nat := 1010192057777746999077365

theorem tailTrace_1967342 : CollatzResearch.WordTrace tailWord_1967342 prefixEnd_1967342 1010192057777746999077365 := by
  unfold tailWord_1967342
  simp only [CollatzResearch.WordTrace]
  refine ⟨8969357204832925513595035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47836571759108936072506853 8969357204832925513595035)
  ·
    refine ⟨13454035807249388270392553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8969357204832925513595035 13454035807249388270392553)
    ·
      refine ⟨10090526855437041202794415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13454035807249388270392553 10090526855437041202794415)
      ·
        refine ⟨15135790283155561804191623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10090526855437041202794415 15135790283155561804191623)
        ·
          refine ⟨22703685424733342706287435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15135790283155561804191623 22703685424733342706287435)
          ·
            refine ⟨34055528137100014059431153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22703685424733342706287435 34055528137100014059431153)
            ·
              refine ⟨25541646102825010544573365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34055528137100014059431153 25541646102825010544573365)
              ·
                refine ⟨2394529322139844738553753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25541646102825010544573365 2394529322139844738553753)
                ·
                  refine ⟨1795896991604883553915315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2394529322139844738553753 1795896991604883553915315)
                  ·
                    refine ⟨2693845487407325330872973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1795896991604883553915315 2693845487407325330872973)
                    ·
                      refine ⟨1010192057777746999077365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2693845487407325330872973 1010192057777746999077365)
                      ·
                        rfl

theorem cell23_1967342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_1967342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967342 prefixEnd_1967342 := by exact prefixLift 1967342
  have htrace : WordTrace (prefixWord ++ tailWord_1967342) baseStart_1967342 baseEnd_1967342 := by
    simpa [prefixWord, tailWord_1967342, baseEnd_1967342] using wordTrace_append hprefix tailTrace_1967342
  have hstable : (prefixWord ++ tailWord_1967342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967342).length < 2 ^ (prefixWord ++ tailWord_1967342).sum := by decide
  have hdescent : baseEnd_1967342 < baseStart_1967342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967365 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 3, 4, 2]
def baseStart_1967365 : Nat := 118140960795 + 1967365 * 2 ^ 59
def prefixEnd_1967365 : Nat := 4983230072969 + 3 ^ 40 * 1967365 * 2
def baseEnd_1967365 : Nat := 1010203867832800409089759

theorem tailTrace_1967365 : CollatzResearch.WordTrace tailWord_1967365 prefixEnd_1967365 1010203867832800409089759 := by
  unfold tailWord_1967365
  simp only [CollatzResearch.WordTrace]
  refine ⟨71755696517580079036847549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47837131011720052691231699 71755696517580079036847549)
  ·
    refine ⟨26908386194092529638817831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71755696517580079036847549 26908386194092529638817831)
    ·
      refine ⟨40362579291138794458226747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26908386194092529638817831 40362579291138794458226747)
      ·
        refine ⟨60543868936708191687340121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40362579291138794458226747 60543868936708191687340121)
        ·
          refine ⟨45407901702531143765505091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60543868936708191687340121 45407901702531143765505091)
          ·
            refine ⟨68111852553796715648257637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45407901702531143765505091 68111852553796715648257637)
            ·
              refine ⟨12770972353836884184048307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68111852553796715648257637 12770972353836884184048307)
              ·
                refine ⟨19156458530755326276072461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12770972353836884184048307 19156458530755326276072461)
                ·
                  refine ⟨7183671949033247353527173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19156458530755326276072461 7183671949033247353527173)
                  ·
                    refine ⟨1346938490443733878786345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7183671949033247353527173 1346938490443733878786345)
                    ·
                      refine ⟨1010203867832800409089759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1346938490443733878786345 1010203867832800409089759)
                      ·
                        rfl

theorem cell23_1967365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 4, 2].length) (baseStart_1967365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967365 prefixEnd_1967365 := by exact prefixLift 1967365
  have htrace : WordTrace (prefixWord ++ tailWord_1967365) baseStart_1967365 baseEnd_1967365 := by
    simpa [prefixWord, tailWord_1967365, baseEnd_1967365] using wordTrace_append hprefix tailTrace_1967365
  have hstable : (prefixWord ++ tailWord_1967365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967365).length < 2 ^ (prefixWord ++ tailWord_1967365).sum := by decide
  have hdescent : baseEnd_1967365 < baseStart_1967365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967422 : List Nat := [4, 2, 1, 2, 1, 1, 2, 5, 5]
def baseStart_1967422 : Nat := 118140960795 + 1967422 * 2 ^ 59
def prefixEnd_1967422 : Nat := 4983230072969 + 3 ^ 40 * 1967422 * 2
def baseEnd_1967422 : Nat := 112248126247789631786333

theorem tailTrace_1967422 : CollatzResearch.WordTrace tailWord_1967422 prefixEnd_1967422 112248126247789631786333 := by
  unfold tailWord_1967422
  simp only [CollatzResearch.WordTrace]
  refine ⟨8969721934796697221459065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47838516985582385181115013 8969721934796697221459065)
  ·
    refine ⟨6727291451097522916094299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8969721934796697221459065 6727291451097522916094299)
    ·
      refine ⟨10090937176646284374141449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6727291451097522916094299 10090937176646284374141449)
      ·
        refine ⟨7568202882484713280606087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10090937176646284374141449 7568202882484713280606087)
        ·
          refine ⟨11352304323727069920909131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7568202882484713280606087 11352304323727069920909131)
          ·
            refine ⟨17028456485590604881363697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11352304323727069920909131 17028456485590604881363697)
            ·
              refine ⟨12771342364192953661022773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17028456485590604881363697 12771342364192953661022773)
              ·
                refine ⟨1197313346643089405720885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12771342364192953661022773 1197313346643089405720885)
                ·
                  refine ⟨112248126247789631786333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1197313346643089405720885 112248126247789631786333)
                  ·
                    rfl

theorem cell23_1967422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_1967422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967422 prefixEnd_1967422 := by exact prefixLift 1967422
  have htrace : WordTrace (prefixWord ++ tailWord_1967422) baseStart_1967422 baseEnd_1967422 := by
    simpa [prefixWord, tailWord_1967422, baseEnd_1967422] using wordTrace_append hprefix tailTrace_1967422
  have hstable : (prefixWord ++ tailWord_1967422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967422).length < 2 ^ (prefixWord ++ tailWord_1967422).sum := by decide
  have hdescent : baseEnd_1967422 < baseStart_1967422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967445 : List Nat := [1, 3, 2, 2, 3, 1, 2, 1, 1, 2, 5]
def baseStart_1967445 : Nat := 118140960795 + 1967445 * 2 ^ 59
def prefixEnd_1967445 : Nat := 4983230072969 + 3 ^ 40 * 1967445 * 2
def baseEnd_1967445 : Nat := 1010244946285160096089391

theorem tailTrace_1967445 : CollatzResearch.WordTrace tailWord_1967445 prefixEnd_1967445 1010244946285160096089391 := by
  unfold tailWord_1967445
  simp only [CollatzResearch.WordTrace]
  refine ⟨71758614357290252699759789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47839076238193501799839859 71758614357290252699759789)
  ·
    refine ⟨26909480383983844762409921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71758614357290252699759789 26909480383983844762409921)
    ·
      refine ⟨20182110287987883571807441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26909480383983844762409921 20182110287987883571807441)
      ·
        refine ⟨15136582715990912678855581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20182110287987883571807441 15136582715990912678855581)
        ·
          refine ⟨5676218518496592254570843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15136582715990912678855581 5676218518496592254570843)
          ·
            refine ⟨8514327777744888381856265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5676218518496592254570843 8514327777744888381856265)
            ·
              refine ⟨6385745833308666286392199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8514327777744888381856265 6385745833308666286392199)
              ·
                refine ⟨9578618749962999429588299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6385745833308666286392199 9578618749962999429588299)
                ·
                  refine ⟨14367928124944499144382449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9578618749962999429588299 14367928124944499144382449)
                  ·
                    refine ⟨10775946093708374358286837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14367928124944499144382449 10775946093708374358286837)
                    ·
                      refine ⟨1010244946285160096089391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10775946093708374358286837 1010244946285160096089391)
                      ·
                        rfl

theorem cell23_1967445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_1967445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967445 prefixEnd_1967445 := by exact prefixLift 1967445
  have htrace : WordTrace (prefixWord ++ tailWord_1967445) baseStart_1967445 baseEnd_1967445 := by
    simpa [prefixWord, tailWord_1967445, baseEnd_1967445] using wordTrace_append hprefix tailTrace_1967445
  have hstable : (prefixWord ++ tailWord_1967445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967445).length < 2 ^ (prefixWord ++ tailWord_1967445).sum := by decide
  have hdescent : baseEnd_1967445 < baseStart_1967445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967495 : List Nat := [1, 1, 4, 2, 2, 3, 1, 1, 8]
def baseStart_1967495 : Nat := 118140960795 + 1967495 * 2 ^ 59
def prefixEnd_1967495 : Nat := 4983230072969 + 3 ^ 40 * 1967495 * 2
def baseEnd_1967495 : Nat := 112252291146431655607129

theorem tailTrace_1967495 : CollatzResearch.WordTrace tailWord_1967495 prefixEnd_1967495 112252291146431655607129 := by
  unfold tailWord_1967495
  simp only [CollatzResearch.WordTrace]
  refine ⟨71760438007109111239079939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47840292004739407492719959 71760438007109111239079939)
  ·
    refine ⟨107640657010663666858619909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71760438007109111239079939 107640657010663666858619909)
    ·
      refine ⟨20182623189499437535991233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107640657010663666858619909 20182623189499437535991233)
      ·
        refine ⟨15136967392124578151993425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20182623189499437535991233 15136967392124578151993425)
        ·
          refine ⟨11352725544093433613995069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15136967392124578151993425 11352725544093433613995069)
          ·
            refine ⟨4257272079035037605248151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11352725544093433613995069 4257272079035037605248151)
            ·
              refine ⟨6385908118552556407872227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4257272079035037605248151 6385908118552556407872227)
              ·
                refine ⟨9578862177828834611808341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6385908118552556407872227 9578862177828834611808341)
                ·
                  refine ⟨112252291146431655607129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9578862177828834611808341 112252291146431655607129)
                  ·
                    rfl

theorem cell23_1967495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 8].length) (baseStart_1967495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967495 prefixEnd_1967495 := by exact prefixLift 1967495
  have htrace : WordTrace (prefixWord ++ tailWord_1967495) baseStart_1967495 baseEnd_1967495 := by
    simpa [prefixWord, tailWord_1967495, baseEnd_1967495] using wordTrace_append hprefix tailTrace_1967495
  have hstable : (prefixWord ++ tailWord_1967495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967495).length < 2 ^ (prefixWord ++ tailWord_1967495).sum := by decide
  have hdescent : baseEnd_1967495 < baseStart_1967495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967532 : List Nat := [2, 2, 1, 1, 1, 1, 6, 1, 1, 5, 2]
def baseStart_1967532 : Nat := 118140960795 + 1967532 * 2 ^ 59
def prefixEnd_1967532 : Nat := 4983230072969 + 3 ^ 40 * 1967532 * 2
def baseEnd_1967532 : Nat := 1010289619102101255701491

theorem tailTrace_1967532 : CollatzResearch.WordTrace tailWord_1967532 prefixEnd_1967532 1010289619102101255701491 := by
  unfold tailWord_1967532
  simp only [CollatzResearch.WordTrace]
  refine ⟨35880893753987533279088425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47841191671983377705451233 35880893753987533279088425)
  ·
    refine ⟨26910670315490649959316319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35880893753987533279088425 26910670315490649959316319)
    ·
      refine ⟨40366005473235974938974479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26910670315490649959316319 40366005473235974938974479)
      ·
        refine ⟨60549008209853962408461719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40366005473235974938974479 60549008209853962408461719)
        ·
          refine ⟨90823512314780943612692579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60549008209853962408461719 90823512314780943612692579)
          ·
            refine ⟨136235268472171415419038869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90823512314780943612692579 136235268472171415419038869)
            ·
              refine ⟨6386028209633035097767447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 136235268472171415419038869 6386028209633035097767447)
              ·
                refine ⟨9579042314449552646651171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6386028209633035097767447 9579042314449552646651171)
                ·
                  refine ⟨14368563471674328969976757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9579042314449552646651171 14368563471674328969976757)
                  ·
                    refine ⟨1347052825469468340935321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14368563471674328969976757 1347052825469468340935321)
                    ·
                      refine ⟨1010289619102101255701491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1347052825469468340935321 1010289619102101255701491)
                      ·
                        rfl

theorem cell23_1967532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 5, 2].length) (baseStart_1967532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967532 prefixEnd_1967532 := by exact prefixLift 1967532
  have htrace : WordTrace (prefixWord ++ tailWord_1967532) baseStart_1967532 baseEnd_1967532 := by
    simpa [prefixWord, tailWord_1967532, baseEnd_1967532] using wordTrace_append hprefix tailTrace_1967532
  have hstable : (prefixWord ++ tailWord_1967532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967532).length < 2 ^ (prefixWord ++ tailWord_1967532).sum := by decide
  have hdescent : baseEnd_1967532 < baseStart_1967532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967533 : List Nat := [1, 5, 2, 2, 1, 3, 1, 3, 1, 4]
def baseStart_1967533 : Nat := 118140960795 + 1967533 * 2 ^ 59
def prefixEnd_1967533 : Nat := 4983230072969 + 3 ^ 40 * 1967533 * 2
def baseEnd_1967533 : Nat := 336763377527585250596329

theorem tailTrace_1967533 : CollatzResearch.WordTrace tailWord_1967533 prefixEnd_1967533 336763377527585250596329 := by
  unfold tailWord_1967533
  simp only [CollatzResearch.WordTrace]
  refine ⟨71761823980971443728963253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47841215987314295819308835 71761823980971443728963253)
  ·
    refine ⟨6727670998216072849590305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71761823980971443728963253 6727670998216072849590305)
    ·
      refine ⟨5045753248662054637192729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6727670998216072849590305 5045753248662054637192729)
      ·
        refine ⟨3784314936496540977894547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5045753248662054637192729 3784314936496540977894547)
        ·
          refine ⟨5676472404744811466841821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3784314936496540977894547 5676472404744811466841821)
          ·
            refine ⟨2128677151779304300065683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5676472404744811466841821 2128677151779304300065683)
            ·
              refine ⟨3193015727668956450098525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2128677151779304300065683 3193015727668956450098525)
              ·
                refine ⟨1197380897875858668786947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3193015727668956450098525 1197380897875858668786947)
                ·
                  refine ⟨1796071346813788003180421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1197380897875858668786947 1796071346813788003180421)
                  ·
                    refine ⟨336763377527585250596329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1796071346813788003180421 336763377527585250596329)
                    ·
                      rfl

theorem cell23_1967533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_1967533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967533 prefixEnd_1967533 := by exact prefixLift 1967533
  have htrace : WordTrace (prefixWord ++ tailWord_1967533) baseStart_1967533 baseEnd_1967533 := by
    simpa [prefixWord, tailWord_1967533, baseEnd_1967533] using wordTrace_append hprefix tailTrace_1967533
  have hstable : (prefixWord ++ tailWord_1967533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967533).length < 2 ^ (prefixWord ++ tailWord_1967533).sum := by decide
  have hdescent : baseEnd_1967533 < baseStart_1967533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967549 : List Nat := [1, 4, 1, 2, 2, 1, 3, 2, 2, 3, 2]
def baseStart_1967549 : Nat := 118140960795 + 1967549 * 2 ^ 59
def prefixEnd_1967549 : Nat := 4983230072969 + 3 ^ 40 * 1967549 * 2
def baseEnd_1967549 : Nat := 1010298348273227689188913

theorem tailTrace_1967549 : CollatzResearch.WordTrace tailWord_1967549 prefixEnd_1967549 1010298348273227689188913 := by
  unfold tailWord_1967549
  simp only [CollatzResearch.WordTrace]
  refine ⟨71762407548913478461545701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47841605032608985641030467 71762407548913478461545701)
  ·
    refine ⟨13455451415421277211539819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71762407548913478461545701 13455451415421277211539819)
    ·
      refine ⟨20183177123131915817309729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13455451415421277211539819 20183177123131915817309729)
      ·
        refine ⟨15137382842348936862982297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20183177123131915817309729 15137382842348936862982297)
        ·
          refine ⟨11353037131761702647236723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15137382842348936862982297 11353037131761702647236723)
          ·
            refine ⟨17029555697642553970855085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11353037131761702647236723 17029555697642553970855085)
            ·
              refine ⟨6386083386615957739070657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17029555697642553970855085 6386083386615957739070657)
              ·
                refine ⟨4789562539961968304302993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6386083386615957739070657 4789562539961968304302993)
                ·
                  refine ⟨3592171904971476228227245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4789562539961968304302993 3592171904971476228227245)
                  ·
                    refine ⟨1347064464364303585585217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3592171904971476228227245 1347064464364303585585217)
                    ·
                      refine ⟨1010298348273227689188913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1347064464364303585585217 1010298348273227689188913)
                      ·
                        rfl

theorem cell23_1967549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_1967549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967549 prefixEnd_1967549 := by exact prefixLift 1967549
  have htrace : WordTrace (prefixWord ++ tailWord_1967549) baseStart_1967549 baseEnd_1967549 := by
    simpa [prefixWord, tailWord_1967549, baseEnd_1967549] using wordTrace_append hprefix tailTrace_1967549
  have hstable : (prefixWord ++ tailWord_1967549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967549).length < 2 ^ (prefixWord ++ tailWord_1967549).sum := by decide
  have hdescent : baseEnd_1967549 < baseStart_1967549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967556 : List Nat := [2, 3, 3, 2, 1, 1, 3, 1, 3, 1, 3]
def baseStart_1967556 : Nat := 118140960795 + 1967556 * 2 ^ 59
def prefixEnd_1967556 : Nat := 4983230072969 + 3 ^ 40 * 1967556 * 2
def baseEnd_1967556 : Nat := 1010301942637809161801381

theorem tailTrace_1967556 : CollatzResearch.WordTrace tailWord_1967556 prefixEnd_1967556 1010301942637809161801381 := by
  unfold tailWord_1967556
  simp only [CollatzResearch.WordTrace]
  refine ⟨35881331429944059328525261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47841775239925412438033681 35881331429944059328525261)
  ·
    refine ⟨13455499286229022248196973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35881331429944059328525261 13455499286229022248196973)
    ·
      refine ⟨5045812232335883343073865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13455499286229022248196973 5045812232335883343073865)
      ·
        refine ⟨3784359174251912507305399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5045812232335883343073865 3784359174251912507305399)
        ·
          refine ⟨5676538761377868760958099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3784359174251912507305399 5676538761377868760958099)
          ·
            refine ⟨8514808142066803141437149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5676538761377868760958099 8514808142066803141437149)
            ·
              refine ⟨3193053053275051178038931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8514808142066803141437149 3193053053275051178038931)
              ·
                refine ⟨4789579579912576767058397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3193053053275051178038931 4789579579912576767058397)
                ·
                  refine ⟨1796092342467216287646899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4789579579912576767058397 1796092342467216287646899)
                  ·
                    refine ⟨2694138513700824431470349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1796092342467216287646899 2694138513700824431470349)
                    ·
                      refine ⟨1010301942637809161801381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2694138513700824431470349 1010301942637809161801381)
                      ·
                        rfl

theorem cell23_1967556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_1967556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967556 prefixEnd_1967556 := by exact prefixLift 1967556
  have htrace : WordTrace (prefixWord ++ tailWord_1967556) baseStart_1967556 baseEnd_1967556 := by
    simpa [prefixWord, tailWord_1967556, baseEnd_1967556] using wordTrace_append hprefix tailTrace_1967556
  have hstable : (prefixWord ++ tailWord_1967556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967556).length < 2 ^ (prefixWord ++ tailWord_1967556).sum := by decide
  have hdescent : baseEnd_1967556 < baseStart_1967556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967575 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 4]
def baseStart_1967575 : Nat := 118140960795 + 1967575 * 2 ^ 59
def prefixEnd_1967575 : Nat := 4983230072969 + 3 ^ 40 * 1967575 * 2
def baseEnd_1967575 : Nat := 1010311698770244587463793

theorem tailTrace_1967575 : CollatzResearch.WordTrace tailWord_1967575 prefixEnd_1967575 1010311698770244587463793 := by
  unfold tailWord_1967575
  simp only [CollatzResearch.WordTrace]
  refine ⟨71763355846819284901992179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47842237231212856601328119 71763355846819284901992179)
  ·
    refine ⟨107645033770228927352988269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71763355846819284901992179 107645033770228927352988269)
    ·
      refine ⟨40366887663835847757370601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107645033770228927352988269 40366887663835847757370601)
      ·
        refine ⟨30275165747876885818027951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40366887663835847757370601 30275165747876885818027951)
        ·
          refine ⟨45412748621815328727041927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30275165747876885818027951 45412748621815328727041927)
          ·
            refine ⟨68119122932722993090562891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45412748621815328727041927 68119122932722993090562891)
            ·
              refine ⟨102178684399084489635844337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68119122932722993090562891 102178684399084489635844337)
              ·
                refine ⟨76634013299313367226883253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102178684399084489635844337 76634013299313367226883253)
                ·
                  refine ⟨7184438746810628177520305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76634013299313367226883253 7184438746810628177520305)
                  ·
                    refine ⟨5388329060107971133140229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7184438746810628177520305 5388329060107971133140229)
                    ·
                      refine ⟨1010311698770244587463793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5388329060107971133140229 1010311698770244587463793)
                      ·
                        rfl

theorem cell23_1967575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_1967575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967575 prefixEnd_1967575 := by exact prefixLift 1967575
  have htrace : WordTrace (prefixWord ++ tailWord_1967575) baseStart_1967575 baseEnd_1967575 := by
    simpa [prefixWord, tailWord_1967575, baseEnd_1967575] using wordTrace_append hprefix tailTrace_1967575
  have hstable : (prefixWord ++ tailWord_1967575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967575).length < 2 ^ (prefixWord ++ tailWord_1967575).sum := by decide
  have hdescent : baseEnd_1967575 < baseStart_1967575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967585 : List Nat := [1, 2, 3, 1, 2, 3, 2, 9]
def baseStart_1967585 : Nat := 118140960795 + 1967585 * 2 ^ 59
def prefixEnd_1967585 : Nat := 4983230072969 + 3 ^ 40 * 1967585 * 2
def baseEnd_1967585 : Nat := 37419141984325538827361

theorem tailTrace_1967585 : CollatzResearch.WordTrace tailWord_1967585 prefixEnd_1967585 37419141984325538827361 := by
  unfold tailWord_1967585
  simp only [CollatzResearch.WordTrace]
  refine ⟨71763720576783056609856209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47842480384522037739904139 71763720576783056609856209)
  ·
    refine ⟨53822790432587292457392157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71763720576783056609856209 53822790432587292457392157)
    ·
      refine ⟨20183546412220234671522059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53822790432587292457392157 20183546412220234671522059)
      ·
        refine ⟨30275319618330352007283089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20183546412220234671522059 30275319618330352007283089)
        ·
          refine ⟨22706489713747764005462317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30275319618330352007283089 22706489713747764005462317)
          ·
            refine ⟨8514933642655411502048369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22706489713747764005462317 8514933642655411502048369)
            ·
              refine ⟨6386200231991558626536277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8514933642655411502048369 6386200231991558626536277)
              ·
                refine ⟨37419141984325538827361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6386200231991558626536277 37419141984325538827361)
                ·
                  rfl

theorem cell23_1967585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 9].length) (baseStart_1967585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967585 prefixEnd_1967585 := by exact prefixLift 1967585
  have htrace : WordTrace (prefixWord ++ tailWord_1967585) baseStart_1967585 baseEnd_1967585 := by
    simpa [prefixWord, tailWord_1967585, baseEnd_1967585] using wordTrace_append hprefix tailTrace_1967585
  have hstable : (prefixWord ++ tailWord_1967585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967585).length < 2 ^ (prefixWord ++ tailWord_1967585).sum := by decide
  have hdescent : baseEnd_1967585 < baseStart_1967585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967592 : List Nat := [2, 1, 4, 1, 1, 2, 3, 2, 1, 2, 4]
def baseStart_1967592 : Nat := 118140960795 + 1967592 * 2 ^ 59
def prefixEnd_1967592 : Nat := 4983230072969 + 3 ^ 40 * 1967592 * 2
def baseEnd_1967592 : Nat := 1010320427941371020951215

theorem tailTrace_1967592 : CollatzResearch.WordTrace tailWord_1967592 prefixEnd_1967592 1010320427941371020951215 := by
  unfold tailWord_1967592
  simp only [CollatzResearch.WordTrace]
  refine ⟨35881987943878848402680515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47842650591838464536907353 35881987943878848402680515)
  ·
    refine ⟨53822981915818272604020773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35881987943878848402680515 53822981915818272604020773)
    ·
      refine ⟨10091809109215926113253895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53822981915818272604020773 10091809109215926113253895)
      ·
        refine ⟨15137713663823889169880843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10091809109215926113253895 15137713663823889169880843)
        ·
          refine ⟨22706570495735833754821265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15137713663823889169880843 22706570495735833754821265)
          ·
            refine ⟨17029927871801875316115949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22706570495735833754821265 17029927871801875316115949)
            ·
              refine ⟨6386222951925703243543481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17029927871801875316115949 6386222951925703243543481)
              ·
                refine ⟨4789667213944277432657611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6386222951925703243543481 4789667213944277432657611)
                ·
                  refine ⟨7184500820916416148986417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4789667213944277432657611 7184500820916416148986417)
                  ·
                    refine ⟨5388375615687312111739813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7184500820916416148986417 5388375615687312111739813)
                    ·
                      refine ⟨1010320427941371020951215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5388375615687312111739813 1010320427941371020951215)
                      ·
                        rfl

theorem cell23_1967592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_1967592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967592 prefixEnd_1967592 := by exact prefixLift 1967592
  have htrace : WordTrace (prefixWord ++ tailWord_1967592) baseStart_1967592 baseEnd_1967592 := by
    simpa [prefixWord, tailWord_1967592, baseEnd_1967592] using wordTrace_append hprefix tailTrace_1967592
  have hstable : (prefixWord ++ tailWord_1967592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967592).length < 2 ^ (prefixWord ++ tailWord_1967592).sum := by decide
  have hdescent : baseEnd_1967592 < baseStart_1967592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967606 : List Nat := [5, 1, 1, 1, 2, 3, 2, 2, 2, 4]
def baseStart_1967606 : Nat := 118140960795 + 1967606 * 2 ^ 59
def prefixEnd_1967606 : Nat := 4983230072969 + 3 ^ 40 * 1967606 * 2
def baseEnd_1967606 : Nat := 336775872223511322058717

theorem tailTrace_1967606 : CollatzResearch.WordTrace tailWord_1967606 prefixEnd_1967606 336775872223511322058717 := by
  unfold tailWord_1967606
  simp only [CollatzResearch.WordTrace]
  refine ⟨4485280406856686074773167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47842991006471318130913781 4485280406856686074773167)
  ·
    refine ⟨6727920610285029112159751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4485280406856686074773167 6727920610285029112159751)
    ·
      refine ⟨10091880915427543668239627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6727920610285029112159751 10091880915427543668239627)
      ·
        refine ⟨15137821373141315502359441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10091880915427543668239627 15137821373141315502359441)
        ·
          refine ⟨11353366029855986626769581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15137821373141315502359441 11353366029855986626769581)
          ·
            refine ⟨4257512261195994985038593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11353366029855986626769581 4257512261195994985038593)
            ·
              refine ⟨3193134195896996238778945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4257512261195994985038593 3193134195896996238778945)
              ·
                refine ⟨2394850646922747179084209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3193134195896996238778945 2394850646922747179084209)
                ·
                  refine ⟨1796137985192060384313157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2394850646922747179084209 1796137985192060384313157)
                  ·
                    refine ⟨336775872223511322058717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1796137985192060384313157 336775872223511322058717)
                    ·
                      rfl

theorem cell23_1967606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_1967606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967606 prefixEnd_1967606 := by exact prefixLift 1967606
  have htrace : WordTrace (prefixWord ++ tailWord_1967606) baseStart_1967606 baseEnd_1967606 := by
    simpa [prefixWord, tailWord_1967606, baseEnd_1967606] using wordTrace_append hprefix tailTrace_1967606
  have hstable : (prefixWord ++ tailWord_1967606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967606).length < 2 ^ (prefixWord ++ tailWord_1967606).sum := by decide
  have hdescent : baseEnd_1967606 < baseStart_1967606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967613 : List Nat := [1, 4, 1, 1, 1, 5, 1, 4, 1, 2, 2]
def baseStart_1967613 : Nat := 118140960795 + 1967613 * 2 ^ 59
def prefixEnd_1967613 : Nat := 4983230072969 + 3 ^ 40 * 1967613 * 2
def baseEnd_1967613 : Nat := 1010331211035115438788619

theorem tailTrace_1967613 : CollatzResearch.WordTrace tailWord_1967613 prefixEnd_1967613 1010331211035115438788619 := by
  unfold tailWord_1967613
  simp only [CollatzResearch.WordTrace]
  refine ⟨71764741820681617391875493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47843161213787744927916995 71764741820681617391875493)
  ·
    refine ⟨13455889091377803260976655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71764741820681617391875493 13455889091377803260976655)
    ·
      refine ⟨20183833637066704891464983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13455889091377803260976655 20183833637066704891464983)
      ·
        refine ⟨30275750455600057337197475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20183833637066704891464983 30275750455600057337197475)
        ·
          refine ⟨45413625683400086005796213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30275750455600057337197475 45413625683400086005796213)
          ·
            refine ⟨4257527407818758063043395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45413625683400086005796213 4257527407818758063043395)
            ·
              refine ⟨6386291111728137094565093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4257527407818758063043395 6386291111728137094565093)
              ·
                refine ⟨1197429583449025705230955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6386291111728137094565093 1197429583449025705230955)
                ·
                  refine ⟨1796144375173538557846433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1197429583449025705230955 1796144375173538557846433)
                  ·
                    refine ⟨1347108281380153918384825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1796144375173538557846433 1347108281380153918384825)
                    ·
                      refine ⟨1010331211035115438788619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1347108281380153918384825 1010331211035115438788619)
                      ·
                        rfl

theorem cell23_1967613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 4, 1, 2, 2].length) (baseStart_1967613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967613 prefixEnd_1967613 := by exact prefixLift 1967613
  have htrace : WordTrace (prefixWord ++ tailWord_1967613) baseStart_1967613 baseEnd_1967613 := by
    simpa [prefixWord, tailWord_1967613, baseEnd_1967613] using wordTrace_append hprefix tailTrace_1967613
  have hstable : (prefixWord ++ tailWord_1967613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967613).length < 2 ^ (prefixWord ++ tailWord_1967613).sum := by decide
  have hdescent : baseEnd_1967613 < baseStart_1967613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967636 : List Nat := [2, 4, 3, 1, 2, 1, 3, 7]
def baseStart_1967636 : Nat := 118140960795 + 1967636 * 2 ^ 59
def prefixEnd_1967636 : Nat := 4983230072969 + 3 ^ 40 * 1967636 * 2
def baseEnd_1967636 : Nat := 37420111892228475881519

theorem tailTrace_1967636 : CollatzResearch.WordTrace tailWord_1967636 prefixEnd_1967636 37420111892228475881519 := by
  unfold tailWord_1967636
  simp only [CollatzResearch.WordTrace]
  refine ⟨35882790349799146159981381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47843720466398861546641841 35882790349799146159981381)
  ·
    refine ⟨6728023190587339904996509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35882790349799146159981381 6728023190587339904996509)
    ·
      refine ⟨2523008696470252464373691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6728023190587339904996509 2523008696470252464373691)
      ·
        refine ⟨3784513044705378696560537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2523008696470252464373691 3784513044705378696560537)
        ·
          refine ⟨2838384783529034022420403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3784513044705378696560537 2838384783529034022420403)
          ·
            refine ⟨4257577175293551033630605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2838384783529034022420403 4257577175293551033630605)
            ·
              refine ⟨1596591440735081637611477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4257577175293551033630605 1596591440735081637611477)
              ·
                refine ⟨37420111892228475881519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1596591440735081637611477 37420111892228475881519)
                ·
                  rfl

theorem cell23_1967636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 7].length) (baseStart_1967636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967636 prefixEnd_1967636 := by exact prefixLift 1967636
  have htrace : WordTrace (prefixWord ++ tailWord_1967636) baseStart_1967636 baseEnd_1967636 := by
    simpa [prefixWord, tailWord_1967636, baseEnd_1967636] using wordTrace_append hprefix tailTrace_1967636
  have hstable : (prefixWord ++ tailWord_1967636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967636).length < 2 ^ (prefixWord ++ tailWord_1967636).sum := by decide
  have hdescent : baseEnd_1967636 < baseStart_1967636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967692 : List Nat := [2, 2, 1, 3, 1, 3, 2, 2, 7]
def baseStart_1967692 : Nat := 118140960795 + 1967692 * 2 ^ 59
def prefixEnd_1967692 : Nat := 4983230072969 + 3 ^ 40 * 1967692 * 2
def baseEnd_1967692 : Nat := 112263530667424514411195

theorem tailTrace_1967692 : CollatzResearch.WordTrace tailWord_1967692 prefixEnd_1967692 112263530667424514411195 := by
  unfold tailWord_1967692
  simp only [CollatzResearch.WordTrace]
  refine ⟨35883811593697706942000665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47845082124930275922667553 35883811593697706942000665)
  ·
    refine ⟨26912858695273280206500499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35883811593697706942000665 26912858695273280206500499)
    ·
      refine ⟨40369288042909920309750749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26912858695273280206500499 40369288042909920309750749)
      ·
        refine ⟨15138483016091220116156531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40369288042909920309750749 15138483016091220116156531)
        ·
          refine ⟨22707724524136830174234797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15138483016091220116156531 22707724524136830174234797)
          ·
            refine ⟨8515396696551311315338049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22707724524136830174234797 8515396696551311315338049)
            ·
              refine ⟨6386547522413483486503537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8515396696551311315338049 6386547522413483486503537)
              ·
                refine ⟨4789910641810112614877653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6386547522413483486503537 4789910641810112614877653)
                ·
                  refine ⟨112263530667424514411195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4789910641810112614877653 112263530667424514411195)
                  ·
                    rfl

theorem cell23_1967692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 7].length) (baseStart_1967692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967692 prefixEnd_1967692 := by exact prefixLift 1967692
  have htrace : WordTrace (prefixWord ++ tailWord_1967692) baseStart_1967692 baseEnd_1967692 := by
    simpa [prefixWord, tailWord_1967692, baseEnd_1967692] using wordTrace_append hprefix tailTrace_1967692
  have hstable : (prefixWord ++ tailWord_1967692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967692).length < 2 ^ (prefixWord ++ tailWord_1967692).sum := by decide
  have hdescent : baseEnd_1967692 < baseStart_1967692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967726 : List Nat := [4, 1, 2, 2, 3, 2, 1, 1, 7]
def baseStart_1967726 : Nat := 118140960795 + 1967726 * 2 ^ 59
def prefixEnd_1967726 : Nat := 4983230072969 + 3 ^ 40 * 1967726 * 2
def baseEnd_1967726 : Nat := 112265470483230388519511

theorem tailTrace_1967726 : CollatzResearch.WordTrace tailWord_1967726 prefixEnd_1967726 112265470483230388519511 := by
  unfold tailWord_1967726
  simp only [CollatzResearch.WordTrace]
  refine ⟨8971107908659029711342379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47845908846181491793826021 8971107908659029711342379)
  ·
    refine ⟨13456661862988544567013569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8971107908659029711342379 13456661862988544567013569)
    ·
      refine ⟨10092496397241408425260177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13456661862988544567013569 10092496397241408425260177)
      ·
        refine ⟨7569372297931056318945133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10092496397241408425260177 7569372297931056318945133)
        ·
          refine ⟨2838514611724146119604425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7569372297931056318945133 2838514611724146119604425)
          ·
            refine ⟨2128885958793109589703319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2838514611724146119604425 2128885958793109589703319)
            ·
              refine ⟨3193328938189664384554979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2128885958793109589703319 3193328938189664384554979)
              ·
                refine ⟨4789993407284496576832469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3193328938189664384554979 4789993407284496576832469)
                ·
                  refine ⟨112265470483230388519511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4789993407284496576832469 112265470483230388519511)
                  ·
                    rfl

theorem cell23_1967726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 7].length) (baseStart_1967726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967726 prefixEnd_1967726 := by exact prefixLift 1967726
  have htrace : WordTrace (prefixWord ++ tailWord_1967726) baseStart_1967726 baseEnd_1967726 := by
    simpa [prefixWord, tailWord_1967726, baseEnd_1967726] using wordTrace_append hprefix tailTrace_1967726
  have hstable : (prefixWord ++ tailWord_1967726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967726).length < 2 ^ (prefixWord ++ tailWord_1967726).sum := by decide
  have hdescent : baseEnd_1967726 < baseStart_1967726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967779 : List Nat := [1, 1, 1, 4, 1, 1, 3, 4, 2, 2, 3]
def baseStart_1967779 : Nat := 118140960795 + 1967779 * 2 ^ 59
def prefixEnd_1967779 : Nat := 4983230072969 + 3 ^ 40 * 1967779 * 2
def baseEnd_1967779 : Nat := 1010416448823761789312855

theorem tailTrace_1967779 : CollatzResearch.WordTrace tailWord_1967779 prefixEnd_1967779 1010416448823761789312855 := by
  unfold tailWord_1967779
  simp only [CollatzResearch.WordTrace]
  refine ⟨71770796338080227742418391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47847197558720151828278927 71770796338080227742418391)
  ·
    refine ⟨107656194507120341613627587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71770796338080227742418391 107656194507120341613627587)
    ·
      refine ⟨161484291760680512420441381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107656194507120341613627587 161484291760680512420441381)
      ·
        refine ⟨30278304705127596078832759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161484291760680512420441381 30278304705127596078832759)
        ·
          refine ⟨45417457057691394118249139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30278304705127596078832759 45417457057691394118249139)
          ·
            refine ⟨68126185586537091177373709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45417457057691394118249139 68126185586537091177373709)
            ·
              refine ⟨25547319594951409191515141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68126185586537091177373709 25547319594951409191515141)
              ·
                refine ⟨4790122424053389223409089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25547319594951409191515141 4790122424053389223409089)
                ·
                  refine ⟨3592591818040041917556817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4790122424053389223409089 3592591818040041917556817)
                  ·
                    refine ⟨2694443863530031438167613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3592591818040041917556817 2694443863530031438167613)
                    ·
                      refine ⟨1010416448823761789312855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2694443863530031438167613 1010416448823761789312855)
                      ·
                        rfl

theorem cell23_1967779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_1967779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967779 prefixEnd_1967779 := by exact prefixLift 1967779
  have htrace : WordTrace (prefixWord ++ tailWord_1967779) baseStart_1967779 baseEnd_1967779 := by
    simpa [prefixWord, tailWord_1967779, baseEnd_1967779] using wordTrace_append hprefix tailTrace_1967779
  have hstable : (prefixWord ++ tailWord_1967779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967779).length < 2 ^ (prefixWord ++ tailWord_1967779).sum := by decide
  have hdescent : baseEnd_1967779 < baseStart_1967779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967799 : List Nat := [1, 1, 3, 1, 5, 1, 2, 3, 6]
def baseStart_1967799 : Nat := 118140960795 + 1967799 * 2 ^ 59
def prefixEnd_1967799 : Nat := 4983230072969 + 3 ^ 40 * 1967799 * 2
def baseEnd_1967799 : Nat := 112269635381872412340307

theorem tailTrace_1967799 : CollatzResearch.WordTrace tailWord_1967799 prefixEnd_1967799 112269635381872412340307 := by
  unfold tailWord_1967799
  simp only [CollatzResearch.WordTrace]
  refine ⟨71771525798007771158146451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47847683865338514105430967 71771525798007771158146451)
  ·
    refine ⟨107657288697011656737219677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71771525798007771158146451 107657288697011656737219677)
    ·
      refine ⟨40371483261379371276457379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107657288697011656737219677 40371483261379371276457379)
      ·
        refine ⟨60557224892069056914686069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40371483261379371276457379 60557224892069056914686069)
        ·
          refine ⟨5677239833631474085751819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60557224892069056914686069 5677239833631474085751819)
          ·
            refine ⟨8515859750447211128627729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5677239833631474085751819 8515859750447211128627729)
            ·
              refine ⟨6386894812835408346470797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8515859750447211128627729 6386894812835408346470797)
              ·
                refine ⟨2395085554813278129926549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6386894812835408346470797 2395085554813278129926549)
                ·
                  refine ⟨112269635381872412340307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2395085554813278129926549 112269635381872412340307)
                  ·
                    rfl

theorem cell23_1967799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 6].length) (baseStart_1967799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967799 prefixEnd_1967799 := by exact prefixLift 1967799
  have htrace : WordTrace (prefixWord ++ tailWord_1967799) baseStart_1967799 baseEnd_1967799 := by
    simpa [prefixWord, tailWord_1967799, baseEnd_1967799] using wordTrace_append hprefix tailTrace_1967799
  have hstable : (prefixWord ++ tailWord_1967799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967799).length < 2 ^ (prefixWord ++ tailWord_1967799).sum := by decide
  have hdescent : baseEnd_1967799 < baseStart_1967799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967810 : List Nat := [3, 5, 1, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_1967810 : Nat := 118140960795 + 1967810 * 2 ^ 59
def prefixEnd_1967810 : Nat := 4983230072969 + 3 ^ 40 * 1967810 * 2
def baseEnd_1967810 : Nat := 1010432366724051168025213

theorem tailTrace_1967810 : CollatzResearch.WordTrace tailWord_1967810 prefixEnd_1967810 1010432366724051168025213 := by
  unfold tailWord_1967810
  simp only [CollatzResearch.WordTrace]
  refine ⟨17942981750241980009199221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47847951333978613357864589 17942981750241980009199221)
  ·
    refine ⟨1682154539085185625862427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17942981750241980009199221 1682154539085185625862427)
    ·
      refine ⟨2523231808627778438793641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1682154539085185625862427 2523231808627778438793641)
      ·
        refine ⟨1892423856470833829095231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2523231808627778438793641 1892423856470833829095231)
        ·
          refine ⟨2838635784706250743642847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1892423856470833829095231 2838635784706250743642847)
          ·
            refine ⟨4257953677059376115464271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2838635784706250743642847 4257953677059376115464271)
            ·
              refine ⟨6386930515589064173196407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4257953677059376115464271 6386930515589064173196407)
              ·
                refine ⟨9580395773383596259794611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6386930515589064173196407 9580395773383596259794611)
                ·
                  refine ⟨14370593660075394389691917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9580395773383596259794611 14370593660075394389691917)
                  ·
                    refine ⟨5388972622528272896134469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14370593660075394389691917 5388972622528272896134469)
                    ·
                      refine ⟨1010432366724051168025213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5388972622528272896134469 1010432366724051168025213)
                      ·
                        rfl

theorem cell23_1967810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_1967810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967810 prefixEnd_1967810 := by exact prefixLift 1967810
  have htrace : WordTrace (prefixWord ++ tailWord_1967810) baseStart_1967810 baseEnd_1967810 := by
    simpa [prefixWord, tailWord_1967810, baseEnd_1967810] using wordTrace_append hprefix tailTrace_1967810
  have hstable : (prefixWord ++ tailWord_1967810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967810).length < 2 ^ (prefixWord ++ tailWord_1967810).sum := by decide
  have hdescent : baseEnd_1967810 < baseStart_1967810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967820 : List Nat := [2, 2, 1, 5, 2, 1, 2, 3, 1, 4]
def baseStart_1967820 : Nat := 118140960795 + 1967820 * 2 ^ 59
def prefixEnd_1967820 : Nat := 4983230072969 + 3 ^ 40 * 1967820 * 2
def baseEnd_1967820 : Nat := 336812500510198709633389

theorem tailTrace_1967820 : CollatzResearch.WordTrace tailWord_1967820 prefixEnd_1967820 336812500510198709633389 := by
  unfold tailWord_1967820
  simp only [CollatzResearch.WordTrace]
  refine ⟨35886145865465845872330457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47848194487287794496440609 35886145865465845872330457)
  ·
    refine ⟨26914609399099384404247843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35886145865465845872330457 26914609399099384404247843)
    ·
      refine ⟨40371914098649076606371765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26914609399099384404247843 40371914098649076606371765)
      ·
        refine ⟨3784866946748350931847353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40371914098649076606371765 3784866946748350931847353)
        ·
          refine ⟨2838650210061263198885515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3784866946748350931847353 2838650210061263198885515)
          ·
            refine ⟨4257975315091894798328273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2838650210061263198885515 4257975315091894798328273)
            ·
              refine ⟨3193481486318921098746205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4257975315091894798328273 3193481486318921098746205)
              ·
                refine ⟨1197555557369595412029827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3193481486318921098746205 1197555557369595412029827)
                ·
                  refine ⟨1796333336054393118044741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1197555557369595412029827 1796333336054393118044741)
                  ·
                    refine ⟨336812500510198709633389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1796333336054393118044741 336812500510198709633389)
                    ·
                      rfl

theorem cell23_1967820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 3, 1, 4].length) (baseStart_1967820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967820 prefixEnd_1967820 := by exact prefixLift 1967820
  have htrace : WordTrace (prefixWord ++ tailWord_1967820) baseStart_1967820 baseEnd_1967820 := by
    simpa [prefixWord, tailWord_1967820, baseEnd_1967820] using wordTrace_append hprefix tailTrace_1967820
  have hstable : (prefixWord ++ tailWord_1967820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967820).length < 2 ^ (prefixWord ++ tailWord_1967820).sum := by decide
  have hdescent : baseEnd_1967820 < baseStart_1967820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967859 : List Nat := [1, 1, 1, 2, 2, 3, 5, 1, 1, 6]
def baseStart_1967859 : Nat := 118140960795 + 1967859 * 2 ^ 59
def prefixEnd_1967859 : Nat := 4983230072969 + 3 ^ 40 * 1967859 * 2
def baseEnd_1967859 : Nat := 336819175758707158770829

theorem tailTrace_1967859 : CollatzResearch.WordTrace tailWord_1967859 prefixEnd_1967859 336819175758707158770829 := by
  unfold tailWord_1967859
  simp only [CollatzResearch.WordTrace]
  refine ⟨71773714177790401405330631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47849142785193600936887087 71773714177790401405330631)
  ·
    refine ⟨107660571266685602107995947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71773714177790401405330631 107660571266685602107995947)
    ·
      refine ⟨161490856900028403161993921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107660571266685602107995947 161490856900028403161993921)
      ·
        refine ⟨121118142675021302371495441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161490856900028403161993921 121118142675021302371495441)
        ·
          refine ⟨90838607006265976778621581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121118142675021302371495441 90838607006265976778621581)
          ·
            refine ⟨34064477627349741291983093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90838607006265976778621581 34064477627349741291983093)
            ·
              refine ⟨3193544777564038246123415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34064477627349741291983093 3193544777564038246123415)
              ·
                refine ⟨4790317166346057369185123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3193544777564038246123415 4790317166346057369185123)
                ·
                  refine ⟨7185475749519086053777685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4790317166346057369185123 7185475749519086053777685)
                  ·
                    refine ⟨336819175758707158770829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7185475749519086053777685 336819175758707158770829)
                    ·
                      rfl

theorem cell23_1967859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 6].length) (baseStart_1967859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967859 prefixEnd_1967859 := by exact prefixLift 1967859
  have htrace : WordTrace (prefixWord ++ tailWord_1967859) baseStart_1967859 baseEnd_1967859 := by
    simpa [prefixWord, tailWord_1967859, baseEnd_1967859] using wordTrace_append hprefix tailTrace_1967859
  have hstable : (prefixWord ++ tailWord_1967859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967859).length < 2 ^ (prefixWord ++ tailWord_1967859).sum := by decide
  have hdescent : baseEnd_1967859 < baseStart_1967859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967872 : List Nat := [2, 1, 1, 2, 1, 1, 2, 13]
def baseStart_1967872 : Nat := 118140960795 + 1967872 * 2 ^ 59
def prefixEnd_1967872 : Nat := 4983230072969 + 3 ^ 40 * 1967872 * 2
def baseEnd_1967872 : Nat := 37424600093504812053701

theorem tailTrace_1967872 : CollatzResearch.WordTrace tailWord_1967872 prefixEnd_1967872 37424600093504812053701 := by
  unfold tailWord_1967872
  simp only [CollatzResearch.WordTrace]
  refine ⟨35887094163371652312776935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47849458884495536417035913 35887094163371652312776935)
  ·
    refine ⟨53830641245057478469165403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35887094163371652312776935 53830641245057478469165403)
    ·
      refine ⟨80745961867586217703748105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53830641245057478469165403 80745961867586217703748105)
      ·
        refine ⟨60559471400689663277811079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80745961867586217703748105 60559471400689663277811079)
        ·
          refine ⟨90839207101034494916716619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60559471400689663277811079 90839207101034494916716619)
          ·
            refine ⟨136258810651551742375074929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90839207101034494916716619 136258810651551742375074929)
            ·
              refine ⟨102194107988663806781306197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136258810651551742375074929 102194107988663806781306197)
              ·
                refine ⟨37424600093504812053701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 102194107988663806781306197 37424600093504812053701)
                ·
                  rfl

theorem cell23_1967872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 13].length) (baseStart_1967872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967872 prefixEnd_1967872 := by exact prefixLift 1967872
  have htrace : WordTrace (prefixWord ++ tailWord_1967872) baseStart_1967872 baseEnd_1967872 := by
    simpa [prefixWord, tailWord_1967872, baseEnd_1967872] using wordTrace_append hprefix tailTrace_1967872
  have hstable : (prefixWord ++ tailWord_1967872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967872).length < 2 ^ (prefixWord ++ tailWord_1967872).sum := by decide
  have hdescent : baseEnd_1967872 < baseStart_1967872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967876 : List Nat := [2, 3, 2, 2, 1, 2, 1, 2, 4, 4]
def baseStart_1967876 : Nat := 118140960795 + 1967876 * 2 ^ 59
def prefixEnd_1967876 : Nat := 4983230072969 + 3 ^ 40 * 1967876 * 2
def baseEnd_1967876 : Nat := 336822085482415969933303

theorem tailTrace_1967876 : CollatzResearch.WordTrace tailWord_1967876 prefixEnd_1967876 336822085482415969933303 := by
  unfold tailWord_1967876
  simp only [CollatzResearch.WordTrace]
  refine ⟨35887167109364406654349741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47849556145819208872466321 35887167109364406654349741)
  ·
    refine ⟨13457687666011652495381153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35887167109364406654349741 13457687666011652495381153)
    ·
      refine ⟨10093265749508739371535865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13457687666011652495381153 10093265749508739371535865)
      ·
        refine ⟨7569949312131554528651899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10093265749508739371535865 7569949312131554528651899)
        ·
          refine ⟨11354923968197331792977849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7569949312131554528651899 11354923968197331792977849)
          ·
            refine ⟨8516192976147998844733387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11354923968197331792977849 8516192976147998844733387)
            ·
              refine ⟨12774289464221998267100081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8516192976147998844733387 12774289464221998267100081)
              ·
                refine ⟨9580717098166498700325061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12774289464221998267100081 9580717098166498700325061)
                ·
                  refine ⟨1796384455906218506310949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9580717098166498700325061 1796384455906218506310949)
                  ·
                    refine ⟨336822085482415969933303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1796384455906218506310949 336822085482415969933303)
                    ·
                      rfl

theorem cell23_1967876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_1967876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967876 prefixEnd_1967876 := by exact prefixLift 1967876
  have htrace : WordTrace (prefixWord ++ tailWord_1967876) baseStart_1967876 baseEnd_1967876 := by
    simpa [prefixWord, tailWord_1967876, baseEnd_1967876] using wordTrace_append hprefix tailTrace_1967876
  have hstable : (prefixWord ++ tailWord_1967876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967876).length < 2 ^ (prefixWord ++ tailWord_1967876).sum := by decide
  have hdescent : baseEnd_1967876 < baseStart_1967876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967899 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 3, 3, 3]
def baseStart_1967899 : Nat := 118140960795 + 1967899 * 2 ^ 59
def prefixEnd_1967899 : Nat := 4983230072969 + 3 ^ 40 * 1967899 * 2
def baseEnd_1967899 : Nat := 1010478066502301319812303

theorem tailTrace_1967899 : CollatzResearch.WordTrace tailWord_1967899 prefixEnd_1967899 1010478066502301319812303 := by
  unfold tailWord_1967899
  simp only [CollatzResearch.WordTrace]
  refine ⟨71775173097645488236786751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47850115398430325491191167 71775173097645488236786751)
  ·
    refine ⟨107662759646468232355180127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71775173097645488236786751 107662759646468232355180127)
    ·
      refine ⟨161494139469702348532770191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107662759646468232355180127 161494139469702348532770191)
      ·
        refine ⟨242241209204553522799155287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161494139469702348532770191 242241209204553522799155287)
        ·
          refine ⟨363361813806830284198732931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242241209204553522799155287 363361813806830284198732931)
          ·
            refine ⟨545042720710245426298099397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363361813806830284198732931 545042720710245426298099397)
            ·
              refine ⟨102195510133171017430893637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 545042720710245426298099397 102195510133171017430893637)
              ·
                refine ⟨19161658149969565768292557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102195510133171017430893637 19161658149969565768292557)
                ·
                  refine ⟨7185621806238587163109709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19161658149969565768292557 7185621806238587163109709)
                  ·
                    refine ⟨2694608177339470186166141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7185621806238587163109709 2694608177339470186166141)
                    ·
                      refine ⟨1010478066502301319812303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2694608177339470186166141 1010478066502301319812303)
                      ·
                        rfl

theorem cell23_1967899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 3, 3].length) (baseStart_1967899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967899 prefixEnd_1967899 := by exact prefixLift 1967899
  have htrace : WordTrace (prefixWord ++ tailWord_1967899) baseStart_1967899 baseEnd_1967899 := by
    simpa [prefixWord, tailWord_1967899, baseEnd_1967899] using wordTrace_append hprefix tailTrace_1967899
  have hstable : (prefixWord ++ tailWord_1967899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967899).length < 2 ^ (prefixWord ++ tailWord_1967899).sum := by decide
  have hdescent : baseEnd_1967899 < baseStart_1967899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967933 : List Nat := [1, 4, 1, 4, 1, 2, 1, 2, 1, 3, 3]
def baseStart_1967933 : Nat := 118140960795 + 1967933 * 2 ^ 59
def prefixEnd_1967933 : Nat := 4983230072969 + 3 ^ 40 * 1967933 * 2
def baseEnd_1967933 : Nat := 1010495524844554186787147

theorem tailTrace_1967933 : CollatzResearch.WordTrace tailWord_1967933 prefixEnd_1967933 1010495524844554186787147 := by
  unfold tailWord_1967933
  simp only [CollatzResearch.WordTrace]
  refine ⟨71776413179522312043524453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47850942119681541362349635 71776413179522312043524453)
  ·
    refine ⟨13458077471160433508160835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71776413179522312043524453 13458077471160433508160835)
    ·
      refine ⟨20187116206740650262241253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13458077471160433508160835 20187116206740650262241253)
      ·
        refine ⟨3785084288763871924170235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20187116206740650262241253 3785084288763871924170235)
        ·
          refine ⟨5677626433145807886255353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3785084288763871924170235 5677626433145807886255353)
          ·
            refine ⟨4258219824859355914691515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5677626433145807886255353 4258219824859355914691515)
            ·
              refine ⟨6387329737289033872037273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4258219824859355914691515 6387329737289033872037273)
              ·
                refine ⟨4790497302966775404027955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6387329737289033872037273 4790497302966775404027955)
                ·
                  refine ⟨7185745954450163106041933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4790497302966775404027955 7185745954450163106041933)
                  ·
                    refine ⟨2694654732918811164765725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7185745954450163106041933 2694654732918811164765725)
                    ·
                      refine ⟨1010495524844554186787147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2694654732918811164765725 1010495524844554186787147)
                      ·
                        rfl

theorem cell23_1967933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_1967933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967933 prefixEnd_1967933 := by exact prefixLift 1967933
  have htrace : WordTrace (prefixWord ++ tailWord_1967933) baseStart_1967933 baseEnd_1967933 := by
    simpa [prefixWord, tailWord_1967933, baseEnd_1967933] using wordTrace_append hprefix tailTrace_1967933
  have hstable : (prefixWord ++ tailWord_1967933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967933).length < 2 ^ (prefixWord ++ tailWord_1967933).sum := by decide
  have hdescent : baseEnd_1967933 < baseStart_1967933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967943 : List Nat := [1, 1, 4, 1, 2, 1, 2, 5, 1, 3, 2]
def baseStart_1967943 : Nat := 118140960795 + 1967943 * 2 ^ 59
def prefixEnd_1967943 : Nat := 4983230072969 + 3 ^ 40 * 1967943 * 2
def baseEnd_1967943 : Nat := 1010500659651099147662101

theorem tailTrace_1967943 : CollatzResearch.WordTrace tailWord_1967943 prefixEnd_1967943 1010500659651099147662101 := by
  unfold tailWord_1967943
  simp only [CollatzResearch.WordTrace]
  refine ⟨71776777909486083751388483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47851185272990722500925655 71776777909486083751388483)
  ·
    refine ⟨107665166864229125627082725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71776777909486083751388483 107665166864229125627082725)
    ·
      refine ⟨20187218787042961055078011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107665166864229125627082725 20187218787042961055078011)
      ·
        refine ⟨30280828180564441582617017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20187218787042961055078011 30280828180564441582617017)
        ·
          refine ⟨22710621135423331186962763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30280828180564441582617017 22710621135423331186962763)
          ·
            refine ⟨34065931703134996780444145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22710621135423331186962763 34065931703134996780444145)
            ·
              refine ⟨25549448777351247585333109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34065931703134996780444145 25549448777351247585333109)
              ·
                refine ⟨2395260822876679461124979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25549448777351247585333109 2395260822876679461124979)
                ·
                  refine ⟨3592891234315019191687469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2395260822876679461124979 3592891234315019191687469)
                  ·
                    refine ⟨1347334212868132196882801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3592891234315019191687469 1347334212868132196882801)
                    ·
                      refine ⟨1010500659651099147662101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1347334212868132196882801 1010500659651099147662101)
                      ·
                        rfl

theorem cell23_1967943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 3, 2].length) (baseStart_1967943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967943 prefixEnd_1967943 := by exact prefixLift 1967943
  have htrace : WordTrace (prefixWord ++ tailWord_1967943) baseStart_1967943 baseEnd_1967943 := by
    simpa [prefixWord, tailWord_1967943, baseEnd_1967943] using wordTrace_append hprefix tailTrace_1967943
  have hstable : (prefixWord ++ tailWord_1967943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967943).length < 2 ^ (prefixWord ++ tailWord_1967943).sum := by decide
  have hdescent : baseEnd_1967943 < baseStart_1967943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967956 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 2, 3, 4]
def baseStart_1967956 : Nat := 118140960795 + 1967956 * 2 ^ 59
def prefixEnd_1967956 : Nat := 4983230072969 + 3 ^ 40 * 1967956 * 2
def baseEnd_1967956 : Nat := 1010507334899607596799541

theorem tailTrace_1967956 : CollatzResearch.WordTrace tailWord_1967956 prefixEnd_1967956 1010507334899607596799541 := by
  unfold tailWord_1967956
  simp only [CollatzResearch.WordTrace]
  refine ⟨35888626029219493485805861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47851501372292657981074481 35888626029219493485805861)
  ·
    refine ⟨6729117380478655028588599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35888626029219493485805861 6729117380478655028588599)
    ·
      refine ⟨10093676070717982542882899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6729117380478655028588599 10093676070717982542882899)
      ·
        refine ⟨15140514106076973814324349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10093676070717982542882899 15140514106076973814324349)
        ·
          refine ⟨5677692789778865180371631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15140514106076973814324349 5677692789778865180371631)
          ·
            refine ⟨8516539184668297770557447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5677692789778865180371631 8516539184668297770557447)
            ·
              refine ⟨12774808777002446655836171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8516539184668297770557447 12774808777002446655836171)
              ·
                refine ⟨19162213165503669983754257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12774808777002446655836171 19162213165503669983754257)
                ·
                  refine ⟨14371659874127752487815693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19162213165503669983754257 14371659874127752487815693)
                  ·
                    refine ⟨5389372452797907182930885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14371659874127752487815693 5389372452797907182930885)
                    ·
                      refine ⟨1010507334899607596799541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5389372452797907182930885 1010507334899607596799541)
                      ·
                        rfl

theorem cell23_1967956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_1967956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967956 prefixEnd_1967956 := by exact prefixLift 1967956
  have htrace : WordTrace (prefixWord ++ tailWord_1967956) baseStart_1967956 baseEnd_1967956 := by
    simpa [prefixWord, tailWord_1967956, baseEnd_1967956] using wordTrace_append hprefix tailTrace_1967956
  have hstable : (prefixWord ++ tailWord_1967956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967956).length < 2 ^ (prefixWord ++ tailWord_1967956).sum := by decide
  have hdescent : baseEnd_1967956 < baseStart_1967956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967973 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 6, 2, 2]
def baseStart_1967973 : Nat := 118140960795 + 1967973 * 2 ^ 59
def prefixEnd_1967973 : Nat := 4983230072969 + 3 ^ 40 * 1967973 * 2
def baseEnd_1967973 : Nat := 1010516064070734030286963

theorem tailTrace_1967973 : CollatzResearch.WordTrace tailWord_1967973 prefixEnd_1967973 1010516064070734030286963 := by
  unfold tailWord_1967973
  simp only [CollatzResearch.WordTrace]
  refine ⟨71777872099377398874980573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47851914732918265916653715 71777872099377398874980573)
  ·
    refine ⟨26916702037266524578117715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71777872099377398874980573 26916702037266524578117715)
    ·
      refine ⟨40375053055899786867176573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26916702037266524578117715 40375053055899786867176573)
      ·
        refine ⟨15140644895962420075191215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40375053055899786867176573 15140644895962420075191215)
        ·
          refine ⟨22710967343943630112786823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15140644895962420075191215 22710967343943630112786823)
          ·
            refine ⟨34066451015915445169180235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22710967343943630112786823 34066451015915445169180235)
            ·
              refine ⟨51099676523873167753770353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34066451015915445169180235 51099676523873167753770353)
              ·
                refine ⟨38324757392904875815327765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51099676523873167753770353 38324757392904875815327765)
                ·
                  refine ⟨1796473002792416053843489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38324757392904875815327765 1796473002792416053843489)
                  ·
                    refine ⟨1347354752094312040382617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1796473002792416053843489 1347354752094312040382617)
                    ·
                      refine ⟨1010516064070734030286963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1347354752094312040382617 1010516064070734030286963)
                      ·
                        rfl

theorem cell23_1967973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_1967973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967973 prefixEnd_1967973 := by exact prefixLift 1967973
  have htrace : WordTrace (prefixWord ++ tailWord_1967973) baseStart_1967973 baseEnd_1967973 := by
    simpa [prefixWord, tailWord_1967973, baseEnd_1967973] using wordTrace_append hprefix tailTrace_1967973
  have hstable : (prefixWord ++ tailWord_1967973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967973).length < 2 ^ (prefixWord ++ tailWord_1967973).sum := by decide
  have hdescent : baseEnd_1967973 < baseStart_1967973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967976 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 2, 4, 3]
def baseStart_1967976 : Nat := 118140960795 + 1967976 * 2 ^ 59
def prefixEnd_1967976 : Nat := 4983230072969 + 3 ^ 40 * 1967976 * 2
def baseEnd_1967976 : Nat := 1010517604512697518549449

theorem tailTrace_1967976 : CollatzResearch.WordTrace tailWord_1967976 prefixEnd_1967976 1010517604512697518549449 := by
  unfold tailWord_1967976
  simp only [CollatzResearch.WordTrace]
  refine ⟨35888990759183265193669891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47851987678911020258226521 35888990759183265193669891)
  ·
    refine ⟨53833486138774897790504837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35888990759183265193669891 53833486138774897790504837)
    ·
      refine ⟨10093778651020293335719657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53833486138774897790504837 10093778651020293335719657)
      ·
        refine ⟨7570333988265220001789743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10093778651020293335719657 7570333988265220001789743)
        ·
          refine ⟨11355500982397830002684615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7570333988265220001789743 11355500982397830002684615)
          ·
            refine ⟨17033251473596745004026923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11355500982397830002684615 17033251473596745004026923)
            ·
              refine ⟨25549877210395117506040385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17033251473596745004026923 25549877210395117506040385)
              ·
                refine ⟨19162407907796338129530289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25549877210395117506040385 19162407907796338129530289)
                ·
                  refine ⟨14371805930847253597147717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19162407907796338129530289 14371805930847253597147717)
                  ·
                    refine ⟨2694713612033860049465197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14371805930847253597147717 2694713612033860049465197)
                    ·
                      refine ⟨1010517604512697518549449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2694713612033860049465197 1010517604512697518549449)
                      ·
                        rfl

theorem cell23_1967976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_1967976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1967976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1967976 prefixEnd_1967976 := by exact prefixLift 1967976
  have htrace : WordTrace (prefixWord ++ tailWord_1967976) baseStart_1967976 baseEnd_1967976 := by
    simpa [prefixWord, tailWord_1967976, baseEnd_1967976] using wordTrace_append hprefix tailTrace_1967976
  have hstable : (prefixWord ++ tailWord_1967976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967976).length < 2 ^ (prefixWord ++ tailWord_1967976).sum := by decide
  have hdescent : baseEnd_1967976 < baseStart_1967976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968019 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 5]
def baseStart_1968019 : Nat := 118140960795 + 1968019 * 2 ^ 59
def prefixEnd_1968019 : Nat := 4983230072969 + 3 ^ 40 * 1968019 * 2
def baseEnd_1968019 : Nat := 1010539684180840850311751

theorem tailTrace_1968019 : CollatzResearch.WordTrace tailWord_1968019 prefixEnd_1968019 1010539684180840850311751 := by
  unfold tailWord_1968019
  simp only [CollatzResearch.WordTrace]
  refine ⟨71779549857210748731155111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47853033238140499154103407 71779549857210748731155111)
  ·
    refine ⟨107669324785816123096732667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71779549857210748731155111 107669324785816123096732667)
    ·
      refine ⟨161503987178724184645099001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107669324785816123096732667 161503987178724184645099001)
      ·
        refine ⟨121127990384043138483824251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161503987178724184645099001 121127990384043138483824251)
        ·
          refine ⟨181691985576064707725736377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121127990384043138483824251 181691985576064707725736377)
          ·
            refine ⟨136268989182048530794302283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181691985576064707725736377 136268989182048530794302283)
            ·
              refine ⟨204403483773072796191453425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136268989182048530794302283 204403483773072796191453425)
              ·
                refine ⟨153302612829804597143590069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204403483773072796191453425 153302612829804597143590069)
                ·
                  refine ⟨14372119952794180982211569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153302612829804597143590069 14372119952794180982211569)
                  ·
                    refine ⟨10779089964595635736658677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14372119952794180982211569 10779089964595635736658677)
                    ·
                      refine ⟨1010539684180840850311751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10779089964595635736658677 1010539684180840850311751)
                      ·
                        rfl

theorem cell23_1968019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 5].length) (baseStart_1968019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968019 prefixEnd_1968019 := by exact prefixLift 1968019
  have htrace : WordTrace (prefixWord ++ tailWord_1968019) baseStart_1968019 baseEnd_1968019 := by
    simpa [prefixWord, tailWord_1968019, baseEnd_1968019] using wordTrace_append hprefix tailTrace_1968019
  have hstable : (prefixWord ++ tailWord_1968019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968019).length < 2 ^ (prefixWord ++ tailWord_1968019).sum := by decide
  have hdescent : baseEnd_1968019 < baseStart_1968019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968024 : List Nat := [2, 1, 2, 6, 2, 1, 1, 1, 1, 4, 2]
def baseStart_1968024 : Nat := 118140960795 + 1968024 * 2 ^ 59
def prefixEnd_1968024 : Nat := 4983230072969 + 3 ^ 40 * 1968024 * 2
def baseEnd_1968024 : Nat := 1010542251584113330749229

theorem tailTrace_1968024 : CollatzResearch.WordTrace tailWord_1968024 prefixEnd_1968024 1010542251584113330749229 := by
  unfold tailWord_1968024
  simp only [CollatzResearch.WordTrace]
  refine ⟨35889866111096317292543563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47853154814795089723391417 35889866111096317292543563)
  ·
    refine ⟨53834799166644475938815345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35889866111096317292543563 53834799166644475938815345)
    ·
      refine ⟨40376099374983356954111509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53834799166644475938815345 40376099374983356954111509)
      ·
        refine ⟨1892629658202344857223977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40376099374983356954111509 1892629658202344857223977)
        ·
          refine ⟨1419472243651758642917983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1892629658202344857223977 1419472243651758642917983)
          ·
            refine ⟨2129208365477637964376975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1419472243651758642917983 2129208365477637964376975)
            ·
              refine ⟨3193812548216456946565463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2129208365477637964376975 3193812548216456946565463)
              ·
                refine ⟨4790718822324685419848195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3193812548216456946565463 4790718822324685419848195)
                ·
                  refine ⟨7186078233487028129772293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4790718822324685419848195 7186078233487028129772293)
                  ·
                    refine ⟨1347389668778817774332305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7186078233487028129772293 1347389668778817774332305)
                    ·
                      refine ⟨1010542251584113330749229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1347389668778817774332305 1010542251584113330749229)
                      ·
                        rfl

theorem cell23_1968024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_1968024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968024 prefixEnd_1968024 := by exact prefixLift 1968024
  have htrace : WordTrace (prefixWord ++ tailWord_1968024) baseStart_1968024 baseEnd_1968024 := by
    simpa [prefixWord, tailWord_1968024, baseEnd_1968024] using wordTrace_append hprefix tailTrace_1968024
  have hstable : (prefixWord ++ tailWord_1968024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968024).length < 2 ^ (prefixWord ++ tailWord_1968024).sum := by decide
  have hdescent : baseEnd_1968024 < baseStart_1968024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968026 : List Nat := [3, 1, 1, 4, 2, 1, 1, 2, 1, 7]
def baseStart_1968026 : Nat := 118140960795 + 1968026 * 2 ^ 59
def prefixEnd_1968026 : Nat := 4983230072969 + 3 ^ 40 * 1968026 * 2
def baseEnd_1968026 : Nat := 336847759515140774308073

theorem tailTrace_1968026 : CollatzResearch.WordTrace tailWord_1968026 prefixEnd_1968026 336847759515140774308073 := by
  unfold tailWord_1968026
  simp only [CollatzResearch.WordTrace]
  refine ⟨17944951292046347231664983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47853203445456925951106621 17944951292046347231664983)
  ·
    refine ⟨26917426938069520847497475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17944951292046347231664983 26917426938069520847497475)
    ·
      refine ⟨40376140407104281271246213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26917426938069520847497475 40376140407104281271246213)
      ·
        refine ⟨7570526326332052738358665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40376140407104281271246213 7570526326332052738358665)
        ·
          refine ⟨5677894744749039553768999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7570526326332052738358665 5677894744749039553768999)
          ·
            refine ⟨8516842117123559330653499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5677894744749039553768999 8516842117123559330653499)
            ·
              refine ⟨12775263175685338995980249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8516842117123559330653499 12775263175685338995980249)
              ·
                refine ⟨9581447381764004246985187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12775263175685338995980249 9581447381764004246985187)
                ·
                  refine ⟨14372171072646006370477781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9581447381764004246985187 14372171072646006370477781)
                  ·
                    refine ⟨336847759515140774308073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14372171072646006370477781 336847759515140774308073)
                    ·
                      rfl

theorem cell23_1968026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 1, 7].length) (baseStart_1968026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968026 prefixEnd_1968026 := by exact prefixLift 1968026
  have htrace : WordTrace (prefixWord ++ tailWord_1968026) baseStart_1968026 baseEnd_1968026 := by
    simpa [prefixWord, tailWord_1968026, baseEnd_1968026] using wordTrace_append hprefix tailTrace_1968026
  have hstable : (prefixWord ++ tailWord_1968026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968026).length < 2 ^ (prefixWord ++ tailWord_1968026).sum := by decide
  have hdescent : baseEnd_1968026 < baseStart_1968026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968060 : List Nat := [2, 2, 2, 5, 1, 1, 1, 2, 2, 5]
def baseStart_1968060 : Nat := 118140960795 + 1968060 * 2 ^ 59
def prefixEnd_1968060 : Nat := 4983230072969 + 3 ^ 40 * 1968060 * 2
def baseEnd_1968060 : Nat := 336853578962558396633021

theorem tailTrace_1968060 : CollatzResearch.WordTrace tailWord_1968060 prefixEnd_1968060 336853578962558396633021 := by
  unfold tailWord_1968060
  simp only [CollatzResearch.WordTrace]
  refine ⟨35890522625031106366698817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47854030166708141822265089 35890522625031106366698817)
  ·
    refine ⟨26917891968773329775024113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35890522625031106366698817 26917891968773329775024113)
    ·
      refine ⟨20188418976579997331268085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26917891968773329775024113 20188418976579997331268085)
      ·
        refine ⟨1892664279054374749806383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20188418976579997331268085 1892664279054374749806383)
        ·
          refine ⟨2838996418581562124709575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1892664279054374749806383 2838996418581562124709575)
          ·
            refine ⟨4258494627872343187064363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2838996418581562124709575 4258494627872343187064363)
            ·
              refine ⟨6387741941808514780596545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4258494627872343187064363 6387741941808514780596545)
              ·
                refine ⟨4790806456356386085447409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6387741941808514780596545 4790806456356386085447409)
                ·
                  refine ⟨3593104842267289564085557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4790806456356386085447409 3593104842267289564085557)
                  ·
                    refine ⟨336853578962558396633021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3593104842267289564085557 336853578962558396633021)
                    ·
                      rfl

theorem cell23_1968060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_1968060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968060 prefixEnd_1968060 := by exact prefixLift 1968060
  have htrace : WordTrace (prefixWord ++ tailWord_1968060) baseStart_1968060 baseEnd_1968060 := by
    simpa [prefixWord, tailWord_1968060, baseEnd_1968060] using wordTrace_append hprefix tailTrace_1968060
  have hstable : (prefixWord ++ tailWord_1968060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968060).length < 2 ^ (prefixWord ++ tailWord_1968060).sum := by decide
  have hdescent : baseEnd_1968060 < baseStart_1968060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968096 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 3]
def baseStart_1968096 : Nat := 118140960795 + 1968096 * 2 ^ 59
def prefixEnd_1968096 : Nat := 4983230072969 + 3 ^ 40 * 1968096 * 2
def baseEnd_1968096 : Nat := 1010579222191237049048897

theorem tailTrace_1968096 : CollatzResearch.WordTrace tailWord_1968096 prefixEnd_1968096 1010579222191237049048897 := by
  unfold tailWord_1968096
  simp only [CollatzResearch.WordTrace]
  refine ⟨35891179138965895440854071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47854905518621193921138761 35891179138965895440854071)
  ·
    refine ⟨53836768708448843161281107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35891179138965895440854071 53836768708448843161281107)
    ·
      refine ⟨80755153062673264741921661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53836768708448843161281107 80755153062673264741921661)
      ·
        refine ⟨30283182398502474278220623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80755153062673264741921661 30283182398502474278220623)
        ·
          refine ⟨45424773597753711417330935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30283182398502474278220623 45424773597753711417330935)
          ·
            refine ⟨68137160396630567125996403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45424773597753711417330935 68137160396630567125996403)
            ·
              refine ⟨102205740594945850688994605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68137160396630567125996403 102205740594945850688994605)
              ·
                refine ⟨38327152723104694008372977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102205740594945850688994605 38327152723104694008372977)
                ·
                  refine ⟨28745364542328520506279733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38327152723104694008372977 28745364542328520506279733)
                  ·
                    refine ⟨2694877925843298797463725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28745364542328520506279733 2694877925843298797463725)
                    ·
                      refine ⟨1010579222191237049048897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2694877925843298797463725 1010579222191237049048897)
                      ·
                        rfl

theorem cell23_1968096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_1968096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968096 prefixEnd_1968096 := by exact prefixLift 1968096
  have htrace : WordTrace (prefixWord ++ tailWord_1968096) baseStart_1968096 baseEnd_1968096 := by
    simpa [prefixWord, tailWord_1968096, baseEnd_1968096] using wordTrace_append hprefix tailTrace_1968096
  have hstable : (prefixWord ++ tailWord_1968096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968096).length < 2 ^ (prefixWord ++ tailWord_1968096).sum := by decide
  have hdescent : baseEnd_1968096 < baseStart_1968096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968153 : List Nat := [1, 2, 1, 2, 1, 1, 3, 6, 1, 1, 4]
def baseStart_1968153 : Nat := 118140960795 + 1968153 * 2 ^ 59
def prefixEnd_1968153 : Nat := 4983230072969 + 3 ^ 40 * 1968153 * 2
def baseEnd_1968153 : Nat := 1010608490588543326036135

theorem tailTrace_1968153 : CollatzResearch.WordTrace tailWord_1968153 prefixEnd_1968153 1010608490588543326036135 := by
  unfold tailWord_1968153
  simp only [CollatzResearch.WordTrace]
  refine ⟨71784437238725289616533113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47856291492483526411022075 71784437238725289616533113)
  ·
    refine ⟨53838327929043967212399835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71784437238725289616533113 53838327929043967212399835)
    ·
      refine ⟨80757491893565950818599753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53838327929043967212399835 80757491893565950818599753)
      ·
        refine ⟨60568118920174463113949815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80757491893565950818599753 60568118920174463113949815)
        ·
          refine ⟨90852178380261694670924723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60568118920174463113949815 90852178380261694670924723)
          ·
            refine ⟨136278267570392542006387085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90852178380261694670924723 136278267570392542006387085)
            ·
              refine ⟨51104350338897203252395157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136278267570392542006387085 51104350338897203252395157)
              ·
                refine ⟨2395516422135806402456023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51104350338897203252395157 2395516422135806402456023)
                ·
                  refine ⟨3593274633203709603684035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2395516422135806402456023 3593274633203709603684035)
                  ·
                    refine ⟨5389911949805564405526053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3593274633203709603684035 5389911949805564405526053)
                    ·
                      refine ⟨1010608490588543326036135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5389911949805564405526053 1010608490588543326036135)
                      ·
                        rfl

theorem cell23_1968153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 1, 4].length) (baseStart_1968153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968153 prefixEnd_1968153 := by exact prefixLift 1968153
  have htrace : WordTrace (prefixWord ++ tailWord_1968153) baseStart_1968153 baseEnd_1968153 := by
    simpa [prefixWord, tailWord_1968153, baseEnd_1968153] using wordTrace_append hprefix tailTrace_1968153
  have hstable : (prefixWord ++ tailWord_1968153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968153).length < 2 ^ (prefixWord ++ tailWord_1968153).sum := by decide
  have hdescent : baseEnd_1968153 < baseStart_1968153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968157 : List Nat := [1, 4, 2, 2, 2, 1, 3, 1, 2, 3, 2]
def baseStart_1968157 : Nat := 118140960795 + 1968157 * 2 ^ 59
def prefixEnd_1968157 : Nat := 4983230072969 + 3 ^ 40 * 1968157 * 2
def baseEnd_1968157 : Nat := 1010610544511161310386117

theorem tailTrace_1968157 : CollatzResearch.WordTrace tailWord_1968157 prefixEnd_1968157 1010610544511161310386117 := by
  unfold tailWord_1968157
  simp only [CollatzResearch.WordTrace]
  refine ⟨71784583130710798299678725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47856388753807198866452483 71784583130710798299678725)
  ·
    refine ⟨13459609337008274681189761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71784583130710798299678725 13459609337008274681189761)
    ·
      refine ⟨10094707002756206010892321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13459609337008274681189761 10094707002756206010892321)
      ·
        refine ⟨7571030252067154508169241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10094707002756206010892321 7571030252067154508169241)
        ·
          refine ⟨5678272689050365881126931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7571030252067154508169241 5678272689050365881126931)
          ·
            refine ⟨8517409033575548821690397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5678272689050365881126931 8517409033575548821690397)
            ·
              refine ⟨3194028387590830808133899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8517409033575548821690397 3194028387590830808133899)
              ·
                refine ⟨4791042581386246212200849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3194028387590830808133899 4791042581386246212200849)
                ·
                  refine ⟨3593281936039684659150637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4791042581386246212200849 3593281936039684659150637)
                  ·
                    refine ⟨1347480726014881747181489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3593281936039684659150637 1347480726014881747181489)
                    ·
                      refine ⟨1010610544511161310386117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1347480726014881747181489 1010610544511161310386117)
                      ·
                        rfl

theorem cell23_1968157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_1968157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968157 prefixEnd_1968157 := by exact prefixLift 1968157
  have htrace : WordTrace (prefixWord ++ tailWord_1968157) baseStart_1968157 baseEnd_1968157 := by
    simpa [prefixWord, tailWord_1968157, baseEnd_1968157] using wordTrace_append hprefix tailTrace_1968157
  have hstable : (prefixWord ++ tailWord_1968157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968157).length < 2 ^ (prefixWord ++ tailWord_1968157).sum := by decide
  have hdescent : baseEnd_1968157 < baseStart_1968157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968163 : List Nat := [1, 1, 1, 4, 3, 1, 2, 2, 4, 4]
def baseStart_1968163 : Nat := 118140960795 + 1968163 * 2 ^ 59
def prefixEnd_1968163 : Nat := 4983230072969 + 3 ^ 40 * 1968163 * 2
def baseEnd_1968163 : Nat := 336871208465029428970363

theorem tailTrace_1968163 : CollatzResearch.WordTrace tailWord_1968163 prefixEnd_1968163 336871208465029428970363 := by
  unfold tailWord_1968163
  simp only [CollatzResearch.WordTrace]
  refine ⟨71784801968689061324397143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47856534645792707549598095 71784801968689061324397143)
  ·
    refine ⟨107677202953033591986595715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71784801968689061324397143 107677202953033591986595715)
    ·
      refine ⟨161515804429550387979893573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107677202953033591986595715 161515804429550387979893573)
      ·
        refine ⟨30284213330540697746230045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161515804429550387979893573 30284213330540697746230045)
        ·
          refine ⟨11356579998952761654836267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30284213330540697746230045 11356579998952761654836267)
          ·
            refine ⟨17034869998429142482254401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11356579998952761654836267 17034869998429142482254401)
            ·
              refine ⟨12776152498821856861690801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17034869998429142482254401 12776152498821856861690801)
              ·
                refine ⟨9582114374116392646268101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12776152498821856861690801 9582114374116392646268101)
                ·
                  refine ⟨1796646445146823621175269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9582114374116392646268101 1796646445146823621175269)
                  ·
                    refine ⟨336871208465029428970363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1796646445146823621175269 336871208465029428970363)
                    ·
                      rfl

theorem cell23_1968163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 4, 4].length) (baseStart_1968163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968163 prefixEnd_1968163 := by exact prefixLift 1968163
  have htrace : WordTrace (prefixWord ++ tailWord_1968163) baseStart_1968163 baseEnd_1968163 := by
    simpa [prefixWord, tailWord_1968163, baseEnd_1968163] using wordTrace_append hprefix tailTrace_1968163
  have hstable : (prefixWord ++ tailWord_1968163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968163).length < 2 ^ (prefixWord ++ tailWord_1968163).sum := by decide
  have hdescent : baseEnd_1968163 < baseStart_1968163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968167 : List Nat := [1, 1, 7, 1, 2, 1, 1, 3, 1, 5]
def baseStart_1968167 : Nat := 118140960795 + 1968167 * 2 ^ 59
def prefixEnd_1968167 : Nat := 4983230072969 + 3 ^ 40 * 1968167 * 2
def baseEnd_1968167 : Nat := 336871893105902090420357

theorem tailTrace_1968167 : CollatzResearch.WordTrace tailWord_1968167 prefixEnd_1968167 336871893105902090420357 := by
  unfold tailWord_1968167
  simp only [CollatzResearch.WordTrace]
  refine ⟨71784947860674570007542755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47856631907116380005028503 71784947860674570007542755)
  ·
    refine ⟨107677421791011855011314133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71784947860674570007542755 107677421791011855011314133)
    ·
      refine ⟨2523689573226840351827675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 107677421791011855011314133 2523689573226840351827675)
      ·
        refine ⟨3785534359840260527741513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2523689573226840351827675 3785534359840260527741513)
        ·
          refine ⟨2839150769880195395806135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3785534359840260527741513 2839150769880195395806135)
          ·
            refine ⟨4258726154820293093709203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2839150769880195395806135 4258726154820293093709203)
            ·
              refine ⟨6388089232230439640563805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4258726154820293093709203 6388089232230439640563805)
              ·
                refine ⟨2395533462086414865211427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6388089232230439640563805 2395533462086414865211427)
                ·
                  refine ⟨3593300193129622297817141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2395533462086414865211427 3593300193129622297817141)
                  ·
                    refine ⟨336871893105902090420357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3593300193129622297817141 336871893105902090420357)
                    ·
                      rfl

theorem cell23_1968167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_1968167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968167 prefixEnd_1968167 := by exact prefixLift 1968167
  have htrace : WordTrace (prefixWord ++ tailWord_1968167) baseStart_1968167 baseEnd_1968167 := by
    simpa [prefixWord, tailWord_1968167, baseEnd_1968167] using wordTrace_append hprefix tailTrace_1968167
  have hstable : (prefixWord ++ tailWord_1968167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968167).length < 2 ^ (prefixWord ++ tailWord_1968167).sum := by decide
  have hdescent : baseEnd_1968167 < baseStart_1968167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968176 : List Nat := [2, 1, 1, 1, 2, 6, 10]
def baseStart_1968176 : Nat := 118140960795 + 1968176 * 2 ^ 59
def prefixEnd_1968176 : Nat := 4983230072969 + 3 ^ 40 * 1968176 * 2
def baseEnd_1968176 : Nat := 12476793835106132543809

theorem tailTrace_1968176 : CollatzResearch.WordTrace tailWord_1968176 prefixEnd_1968176 12476793835106132543809 := by
  unfold tailWord_1968176
  simp only [CollatzResearch.WordTrace]
  refine ⟨35892638058820982272310191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47856850745094643029746921 35892638058820982272310191)
  ·
    refine ⟨53838957088231473408465287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35892638058820982272310191 53838957088231473408465287)
    ·
      refine ⟨80758435632347210112697931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53838957088231473408465287 80758435632347210112697931)
      ·
        refine ⟨121137653448520815169046897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80758435632347210112697931 121137653448520815169046897)
        ·
          refine ⟨90853240086390611376785173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121137653448520815169046897 90853240086390611376785173)
          ·
            refine ⟨4258745629049559908286805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90853240086390611376785173 4258745629049559908286805)
            ·
              refine ⟨12476793835106132543809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4258745629049559908286805 12476793835106132543809)
              ·
                rfl

theorem cell23_1968176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 10].length) (baseStart_1968176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968176 prefixEnd_1968176 := by exact prefixLift 1968176
  have htrace : WordTrace (prefixWord ++ tailWord_1968176) baseStart_1968176 baseEnd_1968176 := by
    simpa [prefixWord, tailWord_1968176, baseEnd_1968176] using wordTrace_append hprefix tailTrace_1968176
  have hstable : (prefixWord ++ tailWord_1968176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968176).length < 2 ^ (prefixWord ++ tailWord_1968176).sum := by decide
  have hdescent : baseEnd_1968176 < baseStart_1968176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968186 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 2, 2, 7]
def baseStart_1968186 : Nat := 118140960795 + 1968186 * 2 ^ 59
def prefixEnd_1968186 : Nat := 4983230072969 + 3 ^ 40 * 1968186 * 2
def baseEnd_1968186 : Nat := 1010625435450141696923483

theorem tailTrace_1968186 : CollatzResearch.WordTrace tailWord_1968186 prefixEnd_1968186 1010625435450141696923483 := by
  unfold tailWord_1968186
  simp only [CollatzResearch.WordTrace]
  refine ⟨17946410211901434063121103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47857093898403824168322941 17946410211901434063121103)
  ·
    refine ⟨26919615317852151094681655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17946410211901434063121103 26919615317852151094681655)
    ·
      refine ⟨40379422976778226642022483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26919615317852151094681655 40379422976778226642022483)
      ·
        refine ⟨60569134465167339963033725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40379422976778226642022483 60569134465167339963033725)
        ·
          refine ⟨22713425424437752486137647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60569134465167339963033725 22713425424437752486137647)
          ·
            refine ⟨34070138136656628729206471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22713425424437752486137647 34070138136656628729206471)
            ·
              refine ⟨51105207204984943093809707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34070138136656628729206471 51105207204984943093809707)
              ·
                refine ⟨76657810807477414640714561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51105207204984943093809707 76657810807477414640714561)
                ·
                  refine ⟨57493358105608060980535921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76657810807477414640714561 57493358105608060980535921)
                  ·
                    refine ⟨43120018579206045735401941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57493358105608060980535921 43120018579206045735401941)
                    ·
                      refine ⟨1010625435450141696923483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 43120018579206045735401941 1010625435450141696923483)
                      ·
                        rfl

theorem cell23_1968186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_1968186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968186 prefixEnd_1968186 := by exact prefixLift 1968186
  have htrace : WordTrace (prefixWord ++ tailWord_1968186) baseStart_1968186 baseEnd_1968186 := by
    simpa [prefixWord, tailWord_1968186, baseEnd_1968186] using wordTrace_append hprefix tailTrace_1968186
  have hstable : (prefixWord ++ tailWord_1968186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968186).length < 2 ^ (prefixWord ++ tailWord_1968186).sum := by decide
  have hdescent : baseEnd_1968186 < baseStart_1968186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968237 : List Nat := [1, 5, 1, 1, 2, 1, 2, 4, 2, 1, 3]
def baseStart_1968237 : Nat := 118140960795 + 1968237 * 2 ^ 59
def prefixEnd_1968237 : Nat := 4983230072969 + 3 ^ 40 * 1968237 * 2
def baseEnd_1968237 : Nat := 1010651622963520997385749

theorem tailTrace_1968237 : CollatzResearch.WordTrace tailWord_1968237 prefixEnd_1968237 1010651622963520997385749 := by
  unfold tailWord_1968237
  simp only [CollatzResearch.WordTrace]
  refine ⟨71787500970420971962590965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47858333980280647975060643 71787500970420971962590965)
  ·
    refine ⟨6730078215976966121492903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71787500970420971962590965 6730078215976966121492903)
    ·
      refine ⟨10095117323965449182239355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6730078215976966121492903 10095117323965449182239355)
      ·
        refine ⟨15142675985948173773359033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10095117323965449182239355 15142675985948173773359033)
        ·
          refine ⟨11357006989461130330019275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15142675985948173773359033 11357006989461130330019275)
          ·
            refine ⟨17035510484191695495028913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11357006989461130330019275 17035510484191695495028913)
            ·
              refine ⟨12776632863143771621271685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17035510484191695495028913 12776632863143771621271685)
              ·
                refine ⟨2395618661839457178988441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12776632863143771621271685 2395618661839457178988441)
                ·
                  refine ⟨1796713996379592884241331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2395618661839457178988441 1796713996379592884241331)
                  ·
                    refine ⟨2695070994569389326361997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1796713996379592884241331 2695070994569389326361997)
                    ·
                      refine ⟨1010651622963520997385749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2695070994569389326361997 1010651622963520997385749)
                      ·
                        rfl

theorem cell23_1968237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_1968237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968237 prefixEnd_1968237 := by exact prefixLift 1968237
  have htrace : WordTrace (prefixWord ++ tailWord_1968237) baseStart_1968237 baseEnd_1968237 := by
    simpa [prefixWord, tailWord_1968237, baseEnd_1968237] using wordTrace_append hprefix tailTrace_1968237
  have hstable : (prefixWord ++ tailWord_1968237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968237).length < 2 ^ (prefixWord ++ tailWord_1968237).sum := by decide
  have hdescent : baseEnd_1968237 < baseStart_1968237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968263 : List Nat := [1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 5]
def baseStart_1968263 : Nat := 118140960795 + 1968263 * 2 ^ 59
def prefixEnd_1968263 : Nat := 4983230072969 + 3 ^ 40 * 1968263 * 2
def baseEnd_1968263 : Nat := 1010664973460537895660629

theorem tailTrace_1968263 : CollatzResearch.WordTrace tailWord_1968263 prefixEnd_1968263 1010664973460537895660629 := by
  unfold tailWord_1968263
  simp only [CollatzResearch.WordTrace]
  refine ⟨71788449268326778403037443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47858966178884518935358295 71788449268326778403037443)
  ·
    refine ⟨107682673902490167604556165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71788449268326778403037443 107682673902490167604556165)
    ·
      refine ⟨20190501356716906425854281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107682673902490167604556165 20190501356716906425854281)
      ·
        refine ⟨15142876017537679819390711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20190501356716906425854281 15142876017537679819390711)
        ·
          refine ⟨22714314026306519729086067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15142876017537679819390711 22714314026306519729086067)
          ·
            refine ⟨34071471039459779593629101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22714314026306519729086067 34071471039459779593629101)
            ·
              refine ⟨12776801639797417347610913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34071471039459779593629101 12776801639797417347610913)
              ·
                refine ⟨9582601229848063010708185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12776801639797417347610913 9582601229848063010708185)
                ·
                  refine ⟨7186950922386047258031139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9582601229848063010708185 7186950922386047258031139)
                  ·
                    refine ⟨10780426383579070887046709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7186950922386047258031139 10780426383579070887046709)
                    ·
                      refine ⟨1010664973460537895660629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10780426383579070887046709 1010664973460537895660629)
                      ·
                        rfl

theorem cell23_1968263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_1968263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968263 prefixEnd_1968263 := by exact prefixLift 1968263
  have htrace : WordTrace (prefixWord ++ tailWord_1968263) baseStart_1968263 baseEnd_1968263 := by
    simpa [prefixWord, tailWord_1968263, baseEnd_1968263] using wordTrace_append hprefix tailTrace_1968263
  have hstable : (prefixWord ++ tailWord_1968263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968263).length < 2 ^ (prefixWord ++ tailWord_1968263).sum := by decide
  have hdescent : baseEnd_1968263 < baseStart_1968263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968264 : List Nat := [2, 1, 3, 4, 1, 1, 3, 2, 1, 3, 2]
def baseStart_1968264 : Nat := 118140960795 + 1968264 * 2 ^ 59
def prefixEnd_1968264 : Nat := 4983230072969 + 3 ^ 40 * 1968264 * 2
def baseEnd_1968264 : Nat := 1010665486941192391748125

theorem tailTrace_1968264 : CollatzResearch.WordTrace tailWord_1968264 prefixEnd_1968264 1010665486941192391748125 := by
  unfold tailWord_1968264
  simp only [CollatzResearch.WordTrace]
  refine ⟨35894242870661577786911923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47858990494215437049215897 35894242870661577786911923)
  ·
    refine ⟨53841364305992366680367885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35894242870661577786911923 53841364305992366680367885)
    ·
      refine ⟨20190511614747137505137957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53841364305992366680367885 20190511614747137505137957)
      ·
        refine ⟨3785720927765088282213367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20190511614747137505137957 3785720927765088282213367)
        ·
          refine ⟨5678581391647632423320051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3785720927765088282213367 5678581391647632423320051)
          ·
            refine ⟨8517872087471448634980077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5678581391647632423320051 8517872087471448634980077)
            ·
              refine ⟨3194202032801793238117529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8517872087471448634980077 3194202032801793238117529)
              ·
                refine ⟨2395651524601344928588147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3194202032801793238117529 2395651524601344928588147)
                ·
                  refine ⟨3593477286902017392882221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2395651524601344928588147 3593477286902017392882221)
                  ·
                    refine ⟨1347553982588256522330833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3593477286902017392882221 1347553982588256522330833)
                    ·
                      refine ⟨1010665486941192391748125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1347553982588256522330833 1010665486941192391748125)
                      ·
                        rfl

theorem cell23_1968264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_1968264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968264 prefixEnd_1968264 := by exact prefixLift 1968264
  have htrace : WordTrace (prefixWord ++ tailWord_1968264) baseStart_1968264 baseEnd_1968264 := by
    simpa [prefixWord, tailWord_1968264, baseEnd_1968264] using wordTrace_append hprefix tailTrace_1968264
  have hstable : (prefixWord ++ tailWord_1968264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968264).length < 2 ^ (prefixWord ++ tailWord_1968264).sum := by decide
  have hdescent : baseEnd_1968264 < baseStart_1968264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968313 : List Nat := [1, 2, 1, 4, 1, 2, 2, 2, 1, 7]
def baseStart_1968313 : Nat := 118140960795 + 1968313 * 2 ^ 59
def prefixEnd_1968313 : Nat := 4983230072969 + 3 ^ 40 * 1968313 * 2
def baseEnd_1968313 : Nat := 336896882497754233345133

theorem tailTrace_1968313 : CollatzResearch.WordTrace tailWord_1968313 prefixEnd_1968313 336896882497754233345133 := by
  unfold tailWord_1968313
  simp only [CollatzResearch.WordTrace]
  refine ⟨71790272918145636942357593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47860181945430424628238395 71790272918145636942357593)
  ·
    refine ⟨53842704688609227706768195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71790272918145636942357593 53842704688609227706768195)
    ·
      refine ⟨80764057032913841560152293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53842704688609227706768195 80764057032913841560152293)
      ·
        refine ⟨15143260693671345292528555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80764057032913841560152293 15143260693671345292528555)
        ·
          refine ⟨22714891040507017938792833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15143260693671345292528555 22714891040507017938792833)
          ·
            refine ⟨17036168280380263454094625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22714891040507017938792833 17036168280380263454094625)
            ·
              refine ⟨12777126210285197590570969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17036168280380263454094625 12777126210285197590570969)
              ·
                refine ⟨9582844657713898192928227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12777126210285197590570969 9582844657713898192928227)
                ·
                  refine ⟨14374266986570847289392341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9582844657713898192928227 14374266986570847289392341)
                  ·
                    refine ⟨336896882497754233345133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14374266986570847289392341 336896882497754233345133)
                    ·
                      rfl

theorem cell23_1968313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 7].length) (baseStart_1968313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968313 prefixEnd_1968313 := by exact prefixLift 1968313
  have htrace : WordTrace (prefixWord ++ tailWord_1968313) baseStart_1968313 baseEnd_1968313 := by
    simpa [prefixWord, tailWord_1968313, baseEnd_1968313] using wordTrace_append hprefix tailTrace_1968313
  have hstable : (prefixWord ++ tailWord_1968313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968313).length < 2 ^ (prefixWord ++ tailWord_1968313).sum := by decide
  have hdescent : baseEnd_1968313 < baseStart_1968313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968363 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 6]
def baseStart_1968363 : Nat := 118140960795 + 1968363 * 2 ^ 59
def prefixEnd_1968363 : Nat := 4983230072969 + 3 ^ 40 * 1968363 * 2
def baseEnd_1968363 : Nat := 1010716321525987504410169

theorem tailTrace_1968363 : CollatzResearch.WordTrace tailWord_1968363 prefixEnd_1968363 1010716321525987504410169 := by
  unfold tailWord_1968363
  simp only [CollatzResearch.WordTrace]
  refine ⟨71792096567964495481677743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47861397711976330321118495 71792096567964495481677743)
  ·
    refine ⟨107688144851946743222516615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71792096567964495481677743 107688144851946743222516615)
    ·
      refine ⟨161532217277920114833774923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107688144851946743222516615 161532217277920114833774923)
      ·
        refine ⟨242298325916880172250662385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161532217277920114833774923 242298325916880172250662385)
        ·
          refine ⟨181723744437660129187996789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242298325916880172250662385 181723744437660129187996789)
          ·
            refine ⟨17036601041030637111374699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 181723744437660129187996789 17036601041030637111374699)
            ·
              refine ⟨25554901561545955667062049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17036601041030637111374699 25554901561545955667062049)
              ·
                refine ⟨19166176171159466750296537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25554901561545955667062049 19166176171159466750296537)
                ·
                  refine ⟨14374632128369600062722403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19166176171159466750296537 14374632128369600062722403)
                  ·
                    refine ⟨21561948192554400094083605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14374632128369600062722403 21561948192554400094083605)
                    ·
                      refine ⟨1010716321525987504410169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21561948192554400094083605 1010716321525987504410169)
                      ·
                        rfl

theorem cell23_1968363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 6].length) (baseStart_1968363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968363 prefixEnd_1968363 := by exact prefixLift 1968363
  have htrace : WordTrace (prefixWord ++ tailWord_1968363) baseStart_1968363 baseEnd_1968363 := by
    simpa [prefixWord, tailWord_1968363, baseEnd_1968363] using wordTrace_append hprefix tailTrace_1968363
  have hstable : (prefixWord ++ tailWord_1968363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968363).length < 2 ^ (prefixWord ++ tailWord_1968363).sum := by decide
  have hdescent : baseEnd_1968363 < baseStart_1968363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968367 : List Nat := [1, 1, 2, 1, 6, 1, 2, 1, 2, 4, 2]
def baseStart_1968367 : Nat := 118140960795 + 1968367 * 2 ^ 59
def prefixEnd_1968367 : Nat := 4983230072969 + 3 ^ 40 * 1968367 * 2
def baseEnd_1968367 : Nat := 1010718375448605488760151

theorem tailTrace_1968367 : CollatzResearch.WordTrace tailWord_1968367 prefixEnd_1968367 1010718375448605488760151 := by
  unfold tailWord_1968367
  simp only [CollatzResearch.WordTrace]
  refine ⟨71792242459950004164823355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47861494973300002776548903 71792242459950004164823355)
  ·
    refine ⟨107688363689925006247235033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71792242459950004164823355 107688363689925006247235033)
    ·
      refine ⟨80766272767443754685426275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107688363689925006247235033 80766272767443754685426275)
      ·
        refine ⟨121149409151165632028139413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80766272767443754685426275 121149409151165632028139413)
        ·
          refine ⟨5678878553960889001319035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121149409151165632028139413 5678878553960889001319035)
          ·
            refine ⟨8518317830941333501978553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5678878553960889001319035 8518317830941333501978553)
            ·
              refine ⟨6388738373206000126483915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8518317830941333501978553 6388738373206000126483915)
              ·
                refine ⟨9583107559809000189725873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6388738373206000126483915 9583107559809000189725873)
                ·
                  refine ⟨7187330669856750142294405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9583107559809000189725873 7187330669856750142294405)
                  ·
                    refine ⟨1347624500598140651680201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7187330669856750142294405 1347624500598140651680201)
                    ·
                      refine ⟨1010718375448605488760151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1347624500598140651680201 1010718375448605488760151)
                      ·
                        rfl

theorem cell23_1968367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 4, 2].length) (baseStart_1968367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968367 prefixEnd_1968367 := by exact prefixLift 1968367
  have htrace : WordTrace (prefixWord ++ tailWord_1968367) baseStart_1968367 baseEnd_1968367 := by
    simpa [prefixWord, tailWord_1968367, baseEnd_1968367] using wordTrace_append hprefix tailTrace_1968367
  have hstable : (prefixWord ++ tailWord_1968367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968367).length < 2 ^ (prefixWord ++ tailWord_1968367).sum := by decide
  have hdescent : baseEnd_1968367 < baseStart_1968367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968394 : List Nat := [3, 1, 2, 2, 1, 1, 5, 3, 1, 4]
def baseStart_1968394 : Nat := 118140960795 + 1968394 * 2 ^ 59
def prefixEnd_1968394 : Nat := 4983230072969 + 3 ^ 40 * 1968394 * 2
def baseEnd_1968394 : Nat := 336910746475425627707509

theorem tailTrace_1968394 : CollatzResearch.WordTrace tailWord_1968394 prefixEnd_1968394 336910746475425627707509 := by
  unfold tailWord_1968394
  simp only [CollatzResearch.WordTrace]
  refine ⟨17948306807713046944014059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47862151487234791850704157 17948306807713046944014059)
  ·
    refine ⟨26922460211569570416021089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17948306807713046944014059 26922460211569570416021089)
    ·
      refine ⟨20191845158677177812015817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26922460211569570416021089 20191845158677177812015817)
      ·
        refine ⟨15143883869007883359011863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20191845158677177812015817 15143883869007883359011863)
        ·
          refine ⟨22715825803511825038517795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15143883869007883359011863 22715825803511825038517795)
          ·
            refine ⟨34073738705267737557776693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22715825803511825038517795 34073738705267737557776693)
            ·
              refine ⟨3194413003618850396041565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34073738705267737557776693 3194413003618850396041565)
              ·
                refine ⟨1197904876357068898515587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3194413003618850396041565 1197904876357068898515587)
                ·
                  refine ⟨1796857314535603347773381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1197904876357068898515587 1796857314535603347773381)
                  ·
                    refine ⟨336910746475425627707509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1796857314535603347773381 336910746475425627707509)
                    ·
                      rfl

theorem cell23_1968394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_1968394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968394 prefixEnd_1968394 := by exact prefixLift 1968394
  have htrace : WordTrace (prefixWord ++ tailWord_1968394) baseStart_1968394 baseEnd_1968394 := by
    simpa [prefixWord, tailWord_1968394, baseEnd_1968394] using wordTrace_append hprefix tailTrace_1968394
  have hstable : (prefixWord ++ tailWord_1968394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968394).length < 2 ^ (prefixWord ++ tailWord_1968394).sum := by decide
  have hdescent : baseEnd_1968394 < baseStart_1968394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968443 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 11]
def baseStart_1968443 : Nat := 118140960795 + 1968443 * 2 ^ 59
def prefixEnd_1968443 : Nat := 4983230072969 + 3 ^ 40 * 1968443 * 2
def baseEnd_1968443 : Nat := 1010757399978347191409801

theorem tailTrace_1968443 : CollatzResearch.WordTrace tailWord_1968443 prefixEnd_1968443 1010757399978347191409801 := by
  unfold tailWord_1968443
  simp only [CollatzResearch.WordTrace]
  refine ⟨71795014407674669144589983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47863342938449779429726655 71795014407674669144589983)
  ·
    refine ⟨107692521611512003716884975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71795014407674669144589983 107692521611512003716884975)
    ·
      refine ⟨161538782417268005575327463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107692521611512003716884975 161538782417268005575327463)
      ·
        refine ⟨242308173625902008362991195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161538782417268005575327463 242308173625902008362991195)
        ·
          refine ⟨363462260438853012544486793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242308173625902008362991195 363462260438853012544486793)
          ·
            refine ⟨272596695329139759408365095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363462260438853012544486793 272596695329139759408365095)
            ·
              refine ⟨408895042993709639112547643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272596695329139759408365095 408895042993709639112547643)
              ·
                refine ⟨613342564490564458668821465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408895042993709639112547643 613342564490564458668821465)
                ·
                  refine ⟨460006923367923344001616099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 613342564490564458668821465 460006923367923344001616099)
                  ·
                    refine ⟨690010385051885016002424149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 460006923367923344001616099 690010385051885016002424149)
                    ·
                      refine ⟨1010757399978347191409801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 690010385051885016002424149 1010757399978347191409801)
                      ·
                        rfl

theorem cell23_1968443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 11].length) (baseStart_1968443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968443 prefixEnd_1968443 := by exact prefixLift 1968443
  have htrace : WordTrace (prefixWord ++ tailWord_1968443) baseStart_1968443 baseEnd_1968443 := by
    simpa [prefixWord, tailWord_1968443, baseEnd_1968443] using wordTrace_append hprefix tailTrace_1968443
  have hstable : (prefixWord ++ tailWord_1968443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968443).length < 2 ^ (prefixWord ++ tailWord_1968443).sum := by decide
  have hdescent : baseEnd_1968443 < baseStart_1968443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968444 : List Nat := [2, 2, 2, 2, 1, 2, 4, 1, 2, 3, 2]
def baseStart_1968444 : Nat := 118140960795 + 1968444 * 2 ^ 59
def prefixEnd_1968444 : Nat := 4983230072969 + 3 ^ 40 * 1968444 * 2
def baseEnd_1968444 : Nat := 1010757913459001687497297

theorem tailTrace_1968444 : CollatzResearch.WordTrace tailWord_1968444 prefixEnd_1968444 1010757913459001687497297 := by
  unfold tailWord_1968444
  simp only [CollatzResearch.WordTrace]
  refine ⟨35897525440335523157688193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47863367253780697543584257 35897525440335523157688193)
  ·
    refine ⟨26923144080251642368266145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35897525440335523157688193 26923144080251642368266145)
    ·
      refine ⟨20192358060188731776199609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26923144080251642368266145 20192358060188731776199609)
      ·
        refine ⟨15144268545141548832149707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20192358060188731776199609 15144268545141548832149707)
        ·
          refine ⟨22716402817712323248224561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15144268545141548832149707 22716402817712323248224561)
          ·
            refine ⟨17037302113284242436168421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22716402817712323248224561 17037302113284242436168421)
            ·
              refine ⟨3194494146240795456781579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17037302113284242436168421 3194494146240795456781579)
              ·
                refine ⟨4791741219361193185172369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3194494146240795456781579 4791741219361193185172369)
                ·
                  refine ⟨3593805914520894888879277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4791741219361193185172369 3593805914520894888879277)
                  ·
                    refine ⟨1347677217945335583329729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3593805914520894888879277 1347677217945335583329729)
                    ·
                      refine ⟨1010757913459001687497297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1347677217945335583329729 1010757913459001687497297)
                      ·
                        rfl

theorem cell23_1968444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_1968444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968444 prefixEnd_1968444 := by exact prefixLift 1968444
  have htrace : WordTrace (prefixWord ++ tailWord_1968444) baseStart_1968444 baseEnd_1968444 := by
    simpa [prefixWord, tailWord_1968444, baseEnd_1968444] using wordTrace_append hprefix tailTrace_1968444
  have hstable : (prefixWord ++ tailWord_1968444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968444).length < 2 ^ (prefixWord ++ tailWord_1968444).sum := by decide
  have hdescent : baseEnd_1968444 < baseStart_1968444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968468 : List Nat := [2, 4, 1, 1, 2, 2, 4, 2, 1, 1, 3]
def baseStart_1968468 : Nat := 118140960795 + 1968468 * 2 ^ 59
def prefixEnd_1968468 : Nat := 4983230072969 + 3 ^ 40 * 1968468 * 2
def baseEnd_1968468 : Nat := 1010770236994709593597187

theorem tailTrace_1968468 : CollatzResearch.WordTrace tailWord_1968468 prefixEnd_1968468 1010770236994709593597187 := by
  unfold tailWord_1968468
  simp only [CollatzResearch.WordTrace]
  refine ⟨35897963116292049207125029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47863950821722732276166705 35897963116292049207125029)
  ·
    refine ⟨6730868084304759226335943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35897963116292049207125029 6730868084304759226335943)
    ·
      refine ⟨10096302126457138839503915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6730868084304759226335943 10096302126457138839503915)
      ·
        refine ⟨15144453189685708259255873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10096302126457138839503915 15144453189685708259255873)
        ·
          refine ⟨11358339892264281194441905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15144453189685708259255873 11358339892264281194441905)
          ·
            refine ⟨8518754919198210895831429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11358339892264281194441905 8518754919198210895831429)
            ·
              refine ⟨1597266547349664542968393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8518754919198210895831429 1597266547349664542968393)
              ·
                refine ⟨1197949910512248407226295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1597266547349664542968393 1197949910512248407226295)
                ·
                  refine ⟨1796924865768372610839443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1197949910512248407226295 1796924865768372610839443)
                  ·
                    refine ⟨2695387298652558916259165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1796924865768372610839443 2695387298652558916259165)
                    ·
                      refine ⟨1010770236994709593597187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2695387298652558916259165 1010770236994709593597187)
                      ·
                        rfl

theorem cell23_1968468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_1968468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968468 prefixEnd_1968468 := by exact prefixLift 1968468
  have htrace : WordTrace (prefixWord ++ tailWord_1968468) baseStart_1968468 baseEnd_1968468 := by
    simpa [prefixWord, tailWord_1968468, baseEnd_1968468] using wordTrace_append hprefix tailTrace_1968468
  have hstable : (prefixWord ++ tailWord_1968468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968468).length < 2 ^ (prefixWord ++ tailWord_1968468).sum := by decide
  have hdescent : baseEnd_1968468 < baseStart_1968468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968474 : List Nat := [3, 1, 1, 2, 1, 2, 1, 5, 3, 2, 2]
def baseStart_1968474 : Nat := 118140960795 + 1968474 * 2 ^ 59
def prefixEnd_1968474 : Nat := 4983230072969 + 3 ^ 40 * 1968474 * 2
def baseEnd_1968474 : Nat := 1010773317878636570122159

theorem tailTrace_1968474 : CollatzResearch.WordTrace tailWord_1968474 prefixEnd_1968474 1010773317878636570122159 := by
  unfold tailWord_1968474
  simp only [CollatzResearch.WordTrace]
  refine ⟨17949036267640590359742119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47864096713708240959312317 17949036267640590359742119)
  ·
    refine ⟨26923554401460885539613179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17949036267640590359742119 26923554401460885539613179)
    ·
      refine ⟨40385331602191328309419769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26923554401460885539613179 40385331602191328309419769)
      ·
        refine ⟨30288998701643496232064827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40385331602191328309419769 30288998701643496232064827)
        ·
          refine ⟨45433498052465244348097241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30288998701643496232064827 45433498052465244348097241)
          ·
            refine ⟨34075123539348933261072931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45433498052465244348097241 34075123539348933261072931)
            ·
              refine ⟨51112685309023399891609397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34075123539348933261072931 51112685309023399891609397)
              ·
                refine ⟨4791814247720943739838381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51112685309023399891609397 4791814247720943739838381)
                ·
                  refine ⟨1796930342895353902439393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4791814247720943739838381 1796930342895353902439393)
                  ·
                    refine ⟨1347697757171515426829545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1796930342895353902439393 1347697757171515426829545)
                    ·
                      refine ⟨1010773317878636570122159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1347697757171515426829545 1010773317878636570122159)
                      ·
                        rfl

theorem cell23_1968474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 3, 2, 2].length) (baseStart_1968474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968474 prefixEnd_1968474 := by exact prefixLift 1968474
  have htrace : WordTrace (prefixWord ++ tailWord_1968474) baseStart_1968474 baseEnd_1968474 := by
    simpa [prefixWord, tailWord_1968474, baseEnd_1968474] using wordTrace_append hprefix tailTrace_1968474
  have hstable : (prefixWord ++ tailWord_1968474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968474).length < 2 ^ (prefixWord ++ tailWord_1968474).sum := by decide
  have hdescent : baseEnd_1968474 < baseStart_1968474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968487 : List Nat := [1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 4]
def baseStart_1968487 : Nat := 118140960795 + 1968487 * 2 ^ 59
def prefixEnd_1968487 : Nat := 4983230072969 + 3 ^ 40 * 1968487 * 2
def baseEnd_1968487 : Nat := 1010779993127145019259599

theorem tailTrace_1968487 : CollatzResearch.WordTrace tailWord_1968487 prefixEnd_1968487 1010779993127145019259599 := by
  unfold tailWord_1968487
  simp only [CollatzResearch.WordTrace]
  refine ⟨71796619219515264659191715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47864412813010176439461143 71796619219515264659191715)
  ·
    refine ⟨107694928829272896988787573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71796619219515264659191715 107694928829272896988787573)
    ·
      refine ⟨10096399577744334092698835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107694928829272896988787573 10096399577744334092698835)
      ·
        refine ⟨15144599366616501139048253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10096399577744334092698835 15144599366616501139048253)
        ·
          refine ⟨5679224762481187927143095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15144599366616501139048253 5679224762481187927143095)
          ·
            refine ⟨8518837143721781890714643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5679224762481187927143095 8518837143721781890714643)
            ·
              refine ⟨12778255715582672836071965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8518837143721781890714643 12778255715582672836071965)
              ·
                refine ⟨4791845893343502313526987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12778255715582672836071965 4791845893343502313526987)
                ·
                  refine ⟨7187768840015253470290481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4791845893343502313526987 7187768840015253470290481)
                  ·
                    refine ⟨5390826630011440102717861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7187768840015253470290481 5390826630011440102717861)
                    ·
                      refine ⟨1010779993127145019259599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5390826630011440102717861 1010779993127145019259599)
                      ·
                        rfl

theorem cell23_1968487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_1968487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968487 prefixEnd_1968487 := by exact prefixLift 1968487
  have htrace : WordTrace (prefixWord ++ tailWord_1968487) baseStart_1968487 baseEnd_1968487 := by
    simpa [prefixWord, tailWord_1968487, baseEnd_1968487] using wordTrace_append hprefix tailTrace_1968487
  have hstable : (prefixWord ++ tailWord_1968487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968487).length < 2 ^ (prefixWord ++ tailWord_1968487).sum := by decide
  have hdescent : baseEnd_1968487 < baseStart_1968487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968507 : List Nat := [1, 1, 1, 1, 1, 7, 2, 2, 1, 3, 3]
def baseStart_1968507 : Nat := 118140960795 + 1968507 * 2 ^ 59
def prefixEnd_1968507 : Nat := 4983230072969 + 3 ^ 40 * 1968507 * 2
def baseEnd_1968507 : Nat := 1010790262740234941009507

theorem tailTrace_1968507 : CollatzResearch.WordTrace tailWord_1968507 prefixEnd_1968507 1010790262740234941009507 := by
  unfold tailWord_1968507
  simp only [CollatzResearch.WordTrace]
  refine ⟨71797348679442808074919775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47864899119628538716613183 71797348679442808074919775)
  ·
    refine ⟨107696023019164212112379663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71797348679442808074919775 107696023019164212112379663)
    ·
      refine ⟨161544034528746318168569495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107696023019164212112379663 161544034528746318168569495)
      ·
        refine ⟨242316051793119477252854243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161544034528746318168569495 242316051793119477252854243)
        ·
          refine ⟨363474077689679215879281365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242316051793119477252854243 363474077689679215879281365)
          ·
            refine ⟨8518923695851856622170657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 363474077689679215879281365 8518923695851856622170657)
            ·
              refine ⟨6389192771888892466627993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8518923695851856622170657 6389192771888892466627993)
              ·
                refine ⟨4791894578916669349970995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6389192771888892466627993 4791894578916669349970995)
                ·
                  refine ⟨7187841868375004024956493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4791894578916669349970995 7187841868375004024956493)
                  ·
                    refine ⟨2695440700640626509358685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7187841868375004024956493 2695440700640626509358685)
                    ·
                      refine ⟨1010790262740234941009507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2695440700640626509358685 1010790262740234941009507)
                      ·
                        rfl

theorem cell23_1968507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 3, 3].length) (baseStart_1968507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968507 prefixEnd_1968507 := by exact prefixLift 1968507
  have htrace : WordTrace (prefixWord ++ tailWord_1968507) baseStart_1968507 baseEnd_1968507 := by
    simpa [prefixWord, tailWord_1968507, baseEnd_1968507] using wordTrace_append hprefix tailTrace_1968507
  have hstable : (prefixWord ++ tailWord_1968507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968507).length < 2 ^ (prefixWord ++ tailWord_1968507).sum := by decide
  have hdescent : baseEnd_1968507 < baseStart_1968507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968514 : List Nat := [3, 4, 2, 1, 2, 1, 10]
def baseStart_1968514 : Nat := 118140960795 + 1968514 * 2 ^ 59
def prefixEnd_1968514 : Nat := 4983230072969 + 3 ^ 40 * 1968514 * 2
def baseEnd_1968514 : Nat := 12478936507466869303975

theorem tailTrace_1968514 : CollatzResearch.WordTrace tailWord_1968514 prefixEnd_1968514 12478936507466869303975 := by
  unfold tailWord_1968514
  simp only [CollatzResearch.WordTrace]
  refine ⟨17949400997604362067606149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47865069326944965513616397 17949400997604362067606149)
  ·
    refine ⟨3365512687050817887676153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17949400997604362067606149 3365512687050817887676153)
    ·
      refine ⟨2524134515288113415757115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3365512687050817887676153 2524134515288113415757115)
      ·
        refine ⟨3786201772932170123635673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2524134515288113415757115 3786201772932170123635673)
        ·
          refine ⟨2839651329699127592726755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3786201772932170123635673 2839651329699127592726755)
          ·
            refine ⟨4259476994548691389090133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2839651329699127592726755 4259476994548691389090133)
            ·
              refine ⟨12478936507466869303975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4259476994548691389090133 12478936507466869303975)
              ·
                rfl

theorem cell23_1968514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 10].length) (baseStart_1968514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968514 prefixEnd_1968514 := by exact prefixLift 1968514
  have htrace : WordTrace (prefixWord ++ tailWord_1968514) baseStart_1968514 baseEnd_1968514 := by
    simpa [prefixWord, tailWord_1968514, baseEnd_1968514] using wordTrace_append hprefix tailTrace_1968514
  have hstable : (prefixWord ++ tailWord_1968514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968514).length < 2 ^ (prefixWord ++ tailWord_1968514).sum := by decide
  have hdescent : baseEnd_1968514 < baseStart_1968514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968524 : List Nat := [2, 2, 1, 2, 1, 5, 1, 1, 4, 1, 3]
def baseStart_1968524 : Nat := 118140960795 + 1968524 * 2 ^ 59
def prefixEnd_1968524 : Nat := 4983230072969 + 3 ^ 40 * 1968524 * 2
def baseEnd_1968524 : Nat := 1010798991911361374496929

theorem tailTrace_1968524 : CollatzResearch.WordTrace tailWord_1968524 prefixEnd_1968524 1010798991911361374496929 := by
  unfold tailWord_1968524
  simp only [CollatzResearch.WordTrace]
  refine ⟨35898984360190609989144313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47865312480254146652192417 35898984360190609989144313)
  ·
    refine ⟨26924238270142957491858235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35898984360190609989144313 26924238270142957491858235)
    ·
      refine ⟨40386357405214436237787353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26924238270142957491858235 40386357405214436237787353)
      ·
        refine ⟨30289768053910827178340515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40386357405214436237787353 30289768053910827178340515)
        ·
          refine ⟨45434652080866240767510773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30289768053910827178340515 45434652080866240767510773)
          ·
            refine ⟨4259498632581210071954135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45434652080866240767510773 4259498632581210071954135)
            ·
              refine ⟨6389247948871815107931203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4259498632581210071954135 6389247948871815107931203)
              ·
                refine ⟨9583871923307722661896805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6389247948871815107931203 9583871923307722661896805)
                ·
                  refine ⟨1796975985620197999105651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9583871923307722661896805 1796975985620197999105651)
                  ·
                    refine ⟨2695463978430296998658477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1796975985620197999105651 2695463978430296998658477)
                    ·
                      refine ⟨1010798991911361374496929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2695463978430296998658477 1010798991911361374496929)
                      ·
                        rfl

theorem cell23_1968524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_1968524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968524 prefixEnd_1968524 := by exact prefixLift 1968524
  have htrace : WordTrace (prefixWord ++ tailWord_1968524) baseStart_1968524 baseEnd_1968524 := by
    simpa [prefixWord, tailWord_1968524, baseEnd_1968524] using wordTrace_append hprefix tailTrace_1968524
  have hstable : (prefixWord ++ tailWord_1968524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968524).length < 2 ^ (prefixWord ++ tailWord_1968524).sum := by decide
  have hdescent : baseEnd_1968524 < baseStart_1968524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968541 : List Nat := [1, 4, 2, 1, 4, 2, 1, 1, 1, 3, 3]
def baseStart_1968541 : Nat := 118140960795 + 1968541 * 2 ^ 59
def prefixEnd_1968541 : Nat := 4983230072969 + 3 ^ 40 * 1968541 * 2
def baseEnd_1968541 : Nat := 1010807721082487807984351

theorem tailTrace_1968541 : CollatzResearch.WordTrace tailWord_1968541 prefixEnd_1968541 1010807721082487807984351 := by
  unfold tailWord_1968541
  simp only [CollatzResearch.WordTrace]
  refine ⟨71798588761319631881657477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47865725840879754587771651 71798588761319631881657477)
  ·
    refine ⟨13462235392747430977810777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71798588761319631881657477 13462235392747430977810777)
    ·
      refine ⟨10096676544560573233358083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13462235392747430977810777 10096676544560573233358083)
      ·
        refine ⟨15145014816840859850037125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10096676544560573233358083 15145014816840859850037125)
        ·
          refine ⟨2839690278157661221881961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15145014816840859850037125 2839690278157661221881961)
          ·
            refine ⟨2129767708618245916411471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2839690278157661221881961 2129767708618245916411471)
            ·
              refine ⟨3194651562927368874617207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2129767708618245916411471 3194651562927368874617207)
              ·
                refine ⟨4791977344391053311925811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3194651562927368874617207 4791977344391053311925811)
                ·
                  refine ⟨7187966016586579967888717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4791977344391053311925811 7187966016586579967888717)
                  ·
                    refine ⟨2695487256219967487958269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7187966016586579967888717 2695487256219967487958269)
                    ·
                      refine ⟨1010807721082487807984351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2695487256219967487958269 1010807721082487807984351)
                      ·
                        rfl

theorem cell23_1968541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_1968541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1968541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1968541 prefixEnd_1968541 := by exact prefixLift 1968541
  have htrace : WordTrace (prefixWord ++ tailWord_1968541) baseStart_1968541 baseEnd_1968541 := by
    simpa [prefixWord, tailWord_1968541, baseEnd_1968541] using wordTrace_append hprefix tailTrace_1968541
  have hstable : (prefixWord ++ tailWord_1968541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968541).length < 2 ^ (prefixWord ++ tailWord_1968541).sum := by decide
  have hdescent : baseEnd_1968541 < baseStart_1968541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
