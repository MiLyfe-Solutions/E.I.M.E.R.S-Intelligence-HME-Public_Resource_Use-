import V185TrunkScan23Chunk0587

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3477439 : List Nat := [1, 1, 2, 2, 2, 1, 5, 1, 4, 4]
def baseStart_3477439 : Nat := 118140960795 + 3477439 * 2 ^ 59
def prefixEnd_3477439 : Nat := 4983230072969 + 3 ^ 40 * 3477439 * 2
def baseEnd_3477439 : Nat := 595199217896775079206685

theorem tailTrace_3477439 : CollatzResearch.WordTrace tailWord_3477439 prefixEnd_3477439 595199217896775079206685 := by
  unfold tailWord_3477439
  simp only [CollatzResearch.WordTrace]
  refine ⟨126832620048839877143571371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84555080032559918095714247 126832620048839877143571371)
  ·
    refine ⟨190248930073259815715357057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126832620048839877143571371 190248930073259815715357057)
    ·
      refine ⟨142686697554944861786517793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190248930073259815715357057 142686697554944861786517793)
      ·
        refine ⟨107015023166208646339888345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142686697554944861786517793 107015023166208646339888345)
        ·
          refine ⟨80261267374656484754916259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107015023166208646339888345 80261267374656484754916259)
          ·
            refine ⟨120391901061984727132374389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80261267374656484754916259 120391901061984727132374389)
            ·
              refine ⟨11286740724561068168660099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120391901061984727132374389 11286740724561068168660099)
              ·
                refine ⟨16930111086841602252990149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11286740724561068168660099 16930111086841602252990149)
                ·
                  refine ⟨3174395828782800422435653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16930111086841602252990149 3174395828782800422435653)
                  ·
                    refine ⟨595199217896775079206685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3174395828782800422435653 595199217896775079206685)
                    ·
                      rfl

theorem cell23_3477439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 4, 4].length) (baseStart_3477439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477439 prefixEnd_3477439 := by exact prefixLift 3477439
  have htrace : WordTrace (prefixWord ++ tailWord_3477439) baseStart_3477439 baseEnd_3477439 := by
    simpa [prefixWord, tailWord_3477439, baseEnd_3477439] using wordTrace_append hprefix tailTrace_3477439
  have hstable : (prefixWord ++ tailWord_3477439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477439).length < 2 ^ (prefixWord ++ tailWord_3477439).sum := by decide
  have hdescent : baseEnd_3477439 < baseStart_3477439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477472 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 6]
def baseStart_3477472 : Nat := 118140960795 + 3477472 * 2 ^ 59
def prefixEnd_3477472 : Nat := 4983230072969 + 3 ^ 40 * 3477472 * 2
def baseEnd_3477472 : Nat := 1785614598551923608507403

theorem tailTrace_3477472 : CollatzResearch.WordTrace tailWord_3477472 prefixEnd_3477472 1785614598551923608507403 := by
  unfold tailWord_3477472
  simp only [CollatzResearch.WordTrace]
  refine ⟨63416911828860161889761335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84555882438480215853015113 63416911828860161889761335)
  ·
    refine ⟨95125367743290242834642003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63416911828860161889761335 95125367743290242834642003)
    ·
      refine ⟨142688051614935364251963005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95125367743290242834642003 142688051614935364251963005)
      ·
        refine ⟨53508019355600761594486127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142688051614935364251963005 53508019355600761594486127)
        ·
          refine ⟨80262029033401142391729191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53508019355600761594486127 80262029033401142391729191)
          ·
            refine ⟨120393043550101713587593787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80262029033401142391729191 120393043550101713587593787)
            ·
              refine ⟨180589565325152570381390681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120393043550101713587593787 180589565325152570381390681)
              ·
                refine ⟨135442173993864427786043011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180589565325152570381390681 135442173993864427786043011)
                ·
                  refine ⟨203163260990796641679064517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135442173993864427786043011 203163260990796641679064517)
                  ·
                    refine ⟨38093111435774370314824597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 203163260990796641679064517 38093111435774370314824597)
                    ·
                      refine ⟨1785614598551923608507403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38093111435774370314824597 1785614598551923608507403)
                      ·
                        rfl

theorem cell23_3477472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_3477472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477472 prefixEnd_3477472 := by exact prefixLift 3477472
  have htrace : WordTrace (prefixWord ++ tailWord_3477472) baseStart_3477472 baseEnd_3477472 := by
    simpa [prefixWord, tailWord_3477472, baseEnd_3477472] using wordTrace_append hprefix tailTrace_3477472
  have hstable : (prefixWord ++ tailWord_3477472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477472).length < 2 ^ (prefixWord ++ tailWord_3477472).sum := by decide
  have hdescent : baseEnd_3477472 < baseStart_3477472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477474 : List Nat := [3, 3, 3, 1, 2, 2, 1, 3, 1, 1, 3]
def baseStart_3477474 : Nat := 118140960795 + 3477474 * 2 ^ 59
def prefixEnd_3477474 : Nat := 4983230072969 + 3 ^ 40 * 3477474 * 2
def baseEnd_3477474 : Nat := 1785615625513232600682395

theorem tailTrace_3477474 : CollatzResearch.WordTrace tailWord_3477474 prefixEnd_3477474 1785615625513232600682395 := by
  unfold tailWord_3477474
  simp only [CollatzResearch.WordTrace]
  refine ⟨31708474150928269530273869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84555931069142052080730317 31708474150928269530273869)
  ·
    refine ⟨11890677806598101073852701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31708474150928269530273869 11890677806598101073852701)
    ·
      refine ⟨4459004177474287902694763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11890677806598101073852701 4459004177474287902694763)
      ·
        refine ⟨6688506266211431854042145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4459004177474287902694763 6688506266211431854042145)
        ·
          refine ⟨5016379699658573890531609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6688506266211431854042145 5016379699658573890531609)
          ·
            refine ⟨3762284774743930417898707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5016379699658573890531609 3762284774743930417898707)
            ·
              refine ⟨5643427162115895626848061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3762284774743930417898707 5643427162115895626848061)
              ·
                refine ⟨2116285185793460860068023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5643427162115895626848061 2116285185793460860068023)
                ·
                  refine ⟨3174427778690191290102035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2116285185793460860068023 3174427778690191290102035)
                  ·
                    refine ⟨4761641668035286935153053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3174427778690191290102035 4761641668035286935153053)
                    ·
                      refine ⟨1785615625513232600682395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4761641668035286935153053 1785615625513232600682395)
                      ·
                        rfl

theorem cell23_3477474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_3477474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477474 prefixEnd_3477474 := by exact prefixLift 3477474
  have htrace : WordTrace (prefixWord ++ tailWord_3477474) baseStart_3477474 baseEnd_3477474 := by
    simpa [prefixWord, tailWord_3477474, baseEnd_3477474] using wordTrace_append hprefix tailTrace_3477474
  have hstable : (prefixWord ++ tailWord_3477474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477474).length < 2 ^ (prefixWord ++ tailWord_3477474).sum := by decide
  have hdescent : baseEnd_3477474 < baseStart_3477474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477496 : List Nat := [2, 1, 2, 1, 1, 3, 4, 1, 4, 1, 3]
def baseStart_3477496 : Nat := 118140960795 + 3477496 * 2 ^ 59
def prefixEnd_3477496 : Nat := 4983230072969 + 3 ^ 40 * 3477496 * 2
def baseEnd_3477496 : Nat := 1785626922087631514607293

theorem tailTrace_3477496 : CollatzResearch.WordTrace tailWord_3477496 prefixEnd_3477496 1785626922087631514607293 := by
  unfold tailWord_3477496
  simp only [CollatzResearch.WordTrace]
  refine ⟨63417349504816687939198171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84556466006422250585597561 63417349504816687939198171)
  ·
    refine ⟨95126024257225031908797257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63417349504816687939198171 95126024257225031908797257)
    ·
      refine ⟨71344518192918773931597943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95126024257225031908797257 71344518192918773931597943)
      ·
        refine ⟨107016777289378160897396915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71344518192918773931597943 107016777289378160897396915)
        ·
          refine ⟨160525165934067241346095373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107016777289378160897396915 160525165934067241346095373)
          ·
            refine ⟨60196937225275215504785765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160525165934067241346095373 60196937225275215504785765)
            ·
              refine ⟨11286925729739102907147331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60196937225275215504785765 11286925729739102907147331)
              ·
                refine ⟨16930388594608654360720997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11286925729739102907147331 16930388594608654360720997)
                ·
                  refine ⟨3174447861489122692635187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16930388594608654360720997 3174447861489122692635187)
                  ·
                    refine ⟨4761671792233684038952781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3174447861489122692635187 4761671792233684038952781)
                    ·
                      refine ⟨1785626922087631514607293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4761671792233684038952781 1785626922087631514607293)
                      ·
                        rfl

theorem cell23_3477496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 4, 1, 3].length) (baseStart_3477496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477496 prefixEnd_3477496 := by exact prefixLift 3477496
  have htrace : WordTrace (prefixWord ++ tailWord_3477496) baseStart_3477496 baseEnd_3477496 := by
    simpa [prefixWord, tailWord_3477496, baseEnd_3477496] using wordTrace_append hprefix tailTrace_3477496
  have hstable : (prefixWord ++ tailWord_3477496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477496).length < 2 ^ (prefixWord ++ tailWord_3477496).sum := by decide
  have hdescent : baseEnd_3477496 < baseStart_3477496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477497 : List Nat := [1, 2, 1, 3, 1, 5, 3, 2, 1, 2, 2]
def baseStart_3477497 : Nat := 118140960795 + 3477497 * 2 ^ 59
def prefixEnd_3477497 : Nat := 4983230072969 + 3 ^ 40 * 3477497 * 2
def baseEnd_3477497 : Nat := 1785627435568286010694789

theorem tailTrace_3477497 : CollatzResearch.WordTrace tailWord_3477497 prefixEnd_3477497 1785627435568286010694789 := by
  unfold tailWord_3477497
  simp only [CollatzResearch.WordTrace]
  refine ⟨126834735482629753049182745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84556490321753168699455163 126834735482629753049182745)
  ·
    refine ⟨95126051611972314786887059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126834735482629753049182745 95126051611972314786887059)
    ·
      refine ⟨142689077417958472180330589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95126051611972314786887059 142689077417958472180330589)
      ·
        refine ⟨53508404031734427067623971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142689077417958472180330589 53508404031734427067623971)
        ·
          refine ⟨80262606047601640601435957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53508404031734427067623971 80262606047601640601435957)
          ·
            refine ⟨7524619316962653806384621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80262606047601640601435957 7524619316962653806384621)
            ·
              refine ⟨2821732243860995177394233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7524619316962653806384621 2821732243860995177394233)
              ·
                refine ⟨2116299182895746383045675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2821732243860995177394233 2116299182895746383045675)
                ·
                  refine ⟨3174448774343619574568513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2116299182895746383045675 3174448774343619574568513)
                  ·
                    refine ⟨2380836580757714680926385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3174448774343619574568513 2380836580757714680926385)
                    ·
                      refine ⟨1785627435568286010694789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2380836580757714680926385 1785627435568286010694789)
                      ·
                        rfl

theorem cell23_3477497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 2, 1, 2, 2].length) (baseStart_3477497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477497 prefixEnd_3477497 := by exact prefixLift 3477497
  have htrace : WordTrace (prefixWord ++ tailWord_3477497) baseStart_3477497 baseEnd_3477497 := by
    simpa [prefixWord, tailWord_3477497, baseEnd_3477497] using wordTrace_append hprefix tailTrace_3477497
  have hstable : (prefixWord ++ tailWord_3477497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477497).length < 2 ^ (prefixWord ++ tailWord_3477497).sum := by decide
  have hdescent : baseEnd_3477497 < baseStart_3477497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477517 : List Nat := [1, 7, 1, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_3477517 : Nat := 118140960795 + 3477517 * 2 ^ 59
def prefixEnd_3477517 : Nat := 4983230072969 + 3 ^ 40 * 3477517 * 2
def baseEnd_3477517 : Nat := 1785637705181375932444697

theorem tailTrace_3477517 : CollatzResearch.WordTrace tailWord_3477517 prefixEnd_3477517 1785637705181375932444697 := by
  unfold tailWord_3477517
  simp only [CollatzResearch.WordTrace]
  refine ⟨126835464942557296464910805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84556976628371530976607203 126835464942557296464910805)
  ·
    refine ⟨2972706209591186635896347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 126835464942557296464910805 2972706209591186635896347)
    ·
      refine ⟨4459059314386779953844521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2972706209591186635896347 4459059314386779953844521)
      ·
        refine ⟨3344294485790084965383391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4459059314386779953844521 3344294485790084965383391)
        ·
          refine ⟨5016441728685127448075087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3344294485790084965383391 5016441728685127448075087)
          ·
            refine ⟨7524662593027691172112631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5016441728685127448075087 7524662593027691172112631)
            ·
              refine ⟨11286993889541536758168947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7524662593027691172112631 11286993889541536758168947)
              ·
                refine ⟨16930490834312305137253421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11286993889541536758168947 16930490834312305137253421)
                ·
                  refine ⟨6348934062867114426470033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16930490834312305137253421 6348934062867114426470033)
                  ·
                    refine ⟨4761700547150335819852525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6348934062867114426470033 4761700547150335819852525)
                    ·
                      refine ⟨1785637705181375932444697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4761700547150335819852525 1785637705181375932444697)
                      ·
                        rfl

theorem cell23_3477517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_3477517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477517 prefixEnd_3477517 := by exact prefixLift 3477517
  have htrace : WordTrace (prefixWord ++ tailWord_3477517) baseStart_3477517 baseEnd_3477517 := by
    simpa [prefixWord, tailWord_3477517, baseEnd_3477517] using wordTrace_append hprefix tailTrace_3477517
  have hstable : (prefixWord ++ tailWord_3477517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477517).length < 2 ^ (prefixWord ++ tailWord_3477517).sum := by decide
  have hdescent : baseEnd_3477517 < baseStart_3477517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477523 : List Nat := [1, 1, 1, 2, 1, 4, 5, 2, 1, 3, 2]
def baseStart_3477523 : Nat := 118140960795 + 3477523 * 2 ^ 59
def prefixEnd_3477523 : Nat := 4983230072969 + 3 ^ 40 * 3477523 * 2
def baseEnd_3477523 : Nat := 1785640786065302908969669

theorem tailTrace_3477523 : CollatzResearch.WordTrace tailWord_3477523 prefixEnd_3477523 1785640786065302908969669 := by
  unfold tailWord_3477523
  simp only [CollatzResearch.WordTrace]
  refine ⟨126835683780535559489629223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84557122520357039659752815 126835683780535559489629223)
  ·
    refine ⟨190253525670803339234443835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126835683780535559489629223 190253525670803339234443835)
    ·
      refine ⟨285380288506205008851665753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190253525670803339234443835 285380288506205008851665753)
      ·
        refine ⟨214035216379653756638749315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285380288506205008851665753 214035216379653756638749315)
        ·
          refine ⟨321052824569480634958123973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214035216379653756638749315 321052824569480634958123973)
          ·
            refine ⟨60197404606777619054648245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 321052824569480634958123973 60197404606777619054648245)
            ·
              refine ⟨5643506681885401786373273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60197404606777619054648245 5643506681885401786373273)
              ·
                refine ⟨4232630011414051339779955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5643506681885401786373273 4232630011414051339779955)
                ·
                  refine ⟨6348945017121077009669933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4232630011414051339779955 6348945017121077009669933)
                  ·
                    refine ⟨2380854381420403878626225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6348945017121077009669933 2380854381420403878626225)
                    ·
                      refine ⟨1785640786065302908969669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2380854381420403878626225 1785640786065302908969669)
                      ·
                        rfl

theorem cell23_3477523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 3, 2].length) (baseStart_3477523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477523 prefixEnd_3477523 := by exact prefixLift 3477523
  have htrace : WordTrace (prefixWord ++ tailWord_3477523) baseStart_3477523 baseEnd_3477523 := by
    simpa [prefixWord, tailWord_3477523, baseEnd_3477523] using wordTrace_append hprefix tailTrace_3477523
  have hstable : (prefixWord ++ tailWord_3477523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477523).length < 2 ^ (prefixWord ++ tailWord_3477523).sum := by decide
  have hdescent : baseEnd_3477523 < baseStart_3477523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477539 : List Nat := [1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 5]
def baseStart_3477539 : Nat := 118140960795 + 3477539 * 2 ^ 59
def prefixEnd_3477539 : Nat := 4983230072969 + 3 ^ 40 * 3477539 * 2
def baseEnd_3477539 : Nat := 1785649001755774846369595

theorem tailTrace_3477539 : CollatzResearch.WordTrace tailWord_3477539 prefixEnd_3477539 1785649001755774846369595 := by
  unfold tailWord_3477539
  simp only [CollatzResearch.WordTrace]
  refine ⟨126836267348477594222211671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84557511565651729481474447 126836267348477594222211671)
  ·
    refine ⟨190254401022716391333317507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126836267348477594222211671 190254401022716391333317507)
    ·
      refine ⟨285381601534074586999976261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190254401022716391333317507 285381601534074586999976261)
      ·
        refine ⟨53509050287638985062495549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 285381601534074586999976261 53509050287638985062495549)
        ·
          refine ⟨20065893857864619398435831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53509050287638985062495549 20065893857864619398435831)
          ·
            refine ⟨30098840786796929097653747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20065893857864619398435831 30098840786796929097653747)
            ·
              refine ⟨45148261180195393646480621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30098840786796929097653747 45148261180195393646480621)
              ·
                refine ⟨16930597942573272617430233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45148261180195393646480621 16930597942573272617430233)
                ·
                  refine ⟨12697948456929954463072675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16930597942573272617430233 12697948456929954463072675)
                  ·
                    refine ⟨19046922685394931694609013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12697948456929954463072675 19046922685394931694609013)
                    ·
                      refine ⟨1785649001755774846369595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19046922685394931694609013 1785649001755774846369595)
                      ·
                        rfl

theorem cell23_3477539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_3477539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477539 prefixEnd_3477539 := by exact prefixLift 3477539
  have htrace : WordTrace (prefixWord ++ tailWord_3477539) baseStart_3477539 baseEnd_3477539 := by
    simpa [prefixWord, tailWord_3477539, baseEnd_3477539] using wordTrace_append hprefix tailTrace_3477539
  have hstable : (prefixWord ++ tailWord_3477539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477539).length < 2 ^ (prefixWord ++ tailWord_3477539).sum := by decide
  have hdescent : baseEnd_3477539 < baseStart_3477539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477599 : List Nat := [1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 5]
def baseStart_3477599 : Nat := 118140960795 + 3477599 * 2 ^ 59
def prefixEnd_3477599 : Nat := 4983230072969 + 3 ^ 40 * 3477599 * 2
def baseEnd_3477599 : Nat := 1785679810595044611619319

theorem tailTrace_3477599 : CollatzResearch.WordTrace tailWord_3477599 prefixEnd_3477599 1785679810595044611619319 := by
  unfold tailWord_3477599
  simp only [CollatzResearch.WordTrace]
  refine ⟨126838455728260224469395851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84558970485506816312930567 126838455728260224469395851)
  ·
    refine ⟨190257683592390336704093777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126838455728260224469395851 190257683592390336704093777)
    ·
      refine ⟨142693262694292752528070333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190257683592390336704093777 142693262694292752528070333)
      ·
        refine ⟨53509973510359782198026375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142693262694292752528070333 53509973510359782198026375)
        ·
          refine ⟨80264960265539673297039563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53509973510359782198026375 80264960265539673297039563)
          ·
            refine ⟨120397440398309509945559345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80264960265539673297039563 120397440398309509945559345)
            ·
              refine ⟨90298080298732132459169509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120397440398309509945559345 90298080298732132459169509)
              ·
                refine ⟨16930890056012274836094283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90298080298732132459169509 16930890056012274836094283)
                ·
                  refine ⟨25396335084018412254141425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16930890056012274836094283 25396335084018412254141425)
                  ·
                    refine ⟨19047251313013809190606069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25396335084018412254141425 19047251313013809190606069)
                    ·
                      refine ⟨1785679810595044611619319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19047251313013809190606069 1785679810595044611619319)
                      ·
                        rfl

theorem cell23_3477599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_3477599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477599 prefixEnd_3477599 := by exact prefixLift 3477599
  have htrace : WordTrace (prefixWord ++ tailWord_3477599) baseStart_3477599 baseEnd_3477599 := by
    simpa [prefixWord, tailWord_3477599, baseEnd_3477599] using wordTrace_append hprefix tailTrace_3477599
  have hstable : (prefixWord ++ tailWord_3477599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477599).length < 2 ^ (prefixWord ++ tailWord_3477599).sum := by decide
  have hdescent : baseEnd_3477599 < baseStart_3477599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477663 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 4, 2, 3]
def baseStart_3477663 : Nat := 118140960795 + 3477663 * 2 ^ 59
def prefixEnd_3477663 : Nat := 4983230072969 + 3 ^ 40 * 3477663 * 2
def baseEnd_3477663 : Nat := 1785712673356932361219025

theorem tailTrace_3477663 : CollatzResearch.WordTrace tailWord_3477663 prefixEnd_3477663 1785712673356932361219025 := by
  unfold tailWord_3477663
  simp only [CollatzResearch.WordTrace]
  refine ⟨126840790000028363399725643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84560526666685575599817095 126840790000028363399725643)
  ·
    refine ⟨190261185000042545099588465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126840790000028363399725643 190261185000042545099588465)
    ·
      refine ⟨142695888750031908824691349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190261185000042545099588465 142695888750031908824691349)
      ·
        refine ⟨6688869785157745726157407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 142695888750031908824691349 6688869785157745726157407)
        ·
          refine ⟨10033304677736618589236111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6688869785157745726157407 10033304677736618589236111)
          ·
            refine ⟨15049957016604927883854167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10033304677736618589236111 15049957016604927883854167)
            ·
              refine ⟨22574935524907391825781251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15049957016604927883854167 22574935524907391825781251)
              ·
                refine ⟨33862403287361087738671877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22574935524907391825781251 33862403287361087738671877)
                ·
                  refine ⟨6349200616380203951000977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33862403287361087738671877 6349200616380203951000977)
                  ·
                    refine ⟨4761900462285152963250733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6349200616380203951000977 4761900462285152963250733)
                    ·
                      refine ⟨1785712673356932361219025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4761900462285152963250733 1785712673356932361219025)
                      ·
                        rfl

theorem cell23_3477663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_3477663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477663 prefixEnd_3477663 := by exact prefixLift 3477663
  have htrace : WordTrace (prefixWord ++ tailWord_3477663) baseStart_3477663 baseEnd_3477663 := by
    simpa [prefixWord, tailWord_3477663, baseEnd_3477663] using wordTrace_append hprefix tailTrace_3477663
  have hstable : (prefixWord ++ tailWord_3477663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477663).length < 2 ^ (prefixWord ++ tailWord_3477663).sum := by decide
  have hdescent : baseEnd_3477663 < baseStart_3477663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477679 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 2, 9]
def baseStart_3477679 : Nat := 118140960795 + 3477679 * 2 ^ 59
def prefixEnd_3477679 : Nat := 4983230072969 + 3 ^ 40 * 3477679 * 2
def baseEnd_3477679 : Nat := 595240296349134766206317

theorem tailTrace_3477679 : CollatzResearch.WordTrace tailWord_3477679 prefixEnd_3477679 595240296349134766206317 := by
  unfold tailWord_3477679
  simp only [CollatzResearch.WordTrace]
  refine ⟨126841373567970398132308091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84560915711980265421538727 126841373567970398132308091)
  ·
    refine ⟨190262060351955597198462137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126841373567970398132308091 190262060351955597198462137)
    ·
      refine ⟨142696545263966697898846603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190262060351955597198462137 142696545263966697898846603)
      ·
        refine ⟨214044817895950046848269905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142696545263966697898846603 214044817895950046848269905)
        ·
          refine ⟨160533613421962535136202429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214044817895950046848269905 160533613421962535136202429)
          ·
            refine ⟨60200105033235950676075911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160533613421962535136202429 60200105033235950676075911)
            ·
              refine ⟨90300157549853926014113867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60200105033235950676075911 90300157549853926014113867)
              ·
                refine ⟨135450236324780889021170801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90300157549853926014113867 135450236324780889021170801)
                ·
                  refine ⟨101587677243585666765878101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135450236324780889021170801 101587677243585666765878101)
                  ·
                    refine ⟨595240296349134766206317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 101587677243585666765878101 595240296349134766206317)
                    ·
                      rfl

theorem cell23_3477679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 9].length) (baseStart_3477679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477679 prefixEnd_3477679 := by exact prefixLift 3477679
  have htrace : WordTrace (prefixWord ++ tailWord_3477679) baseStart_3477679 baseEnd_3477679 := by
    simpa [prefixWord, tailWord_3477679, baseEnd_3477679] using wordTrace_append hprefix tailTrace_3477679
  have hstable : (prefixWord ++ tailWord_3477679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477679).length < 2 ^ (prefixWord ++ tailWord_3477679).sum := by decide
  have hdescent : baseEnd_3477679 < baseStart_3477679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477693 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 5, 1, 3]
def baseStart_3477693 : Nat := 118140960795 + 3477693 * 2 ^ 59
def prefixEnd_3477693 : Nat := 4983230072969 + 3 ^ 40 * 3477693 * 2
def baseEnd_3477693 : Nat := 1785728077776567243843887

theorem tailTrace_3477693 : CollatzResearch.WordTrace tailWord_3477693 prefixEnd_3477693 1785728077776567243843887 := by
  unfold tailWord_3477693
  simp only [CollatzResearch.WordTrace]
  refine ⟨126841884189919678523317733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84561256126613119015545155 126841884189919678523317733)
  ·
    refine ⟨23782853285609939723122075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126841884189919678523317733 23782853285609939723122075)
    ·
      refine ⟨35674279928414909584683113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23782853285609939723122075 35674279928414909584683113)
      ·
        refine ⟨26755709946311182188512335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35674279928414909584683113 26755709946311182188512335)
        ·
          refine ⟨40133564919466773282768503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26755709946311182188512335 40133564919466773282768503)
          ·
            refine ⟨60200347379200159924152755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40133564919466773282768503 60200347379200159924152755)
            ·
              refine ⟨90300521068800239886229133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60200347379200159924152755 90300521068800239886229133)
              ·
                refine ⟨33862695400800089957335925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90300521068800239886229133 33862695400800089957335925)
                ·
                  refine ⟨3174627693825008433500243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33862695400800089957335925 3174627693825008433500243)
                  ·
                    refine ⟨4761941540737512650250365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3174627693825008433500243 4761941540737512650250365)
                    ·
                      refine ⟨1785728077776567243843887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4761941540737512650250365 1785728077776567243843887)
                      ·
                        rfl

theorem cell23_3477693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_3477693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477693 prefixEnd_3477693 := by exact prefixLift 3477693
  have htrace : WordTrace (prefixWord ++ tailWord_3477693) baseStart_3477693 baseEnd_3477693 := by
    simpa [prefixWord, tailWord_3477693, baseEnd_3477693] using wordTrace_append hprefix tailTrace_3477693
  have hstable : (prefixWord ++ tailWord_3477693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477693).length < 2 ^ (prefixWord ++ tailWord_3477693).sum := by decide
  have hdescent : baseEnd_3477693 < baseStart_3477693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477697 : List Nat := [1, 2, 6, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_3477697 : Nat := 118140960795 + 3477697 * 2 ^ 59
def prefixEnd_3477697 : Nat := 4983230072969 + 3 ^ 40 * 3477697 * 2
def baseEnd_3477697 : Nat := 1785730131699185228193869

theorem tailTrace_3477697 : CollatzResearch.WordTrace tailWord_3477697 prefixEnd_3477697 1785730131699185228193869 := by
  unfold tailWord_3477697
  simp only [CollatzResearch.WordTrace]
  refine ⟨126842030081905187206463345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84561353387936791470975563 126842030081905187206463345)
  ·
    refine ⟨95131522561428890404847509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126842030081905187206463345 95131522561428890404847509)
    ·
      refine ⟨4459290120066979237727227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 95131522561428890404847509 4459290120066979237727227)
      ·
        refine ⟨6688935180100468856590841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4459290120066979237727227 6688935180100468856590841)
        ·
          refine ⟨5016701385075351642443131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6688935180100468856590841 5016701385075351642443131)
          ·
            refine ⟨7525052077613027463664697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5016701385075351642443131 7525052077613027463664697)
            ·
              refine ⟨5643789058209770597748523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7525052077613027463664697 5643789058209770597748523)
              ·
                refine ⟨8465683587314655896622785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5643789058209770597748523 8465683587314655896622785)
                ·
                  refine ⟨6349262690485991922467089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8465683587314655896622785 6349262690485991922467089)
                  ·
                    refine ⟨4761947017864493941850317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6349262690485991922467089 4761947017864493941850317)
                    ·
                      refine ⟨1785730131699185228193869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4761947017864493941850317 1785730131699185228193869)
                      ·
                        rfl

theorem cell23_3477697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_3477697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477697 prefixEnd_3477697 := by exact prefixLift 3477697
  have htrace : WordTrace (prefixWord ++ tailWord_3477697) baseStart_3477697 baseEnd_3477697 := by
    simpa [prefixWord, tailWord_3477697, baseEnd_3477697] using wordTrace_append hprefix tailTrace_3477697
  have hstable : (prefixWord ++ tailWord_3477697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477697).length < 2 ^ (prefixWord ++ tailWord_3477697).sum := by decide
  have hdescent : baseEnd_3477697 < baseStart_3477697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477720 : List Nat := [2, 1, 2, 2, 4, 1, 2, 2, 2, 3, 2]
def baseStart_3477720 : Nat := 118140960795 + 3477720 * 2 ^ 59
def prefixEnd_3477720 : Nat := 4983230072969 + 3 ^ 40 * 3477720 * 2
def baseEnd_3477720 : Nat := 1785741941754238638206263

theorem tailTrace_3477720 : CollatzResearch.WordTrace tailWord_3477720 prefixEnd_3477720 1785741941754238638206263 := by
  unfold tailWord_3477720
  simp only [CollatzResearch.WordTrace]
  refine ⟨63421434480410931067275307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84561912640547908089700409 63421434480410931067275307)
  ·
    refine ⟨95132151720616396600912961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63421434480410931067275307 95132151720616396600912961)
    ·
      refine ⟨71349113790462297450684721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95132151720616396600912961 71349113790462297450684721)
      ·
        refine ⟨53511835342846723088013541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71349113790462297450684721 53511835342846723088013541)
        ·
          refine ⟨10033469126783760579002539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53511835342846723088013541 10033469126783760579002539)
          ·
            refine ⟨15050203690175640868503809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10033469126783760579002539 15050203690175640868503809)
            ·
              refine ⟨11287652767631730651377857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15050203690175640868503809 11287652767631730651377857)
              ·
                refine ⟨8465739575723797988533393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11287652767631730651377857 8465739575723797988533393)
                ·
                  refine ⟨6349304681792848491400045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8465739575723797988533393 6349304681792848491400045)
                  ·
                    refine ⟨2380989255672318184275017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6349304681792848491400045 2380989255672318184275017)
                    ·
                      refine ⟨1785741941754238638206263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2380989255672318184275017 1785741941754238638206263)
                      ·
                        rfl

theorem cell23_3477720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 2, 3, 2].length) (baseStart_3477720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477720 prefixEnd_3477720 := by exact prefixLift 3477720
  have htrace : WordTrace (prefixWord ++ tailWord_3477720) baseStart_3477720 baseEnd_3477720 := by
    simpa [prefixWord, tailWord_3477720, baseEnd_3477720] using wordTrace_append hprefix tailTrace_3477720
  have hstable : (prefixWord ++ tailWord_3477720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477720).length < 2 ^ (prefixWord ++ tailWord_3477720).sum := by decide
  have hdescent : baseEnd_3477720 < baseStart_3477720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477733 : List Nat := [1, 3, 1, 4, 2, 1, 1, 2, 3, 1, 4]
def baseStart_3477733 : Nat := 118140960795 + 3477733 * 2 ^ 59
def prefixEnd_3477733 : Nat := 4983230072969 + 3 ^ 40 * 3477733 * 2
def baseEnd_3477733 : Nat := 1785748617002747087343703

theorem tailTrace_3477733 : CollatzResearch.WordTrace tailWord_3477733 prefixEnd_3477733 1785748617002747087343703 := by
  unfold tailWord_3477733
  simp only [CollatzResearch.WordTrace]
  refine ⟨126843343109774765354773853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84562228739849843569849235 126843343109774765354773853)
  ·
    refine ⟨47566253666165537008040195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126843343109774765354773853 47566253666165537008040195)
    ·
      refine ⟨71349380499248305512060293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47566253666165537008040195 71349380499248305512060293)
      ·
        refine ⟨13378008843609057283511305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71349380499248305512060293 13378008843609057283511305)
        ·
          refine ⟨10033506632706792962633479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13378008843609057283511305 10033506632706792962633479)
          ·
            refine ⟨15050259949060189443950219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10033506632706792962633479 15050259949060189443950219)
            ·
              refine ⟨22575389923590284165925329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15050259949060189443950219 22575389923590284165925329)
              ·
                refine ⟨16931542442692713124443997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22575389923590284165925329 16931542442692713124443997)
                ·
                  refine ⟨6349328416009767421666499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16931542442692713124443997 6349328416009767421666499)
                  ·
                    refine ⟨9523992624014651132499749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6349328416009767421666499 9523992624014651132499749)
                    ·
                      refine ⟨1785748617002747087343703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9523992624014651132499749 1785748617002747087343703)
                      ·
                        rfl

theorem cell23_3477733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_3477733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477733 prefixEnd_3477733 := by exact prefixLift 3477733
  have htrace : WordTrace (prefixWord ++ tailWord_3477733) baseStart_3477733 baseEnd_3477733 := by
    simpa [prefixWord, tailWord_3477733, baseEnd_3477733] using wordTrace_append hprefix tailTrace_3477733
  have hstable : (prefixWord ++ tailWord_3477733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477733).length < 2 ^ (prefixWord ++ tailWord_3477733).sum := by decide
  have hdescent : baseEnd_3477733 < baseStart_3477733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477743 : List Nat := [1, 1, 2, 1, 6, 2, 2, 1, 1, 6]
def baseStart_3477743 : Nat := 118140960795 + 3477743 * 2 ^ 59
def prefixEnd_3477743 : Nat := 4983230072969 + 3 ^ 40 * 3477743 * 2
def baseEnd_3477743 : Nat := 595251250603097349406219

theorem tailTrace_3477743 : CollatzResearch.WordTrace tailWord_3477743 prefixEnd_3477743 595251250603097349406219 := by
  unfold tailWord_3477743
  simp only [CollatzResearch.WordTrace]
  refine ⟨126843707839738537062637883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84562471893159024708425255 126843707839738537062637883)
  ·
    refine ⟨190265561759607805593956825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126843707839738537062637883 190265561759607805593956825)
    ·
      refine ⟨142699171319705854195467619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190265561759607805593956825 142699171319705854195467619)
      ·
        refine ⟨214048756979558781293201429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142699171319705854195467619 214048756979558781293201429)
        ·
          refine ⟨10033535483416817873118817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 214048756979558781293201429 10033535483416817873118817)
          ·
            refine ⟨7525151612562613404839113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10033535483416817873118817 7525151612562613404839113)
            ·
              refine ⟨5643863709421960053629335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7525151612562613404839113 5643863709421960053629335)
              ·
                refine ⟨8465795564132940080444003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5643863709421960053629335 8465795564132940080444003)
                ·
                  refine ⟨12698693346199410120666005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8465795564132940080444003 12698693346199410120666005)
                  ·
                    refine ⟨595251250603097349406219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12698693346199410120666005 595251250603097349406219)
                    ·
                      rfl

theorem cell23_3477743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 6].length) (baseStart_3477743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477743 prefixEnd_3477743 := by exact prefixLift 3477743
  have htrace : WordTrace (prefixWord ++ tailWord_3477743) baseStart_3477743 baseEnd_3477743 := by
    simpa [prefixWord, tailWord_3477743, baseEnd_3477743] using wordTrace_append hprefix tailTrace_3477743
  have hstable : (prefixWord ++ tailWord_3477743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477743).length < 2 ^ (prefixWord ++ tailWord_3477743).sum := by decide
  have hdescent : baseEnd_3477743 < baseStart_3477743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477764 : List Nat := [2, 3, 2, 2, 4, 1, 2, 1, 1, 5]
def baseStart_3477764 : Nat := 118140960795 + 3477764 * 2 ^ 59
def prefixEnd_3477764 : Nat := 4983230072969 + 3 ^ 40 * 3477764 * 2
def baseEnd_3477764 : Nat := 595254844967678822018687

theorem tailTrace_3477764 : CollatzResearch.WordTrace tailWord_3477764 prefixEnd_3477764 595254844967678822018687 := by
  unfold tailWord_3477764
  simp only [CollatzResearch.WordTrace]
  refine ⟨63422236886331228824576173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84562982515108305099434897 63422236886331228824576173)
  ·
    refine ⟨23783338832374210809216065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63422236886331228824576173 23783338832374210809216065)
    ·
      refine ⟨17837504124280658106912049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23783338832374210809216065 17837504124280658106912049)
      ·
        refine ⟨13378128093210493580184037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17837504124280658106912049 13378128093210493580184037)
        ·
          refine ⟨2508399017476967546284507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13378128093210493580184037 2508399017476967546284507)
          ·
            refine ⟨3762598526215451319426761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508399017476967546284507 3762598526215451319426761)
            ·
              refine ⟨2821948894661588489570071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3762598526215451319426761 2821948894661588489570071)
              ·
                refine ⟨4232923341992382734355107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2821948894661588489570071 4232923341992382734355107)
                ·
                  refine ⟨6349385012988574101532661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4232923341992382734355107 6349385012988574101532661)
                  ·
                    refine ⟨595254844967678822018687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6349385012988574101532661 595254844967678822018687)
                    ·
                      rfl

theorem cell23_3477764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_3477764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477764 prefixEnd_3477764 := by exact prefixLift 3477764
  have htrace : WordTrace (prefixWord ++ tailWord_3477764) baseStart_3477764 baseEnd_3477764 := by
    simpa [prefixWord, tailWord_3477764, baseEnd_3477764] using wordTrace_append hprefix tailTrace_3477764
  have hstable : (prefixWord ++ tailWord_3477764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477764).length < 2 ^ (prefixWord ++ tailWord_3477764).sum := by decide
  have hdescent : baseEnd_3477764 < baseStart_3477764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477767 : List Nat := [1, 1, 4, 5, 1, 1, 1, 3, 1, 1, 4]
def baseStart_3477767 : Nat := 118140960795 + 3477767 * 2 ^ 59
def prefixEnd_3477767 : Nat := 4983230072969 + 3 ^ 40 * 3477767 * 2
def baseEnd_3477767 : Nat := 1785766075344999954318547

theorem tailTrace_3477767 : CollatzResearch.WordTrace tailWord_3477767 prefixEnd_3477767 1785766075344999954318547 := by
  unfold tailWord_3477767
  simp only [CollatzResearch.WordTrace]
  refine ⟨126844583191651589161511555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84563055461101059441007703 126844583191651589161511555)
  ·
    refine ⟨190266874787477383742267333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126844583191651589161511555 190266874787477383742267333)
    ·
      refine ⟨35675039022652009451675125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190266874787477383742267333 35675039022652009451675125)
      ·
        refine ⟨3344534908373625886094543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35675039022652009451675125 3344534908373625886094543)
        ·
          refine ⟨5016802362560438829141815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3344534908373625886094543 5016802362560438829141815)
          ·
            refine ⟨7525203543840658243712723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5016802362560438829141815 7525203543840658243712723)
            ·
              refine ⟨11287805315760987365569085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7525203543840658243712723 11287805315760987365569085)
              ·
                refine ⟨4232926993410370262088407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11287805315760987365569085 4232926993410370262088407)
                ·
                  refine ⟨6349390490115555393132611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4232926993410370262088407 6349390490115555393132611)
                  ·
                    refine ⟨9524085735173333089698917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6349390490115555393132611 9524085735173333089698917)
                    ·
                      refine ⟨1785766075344999954318547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9524085735173333089698917 1785766075344999954318547)
                      ·
                        rfl

theorem cell23_3477767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_3477767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477767 prefixEnd_3477767 := by exact prefixLift 3477767
  have htrace : WordTrace (prefixWord ++ tailWord_3477767) baseStart_3477767 baseEnd_3477767 := by
    simpa [prefixWord, tailWord_3477767, baseEnd_3477767] using wordTrace_append hprefix tailTrace_3477767
  have hstable : (prefixWord ++ tailWord_3477767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477767).length < 2 ^ (prefixWord ++ tailWord_3477767).sum := by decide
  have hdescent : baseEnd_3477767 < baseStart_3477767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477797 : List Nat := [1, 3, 1, 2, 6, 1, 1, 1, 1, 2, 4]
def baseStart_3477797 : Nat := 118140960795 + 3477797 * 2 ^ 59
def prefixEnd_3477797 : Nat := 4983230072969 + 3 ^ 40 * 3477797 * 2
def baseEnd_3477797 : Nat := 1785781479764634836943409

theorem tailTrace_3477797 : CollatzResearch.WordTrace tailWord_3477797 prefixEnd_3477797 1785781479764634836943409 := by
  unfold tailWord_3477797
  simp only [CollatzResearch.WordTrace]
  refine ⟨126845677381542904285103645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84563784921028602856735763 126845677381542904285103645)
  ·
    refine ⟨47567129018078589106913867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126845677381542904285103645 47567129018078589106913867)
    ·
      refine ⟨71350693527117883660370801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47567129018078589106913867 71350693527117883660370801)
      ·
        refine ⟨53513020145338412745278101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71350693527117883660370801 53513020145338412745278101)
        ·
          refine ⟨2508422819312738097434911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53513020145338412745278101 2508422819312738097434911)
          ·
            refine ⟨3762634228969107146152367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508422819312738097434911 3762634228969107146152367)
            ·
              refine ⟨5643951343453660719228551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3762634228969107146152367 5643951343453660719228551)
              ·
                refine ⟨8465927015180491078842827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5643951343453660719228551 8465927015180491078842827)
                ·
                  refine ⟨12698890522770736618264241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8465927015180491078842827 12698890522770736618264241)
                  ·
                    refine ⟨9524167892078052463698181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12698890522770736618264241 9524167892078052463698181)
                    ·
                      refine ⟨1785781479764634836943409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9524167892078052463698181 1785781479764634836943409)
                      ·
                        rfl

theorem cell23_3477797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 1, 2, 4].length) (baseStart_3477797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477797 prefixEnd_3477797 := by exact prefixLift 3477797
  have htrace : WordTrace (prefixWord ++ tailWord_3477797) baseStart_3477797 baseEnd_3477797 := by
    simpa [prefixWord, tailWord_3477797, baseEnd_3477797] using wordTrace_append hprefix tailTrace_3477797
  have hstable : (prefixWord ++ tailWord_3477797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477797).length < 2 ^ (prefixWord ++ tailWord_3477797).sum := by decide
  have hdescent : baseEnd_3477797 < baseStart_3477797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477816 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 1, 8]
def baseStart_3477816 : Nat := 118140960795 + 3477816 * 2 ^ 59
def prefixEnd_3477816 : Nat := 4983230072969 + 3 ^ 40 * 3477816 * 2
def baseEnd_3477816 : Nat := 595263745299023420868607

theorem tailTrace_3477816 : CollatzResearch.WordTrace tailWord_3477816 prefixEnd_3477816 595263745299023420868607 := by
  unfold tailWord_3477816
  simp only [CollatzResearch.WordTrace]
  refine ⟨63423185184237035265022651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84564246912316047020030201 63423185184237035265022651)
  ·
    refine ⟨95134777776355552897533977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63423185184237035265022651 95134777776355552897533977)
    ·
      refine ⟨71351083332266664673150483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95134777776355552897533977 71351083332266664673150483)
      ·
        refine ⟨107026624998399997009725725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71351083332266664673150483 107026624998399997009725725)
        ·
          refine ⟨40134984374399998878647147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107026624998399997009725725 40134984374399998878647147)
          ·
            refine ⟨60202476561599998317970721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40134984374399998878647147 60202476561599998317970721)
            ·
              refine ⟨45151857421199998738478041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60202476561599998317970721 45151857421199998738478041)
              ·
                refine ⟨33863893065899999053858531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45151857421199998738478041 33863893065899999053858531)
                ·
                  refine ⟨50795839598849998580787797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33863893065899999053858531 50795839598849998580787797)
                  ·
                    refine ⟨595263745299023420868607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50795839598849998580787797 595263745299023420868607)
                    ·
                      rfl

theorem cell23_3477816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 1, 8].length) (baseStart_3477816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477816 prefixEnd_3477816 := by exact prefixLift 3477816
  have htrace : WordTrace (prefixWord ++ tailWord_3477816) baseStart_3477816 baseEnd_3477816 := by
    simpa [prefixWord, tailWord_3477816, baseEnd_3477816] using wordTrace_append hprefix tailTrace_3477816
  have hstable : (prefixWord ++ tailWord_3477816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477816).length < 2 ^ (prefixWord ++ tailWord_3477816).sum := by decide
  have hdescent : baseEnd_3477816 < baseStart_3477816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477873 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 4, 3, 3]
def baseStart_3477873 : Nat := 118140960795 + 3477873 * 2 ^ 59
def prefixEnd_3477873 : Nat := 4983230072969 + 3 ^ 40 * 3477873 * 2
def baseEnd_3477873 : Nat := 1785820504294376539593059

theorem tailTrace_3477873 : CollatzResearch.WordTrace tailWord_3477873 prefixEnd_3477873 1785820504294376539593059 := by
  unfold tailWord_3477873
  simp only [CollatzResearch.WordTrace]
  refine ⟨126848449329267569264870273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84565632886178379509913515 126848449329267569264870273)
  ·
    refine ⟨95136336996950676948652705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126848449329267569264870273 95136336996950676948652705)
    ·
      refine ⟨71352252747713007711489529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95136336996950676948652705 71352252747713007711489529)
      ·
        refine ⟨53514189560784755783617147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71352252747713007711489529 53514189560784755783617147)
        ·
          refine ⟨80271284341177133675425721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53514189560784755783617147 80271284341177133675425721)
          ·
            refine ⟨60203463255882850256569291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80271284341177133675425721 60203463255882850256569291)
            ·
              refine ⟨90305194883824275384853937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60203463255882850256569291 90305194883824275384853937)
              ·
                refine ⟨67728896162868206538640453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90305194883824275384853937 67728896162868206538640453)
                ·
                  refine ⟨12699168030537788725995085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67728896162868206538640453 12699168030537788725995085)
                  ·
                    refine ⟨4762188011451670772248157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12699168030537788725995085 4762188011451670772248157)
                    ·
                      refine ⟨1785820504294376539593059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4762188011451670772248157 1785820504294376539593059)
                      ·
                        rfl

theorem cell23_3477873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_3477873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477873 prefixEnd_3477873 := by exact prefixLift 3477873
  have htrace : WordTrace (prefixWord ++ tailWord_3477873) baseStart_3477873 baseEnd_3477873 := by
    simpa [prefixWord, tailWord_3477873, baseEnd_3477873] using wordTrace_append hprefix tailTrace_3477873
  have hstable : (prefixWord ++ tailWord_3477873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477873).length < 2 ^ (prefixWord ++ tailWord_3477873).sum := by decide
  have hdescent : baseEnd_3477873 < baseStart_3477873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477878 : List Nat := [5, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2]
def baseStart_3477878 : Nat := 118140960795 + 3477878 * 2 ^ 59
def prefixEnd_3477878 : Nat := 4983230072969 + 3 ^ 40 * 3477878 * 2
def baseEnd_3477878 : Nat := 1785823071697649020030537

theorem tailTrace_3477878 : CollatzResearch.WordTrace tailWord_3477878 prefixEnd_3477878 1785823071697649020030537 := by
  unfold tailWord_3477878
  simp only [CollatzResearch.WordTrace]
  refine ⟨7928039480890590944925143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84565754462832970079201525 7928039480890590944925143)
  ·
    refine ⟨11892059221335886417387715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7928039480890590944925143 11892059221335886417387715)
    ·
      refine ⟨17838088832003829626081573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11892059221335886417387715 17838088832003829626081573)
      ·
        refine ⟨3344641656000718054890295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17838088832003829626081573 3344641656000718054890295)
        ·
          refine ⟨5016962484001077082335443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3344641656000718054890295 5016962484001077082335443)
          ·
            refine ⟨7525443726001615623503165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5016962484001077082335443 7525443726001615623503165)
            ·
              refine ⟨2822041397250605858813687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7525443726001615623503165 2822041397250605858813687)
              ·
                refine ⟨4233062095875908788220531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2822041397250605858813687 4233062095875908788220531)
                ·
                  refine ⟨6349593143813863182330797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4233062095875908788220531 6349593143813863182330797)
                  ·
                    refine ⟨2381097428930198693374049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6349593143813863182330797 2381097428930198693374049)
                    ·
                      refine ⟨1785823071697649020030537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2381097428930198693374049 1785823071697649020030537)
                      ·
                        rfl

theorem cell23_3477878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_3477878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477878 prefixEnd_3477878 := by exact prefixLift 3477878
  have htrace : WordTrace (prefixWord ++ tailWord_3477878) baseStart_3477878 baseEnd_3477878 := by
    simpa [prefixWord, tailWord_3477878, baseEnd_3477878] using wordTrace_append hprefix tailTrace_3477878
  have hstable : (prefixWord ++ tailWord_3477878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477878).length < 2 ^ (prefixWord ++ tailWord_3477878).sum := by decide
  have hdescent : baseEnd_3477878 < baseStart_3477878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477897 : List Nat := [1, 2, 1, 1, 6, 1, 4, 2, 5]
def baseStart_3477897 : Nat := 118140960795 + 3477897 * 2 ^ 59
def prefixEnd_3477897 : Nat := 4983230072969 + 3 ^ 40 * 3477897 * 2
def baseEnd_3477897 : Nat := 198425869758898271743661

theorem tailTrace_3477897 : CollatzResearch.WordTrace tailWord_3477897 prefixEnd_3477897 198425869758898271743661 := by
  unfold tailWord_3477897
  simp only [CollatzResearch.WordTrace]
  refine ⟨126849324681180621363743945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84566216454120414242495963 126849324681180621363743945)
  ·
    refine ⟨95136993510885466022807959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126849324681180621363743945 95136993510885466022807959)
    ·
      refine ⟨142705490266328199034211939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95136993510885466022807959 142705490266328199034211939)
      ·
        refine ⟨214058235399492298551317909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142705490266328199034211939 214058235399492298551317909)
        ·
          refine ⟨10033979784351201494593027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 214058235399492298551317909 10033979784351201494593027)
          ·
            refine ⟨15050969676526802241889541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10033979784351201494593027 15050969676526802241889541)
            ·
              refine ⟨2822056814348775420354289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15050969676526802241889541 2822056814348775420354289)
              ·
                refine ⟨2116542610761581565265717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2822056814348775420354289 2116542610761581565265717)
                ·
                  refine ⟨198425869758898271743661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2116542610761581565265717 198425869758898271743661)
                  ·
                    rfl

theorem cell23_3477897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 2, 5].length) (baseStart_3477897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477897 prefixEnd_3477897 := by exact prefixLift 3477897
  have htrace : WordTrace (prefixWord ++ tailWord_3477897) baseStart_3477897 baseEnd_3477897 := by
    simpa [prefixWord, tailWord_3477897, baseEnd_3477897] using wordTrace_append hprefix tailTrace_3477897
  have hstable : (prefixWord ++ tailWord_3477897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477897).length < 2 ^ (prefixWord ++ tailWord_3477897).sum := by decide
  have hdescent : baseEnd_3477897 < baseStart_3477897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477900 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 2, 5, 2]
def baseStart_3477900 : Nat := 118140960795 + 3477900 * 2 ^ 59
def prefixEnd_3477900 : Nat := 4983230072969 + 3 ^ 40 * 3477900 * 2
def baseEnd_3477900 : Nat := 1785834368272047933955435

theorem tailTrace_3477900 : CollatzResearch.WordTrace tailWord_3477900 prefixEnd_3477900 1785834368272047933955435 := by
  unfold tailWord_3477900
  simp only [CollatzResearch.WordTrace]
  refine ⟨63424717050084876438051577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84566289400113168584068769 63424717050084876438051577)
  ·
    refine ⟨47568537787563657328538683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63424717050084876438051577 47568537787563657328538683)
    ·
      refine ⟨71352806681345485992808025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47568537787563657328538683 71352806681345485992808025)
      ·
        refine ⟨53514605011009114494606019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71352806681345485992808025 53514605011009114494606019)
        ·
          refine ⟨80271907516513671741909029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53514605011009114494606019 80271907516513671741909029)
          ·
            refine ⟨15050982659346313451607943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80271907516513671741909029 15050982659346313451607943)
            ·
              refine ⟨22576473989019470177411915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15050982659346313451607943 22576473989019470177411915)
              ·
                refine ⟨33864710983529205266117873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22576473989019470177411915 33864710983529205266117873)
                ·
                  refine ⟨25398533237646903949588405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33864710983529205266117873 25398533237646903949588405)
                  ·
                    refine ⟨2381112491029397245273913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25398533237646903949588405 2381112491029397245273913)
                    ·
                      refine ⟨1785834368272047933955435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2381112491029397245273913 1785834368272047933955435)
                      ·
                        rfl

theorem cell23_3477900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 2, 5, 2].length) (baseStart_3477900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477900 prefixEnd_3477900 := by exact prefixLift 3477900
  have htrace : WordTrace (prefixWord ++ tailWord_3477900) baseStart_3477900 baseEnd_3477900 := by
    simpa [prefixWord, tailWord_3477900, baseEnd_3477900] using wordTrace_append hprefix tailTrace_3477900
  have hstable : (prefixWord ++ tailWord_3477900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477900).length < 2 ^ (prefixWord ++ tailWord_3477900).sum := by decide
  have hdescent : baseEnd_3477900 < baseStart_3477900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477913 : List Nat := [1, 2, 1, 2, 1, 4, 2, 2, 1, 3, 4]
def baseStart_3477913 : Nat := 118140960795 + 3477913 * 2 ^ 59
def prefixEnd_3477913 : Nat := 4983230072969 + 3 ^ 40 * 3477913 * 2
def baseEnd_3477913 : Nat := 1785841043520556383092875

theorem tailTrace_3477913 : CollatzResearch.WordTrace tailWord_3477913 prefixEnd_3477913 1785841043520556383092875 := by
  unfold tailWord_3477913
  simp only [CollatzResearch.WordTrace]
  refine ⟨126849908249122656096326393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84566605499415104064217595 126849908249122656096326393)
  ·
    refine ⟨95137431186841992072244795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126849908249122656096326393 95137431186841992072244795)
    ·
      refine ⟨142706146780262988108367193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95137431186841992072244795 142706146780262988108367193)
      ·
        refine ⟨107029610085197241081275395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142706146780262988108367193 107029610085197241081275395)
        ·
          refine ⟨160544415127795861621913093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107029610085197241081275395 160544415127795861621913093)
          ·
            refine ⟨30102077836461724054108705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160544415127795861621913093 30102077836461724054108705)
            ·
              refine ⟨22576558377346293040581529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30102077836461724054108705 22576558377346293040581529)
              ·
                refine ⟨16932418783009719780436147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22576558377346293040581529 16932418783009719780436147)
                ·
                  refine ⟨25398628174514579670654221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16932418783009719780436147 25398628174514579670654221)
                  ·
                    refine ⟨9524485565442967376495333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25398628174514579670654221 9524485565442967376495333)
                    ·
                      refine ⟨1785841043520556383092875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9524485565442967376495333 1785841043520556383092875)
                      ·
                        rfl

theorem cell23_3477913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_3477913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477913 prefixEnd_3477913 := by exact prefixLift 3477913
  have htrace : WordTrace (prefixWord ++ tailWord_3477913) baseStart_3477913 baseEnd_3477913 := by
    simpa [prefixWord, tailWord_3477913, baseEnd_3477913] using wordTrace_append hprefix tailTrace_3477913
  have hstable : (prefixWord ++ tailWord_3477913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477913).length < 2 ^ (prefixWord ++ tailWord_3477913).sum := by decide
  have hdescent : baseEnd_3477913 < baseStart_3477913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477927 : List Nat := [1, 1, 6, 1, 1, 4, 1, 1, 2, 5]
def baseStart_3477927 : Nat := 118140960795 + 3477927 * 2 ^ 59
def prefixEnd_3477927 : Nat := 4983230072969 + 3 ^ 40 * 3477927 * 2
def baseEnd_3477927 : Nat := 595282744083239776105937

theorem tailTrace_3477927 : CollatzResearch.WordTrace tailWord_3477927 prefixEnd_3477927 595282744083239776105937 := by
  unfold tailWord_3477927
  simp only [CollatzResearch.WordTrace]
  refine ⟨126850418871071936487336035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84566945914047957658224023 126850418871071936487336035)
  ·
    refine ⟨190275628306607904731004053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126850418871071936487336035 190275628306607904731004053)
    ·
      refine ⟨8919170076872245534265815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 190275628306607904731004053 8919170076872245534265815)
      ·
        refine ⟨13378755115308368301398723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8919170076872245534265815 13378755115308368301398723)
        ·
          refine ⟨20068132672962552452098085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13378755115308368301398723 20068132672962552452098085)
          ·
            refine ⟨3762774876180478584768391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20068132672962552452098085 3762774876180478584768391)
            ·
              refine ⟨5644162314270717877152587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3762774876180478584768391 5644162314270717877152587)
              ·
                refine ⟨8466243471406076815728881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5644162314270717877152587 8466243471406076815728881)
                ·
                  refine ⟨6349682603554557611796661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8466243471406076815728881 6349682603554557611796661)
                  ·
                    refine ⟨595282744083239776105937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6349682603554557611796661 595282744083239776105937)
                    ·
                      rfl

theorem cell23_3477927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_3477927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477927 prefixEnd_3477927 := by exact prefixLift 3477927
  have htrace : WordTrace (prefixWord ++ tailWord_3477927) baseStart_3477927 baseEnd_3477927 := by
    simpa [prefixWord, tailWord_3477927, baseEnd_3477927] using wordTrace_append hprefix tailTrace_3477927
  have hstable : (prefixWord ++ tailWord_3477927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477927).length < 2 ^ (prefixWord ++ tailWord_3477927).sum := by decide
  have hdescent : baseEnd_3477927 < baseStart_3477927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477943 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 6]
def baseStart_3477943 : Nat := 118140960795 + 3477943 * 2 ^ 59
def prefixEnd_3477943 : Nat := 4983230072969 + 3 ^ 40 * 3477943 * 2
def baseEnd_3477943 : Nat := 1785856447940191265717737

theorem tailTrace_3477943 : CollatzResearch.WordTrace tailWord_3477943 prefixEnd_3477943 1785856447940191265717737 := by
  unfold tailWord_3477943
  simp only [CollatzResearch.WordTrace]
  refine ⟨126851002439013971219918483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84567334959342647479945655 126851002439013971219918483)
  ·
    refine ⟨190276503658520956829877725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126851002439013971219918483 190276503658520956829877725)
    ·
      refine ⟨71353688871945358811204147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190276503658520956829877725 71353688871945358811204147)
      ·
        refine ⟨107030533307918038216806221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71353688871945358811204147 107030533307918038216806221)
        ·
          refine ⟨40136449990469264331302333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107030533307918038216806221 40136449990469264331302333)
          ·
            refine ⟨15051168746425974124238375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40136449990469264331302333 15051168746425974124238375)
            ·
              refine ⟨22576753119638961186357563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15051168746425974124238375 22576753119638961186357563)
              ·
                refine ⟨33865129679458441779536345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22576753119638961186357563 33865129679458441779536345)
                ·
                  refine ⟨25398847259593831334652259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33865129679458441779536345 25398847259593831334652259)
                  ·
                    refine ⟨38098270889390747001978389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25398847259593831334652259 38098270889390747001978389)
                    ·
                      refine ⟨1785856447940191265717737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38098270889390747001978389 1785856447940191265717737)
                      ·
                        rfl

theorem cell23_3477943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_3477943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3477943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3477943 prefixEnd_3477943 := by exact prefixLift 3477943
  have htrace : WordTrace (prefixWord ++ tailWord_3477943) baseStart_3477943 baseEnd_3477943 := by
    simpa [prefixWord, tailWord_3477943, baseEnd_3477943] using wordTrace_append hprefix tailTrace_3477943
  have hstable : (prefixWord ++ tailWord_3477943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477943).length < 2 ^ (prefixWord ++ tailWord_3477943).sum := by decide
  have hdescent : baseEnd_3477943 < baseStart_3477943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478000 : List Nat := [2, 1, 1, 1, 3, 3, 1, 5, 1, 5]
def baseStart_3478000 : Nat := 118140960795 + 3478000 * 2 ^ 59
def prefixEnd_3478000 : Nat := 4983230072969 + 3 ^ 40 * 3478000 * 2
def baseEnd_3478000 : Nat := 595295238779165847568325

theorem tailTrace_3478000 : CollatzResearch.WordTrace tailWord_3478000 prefixEnd_3478000 595295238779165847568325 := by
  unfold tailWord_3478000
  simp only [CollatzResearch.WordTrace]
  refine ⟨63426540699903734977371727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84568720933204979969828969 63426540699903734977371727)
  ·
    refine ⟨95139811049855602466057591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63426540699903734977371727 95139811049855602466057591)
    ·
      refine ⟨142709716574783403699086387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95139811049855602466057591 142709716574783403699086387)
      ·
        refine ⟨214064574862175105548629581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142709716574783403699086387 214064574862175105548629581)
        ·
          refine ⟨80274215573315664580736093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214064574862175105548629581 80274215573315664580736093)
          ·
            refine ⟨30102830839993374217776035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80274215573315664580736093 30102830839993374217776035)
            ·
              refine ⟨45154246259990061326664053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30102830839993374217776035 45154246259990061326664053)
              ·
                refine ⟨4233210586874068249374755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45154246259990061326664053 4233210586874068249374755)
                ·
                  refine ⟨6349815880311102374062133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4233210586874068249374755 6349815880311102374062133)
                  ·
                    refine ⟨595295238779165847568325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6349815880311102374062133 595295238779165847568325)
                    ·
                      rfl

theorem cell23_3478000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 1, 5].length) (baseStart_3478000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478000 prefixEnd_3478000 := by exact prefixLift 3478000
  have htrace : WordTrace (prefixWord ++ tailWord_3478000) baseStart_3478000 baseEnd_3478000 := by
    simpa [prefixWord, tailWord_3478000, baseEnd_3478000] using wordTrace_append hprefix tailTrace_3478000
  have hstable : (prefixWord ++ tailWord_3478000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478000).length < 2 ^ (prefixWord ++ tailWord_3478000).sum := by decide
  have hdescent : baseEnd_3478000 < baseStart_3478000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478063 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 8]
def baseStart_3478063 : Nat := 118140960795 + 3478063 * 2 ^ 59
def prefixEnd_3478063 : Nat := 4983230072969 + 3 ^ 40 * 3478063 * 2
def baseEnd_3478063 : Nat := 1785918065618730796217185

theorem tailTrace_3478063 : CollatzResearch.WordTrace tailWord_3478063 prefixEnd_3478063 1785918065618730796217185 := by
  unfold tailWord_3478063
  simp only [CollatzResearch.WordTrace]
  refine ⟨126855379198579231714286843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84570252799052821142857895 126855379198579231714286843)
  ·
    refine ⟨190283068797868847571430265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126855379198579231714286843 190283068797868847571430265)
    ·
      refine ⟨142712301598401635678572699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190283068797868847571430265 142712301598401635678572699)
      ·
        refine ⟨214068452397602453517859049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142712301598401635678572699 214068452397602453517859049)
        ·
          refine ⟨160551339298201840138394287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214068452397602453517859049 160551339298201840138394287)
          ·
            refine ⟨240827008947302760207591431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160551339298201840138394287 240827008947302760207591431)
            ·
              refine ⟨361240513420954140311387147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240827008947302760207591431 361240513420954140311387147)
              ·
                refine ⟨541860770131431210467080721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361240513420954140311387147 541860770131431210467080721)
                ·
                  refine ⟨406395577598573407850310541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541860770131431210467080721 406395577598573407850310541)
                  ·
                    refine ⟨152398341599465027943866453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 406395577598573407850310541 152398341599465027943866453)
                    ·
                      refine ⟨1785918065618730796217185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 152398341599465027943866453 1785918065618730796217185)
                      ·
                        rfl

theorem cell23_3478063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 8].length) (baseStart_3478063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478063 prefixEnd_3478063 := by exact prefixLift 3478063
  have htrace : WordTrace (prefixWord ++ tailWord_3478063) baseStart_3478063 baseEnd_3478063 := by
    simpa [prefixWord, tailWord_3478063, baseEnd_3478063] using wordTrace_append hprefix tailTrace_3478063
  have hstable : (prefixWord ++ tailWord_3478063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478063).length < 2 ^ (prefixWord ++ tailWord_3478063).sum := by decide
  have hdescent : baseEnd_3478063 < baseStart_3478063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478071 : List Nat := [1, 1, 3, 1, 2, 3, 3, 4, 1, 2, 2]
def baseStart_3478071 : Nat := 118140960795 + 3478071 * 2 ^ 59
def prefixEnd_3478071 : Nat := 4983230072969 + 3 ^ 40 * 3478071 * 2
def baseEnd_3478071 : Nat := 1785922173463966764917149

theorem tailTrace_3478071 : CollatzResearch.WordTrace tailWord_3478071 prefixEnd_3478071 1785922173463966764917149 := by
  unfold tailWord_3478071
  simp only [CollatzResearch.WordTrace]
  refine ⟨126855670982550249080578067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84570447321700166053718711 126855670982550249080578067)
  ·
    refine ⟨190283506473825373620867101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126855670982550249080578067 190283506473825373620867101)
    ·
      refine ⟨71356314927684515107825163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190283506473825373620867101 71356314927684515107825163)
      ·
        refine ⟨107034472391526772661737745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71356314927684515107825163 107034472391526772661737745)
        ·
          refine ⟨80275854293645079496303309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107034472391526772661737745 80275854293645079496303309)
          ·
            refine ⟨30103445360116904811113741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80275854293645079496303309 30103445360116904811113741)
            ·
              refine ⟨11288792010043839304167653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30103445360116904811113741 11288792010043839304167653)
              ·
                refine ⟨2116648501883219869531435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11288792010043839304167653 2116648501883219869531435)
                ·
                  refine ⟨3174972752824829804297153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2116648501883219869531435 3174972752824829804297153)
                  ·
                    refine ⟨2381229564618622353222865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3174972752824829804297153 2381229564618622353222865)
                    ·
                      refine ⟨1785922173463966764917149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2381229564618622353222865 1785922173463966764917149)
                      ·
                        rfl

theorem cell23_3478071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 4, 1, 2, 2].length) (baseStart_3478071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478071 prefixEnd_3478071 := by exact prefixLift 3478071
  have htrace : WordTrace (prefixWord ++ tailWord_3478071) baseStart_3478071 baseEnd_3478071 := by
    simpa [prefixWord, tailWord_3478071, baseEnd_3478071] using wordTrace_append hprefix tailTrace_3478071
  have hstable : (prefixWord ++ tailWord_3478071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478071).length < 2 ^ (prefixWord ++ tailWord_3478071).sum := by decide
  have hdescent : baseEnd_3478071 < baseStart_3478071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478077 : List Nat := [1, 4, 1, 3, 2, 3, 1, 8]
def baseStart_3478077 : Nat := 118140960795 + 3478077 * 2 ^ 59
def prefixEnd_3478077 : Nat := 4983230072969 + 3 ^ 40 * 3478077 * 2
def baseEnd_3478077 : Nat := 66145379790662731164523

theorem tailTrace_3478077 : CollatzResearch.WordTrace tailWord_3478077 prefixEnd_3478077 66145379790662731164523 := by
  unfold tailWord_3478077
  simp only [CollatzResearch.WordTrace]
  refine ⟨126855889820528512105296485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84570593213685674736864323 126855889820528512105296485)
  ·
    refine ⟨23785479341349096019743091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126855889820528512105296485 23785479341349096019743091)
    ·
      refine ⟨35678219012023644029614637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23785479341349096019743091 35678219012023644029614637)
      ·
        refine ⟨13379332129508866511105489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35678219012023644029614637 13379332129508866511105489)
        ·
          refine ⟨10034499097131649883329117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13379332129508866511105489 10034499097131649883329117)
          ·
            refine ⟨3762937161424368706248419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10034499097131649883329117 3762937161424368706248419)
            ·
              refine ⟨5644405742136553059372629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3762937161424368706248419 5644405742136553059372629)
              ·
                refine ⟨66145379790662731164523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5644405742136553059372629 66145379790662731164523)
                ·
                  rfl

theorem cell23_3478077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 8].length) (baseStart_3478077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478077 prefixEnd_3478077 := by exact prefixLift 3478077
  have htrace : WordTrace (prefixWord ++ tailWord_3478077) baseStart_3478077 baseEnd_3478077 := by
    simpa [prefixWord, tailWord_3478077, baseEnd_3478077] using wordTrace_append hprefix tailTrace_3478077
  have hstable : (prefixWord ++ tailWord_3478077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478077).length < 2 ^ (prefixWord ++ tailWord_3478077).sum := by decide
  have hdescent : baseEnd_3478077 < baseStart_3478077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478087 : List Nat := [1, 1, 4, 1, 4, 1, 1, 3, 1, 3, 3]
def baseStart_3478087 : Nat := 118140960795 + 3478087 * 2 ^ 59
def prefixEnd_3478087 : Nat := 4983230072969 + 3 ^ 40 * 3478087 * 2
def baseEnd_3478087 : Nat := 1785930389154438702317075

theorem tailTrace_3478087 : CollatzResearch.WordTrace tailWord_3478087 prefixEnd_3478087 1785930389154438702317075 := by
  unfold tailWord_3478087
  simp only [CollatzResearch.WordTrace]
  refine ⟨126856254550492283813160515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84570836366994855875440343 126856254550492283813160515)
  ·
    refine ⟨190284381825738425719740773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126856254550492283813160515 190284381825738425719740773)
    ·
      refine ⟨35678321592325954822451395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190284381825738425719740773 35678321592325954822451395)
      ·
        refine ⟨53517482388488932233677093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35678321592325954822451395 53517482388488932233677093)
        ·
          refine ⟨10034527947841674793814455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53517482388488932233677093 10034527947841674793814455)
          ·
            refine ⟨15051791921762512190721683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10034527947841674793814455 15051791921762512190721683)
            ·
              refine ⟨22577687882643768286082525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15051791921762512190721683 22577687882643768286082525)
              ·
                refine ⟨8466632955991413107280947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22577687882643768286082525 8466632955991413107280947)
                ·
                  refine ⟨12699949433987119660921421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8466632955991413107280947 12699949433987119660921421)
                  ·
                    refine ⟨4762481037745169872845533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12699949433987119660921421 4762481037745169872845533)
                    ·
                      refine ⟨1785930389154438702317075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4762481037745169872845533 1785930389154438702317075)
                      ·
                        rfl

theorem cell23_3478087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_3478087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478087 prefixEnd_3478087 := by exact prefixLift 3478087
  have htrace : WordTrace (prefixWord ++ tailWord_3478087) baseStart_3478087 baseEnd_3478087 := by
    simpa [prefixWord, tailWord_3478087, baseEnd_3478087] using wordTrace_append hprefix tailTrace_3478087
  have hstable : (prefixWord ++ tailWord_3478087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478087).length < 2 ^ (prefixWord ++ tailWord_3478087).sum := by decide
  have hdescent : baseEnd_3478087 < baseStart_3478087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478108 : List Nat := [2, 2, 4, 1, 3, 2, 2, 1, 1, 2, 3]
def baseStart_3478108 : Nat := 118140960795 + 3478108 * 2 ^ 59
def prefixEnd_3478108 : Nat := 4983230072969 + 3 ^ 40 * 3478108 * 2
def baseEnd_3478108 : Nat := 1785941172248183120154479

theorem tailTrace_3478108 : CollatzResearch.WordTrace tailWord_3478108 prefixEnd_3478108 1785941172248183120154479 := by
  unfold tailWord_3478108
  simp only [CollatzResearch.WordTrace]
  refine ⟨63428510241708102199837489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84571346988944136266449985 63428510241708102199837489)
  ·
    refine ⟨47571382681281076649878117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63428510241708102199837489 47571382681281076649878117)
    ·
      refine ⟨8919634252740201871852147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47571382681281076649878117 8919634252740201871852147)
      ·
        refine ⟨13379451379110302807778221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8919634252740201871852147 13379451379110302807778221)
        ·
          refine ⟨5017294267166363552916833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13379451379110302807778221 5017294267166363552916833)
          ·
            refine ⟨3762970700374772664687625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5017294267166363552916833 3762970700374772664687625)
            ·
              refine ⟨2822228025281079498515719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3762970700374772664687625 2822228025281079498515719)
              ·
                refine ⟨4233342037921619247773579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2822228025281079498515719 4233342037921619247773579)
                ·
                  refine ⟨6350013056882428871660369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4233342037921619247773579 6350013056882428871660369)
                  ·
                    refine ⟨4762509792661821653745277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6350013056882428871660369 4762509792661821653745277)
                    ·
                      refine ⟨1785941172248183120154479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4762509792661821653745277 1785941172248183120154479)
                      ·
                        rfl

theorem cell23_3478108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_3478108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478108 prefixEnd_3478108 := by exact prefixLift 3478108
  have htrace : WordTrace (prefixWord ++ tailWord_3478108) baseStart_3478108 baseEnd_3478108 := by
    simpa [prefixWord, tailWord_3478108, baseEnd_3478108] using wordTrace_append hprefix tailTrace_3478108
  have hstable : (prefixWord ++ tailWord_3478108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478108).length < 2 ^ (prefixWord ++ tailWord_3478108).sum := by decide
  have hdescent : baseEnd_3478108 < baseStart_3478108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478127 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 3, 4, 2]
def baseStart_3478127 : Nat := 118140960795 + 3478127 * 2 ^ 59
def prefixEnd_3478127 : Nat := 4983230072969 + 3 ^ 40 * 3478127 * 2
def baseEnd_3478127 : Nat := 1785950928380618545816891

theorem tailTrace_3478127 : CollatzResearch.WordTrace tailWord_3478127 prefixEnd_3478127 1785950928380618545816891 := by
  unfold tailWord_3478127
  simp only [CollatzResearch.WordTrace]
  refine ⟨126857713470347370644616635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84571808980231580429744423 126857713470347370644616635)
  ·
    refine ⟨190286570205521055966924953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126857713470347370644616635 190286570205521055966924953)
    ·
      refine ⟨142714927654140791975193715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190286570205521055966924953 142714927654140791975193715)
      ·
        refine ⟨214072391481211187962790573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142714927654140791975193715 214072391481211187962790573)
        ·
          refine ⟨80277146805454195486046465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214072391481211187962790573 80277146805454195486046465)
          ·
            refine ⟨60207860104090646614534849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80277146805454195486046465 60207860104090646614534849)
            ·
              refine ⟨45155895078067984960901137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60207860104090646614534849 45155895078067984960901137)
              ·
                refine ⟨33866921308550988720675853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45155895078067984960901137 33866921308550988720675853)
                ·
                  refine ⟨12700095490706620770253445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33866921308550988720675853 12700095490706620770253445)
                  ·
                    refine ⟨2381267904507491394422521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12700095490706620770253445 2381267904507491394422521)
                    ·
                      refine ⟨1785950928380618545816891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2381267904507491394422521 1785950928380618545816891)
                      ·
                        rfl

theorem cell23_3478127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 4, 2].length) (baseStart_3478127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478127 prefixEnd_3478127 := by exact prefixLift 3478127
  have htrace : WordTrace (prefixWord ++ tailWord_3478127) baseStart_3478127 baseEnd_3478127 := by
    simpa [prefixWord, tailWord_3478127, baseEnd_3478127] using wordTrace_append hprefix tailTrace_3478127
  have hstable : (prefixWord ++ tailWord_3478127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478127).length < 2 ^ (prefixWord ++ tailWord_3478127).sum := by decide
  have hdescent : baseEnd_3478127 < baseStart_3478127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478144 : List Nat := [2, 1, 1, 2, 1, 5, 3, 1, 1, 4, 2]
def baseStart_3478144 : Nat := 118140960795 + 3478144 * 2 ^ 59
def prefixEnd_3478144 : Nat := 4983230072969 + 3 ^ 40 * 3478144 * 2
def baseEnd_3478144 : Nat := 1785959657551744979304313

theorem tailTrace_3478144 : CollatzResearch.WordTrace tailWord_3478144 prefixEnd_3478144 1785959657551744979304313 := by
  unfold tailWord_3478144
  simp only [CollatzResearch.WordTrace]
  refine ⟨63429166755642891273992743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84572222340857188365323657 63429166755642891273992743)
  ·
    refine ⟨95143750133464336910989115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63429166755642891273992743 95143750133464336910989115)
    ·
      refine ⟨142715625200196505366483673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95143750133464336910989115 142715625200196505366483673)
      ·
        refine ⟨107036718900147379024862755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142715625200196505366483673 107036718900147379024862755)
        ·
          refine ⟨160555078350221068537294133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107036718900147379024862755 160555078350221068537294133)
          ·
            refine ⟨15052038595333225175371325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160555078350221068537294133 15052038595333225175371325)
            ·
              refine ⟨5644514473249959440764247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15052038595333225175371325 5644514473249959440764247)
              ·
                refine ⟨8466771709874939161146371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5644514473249959440764247 8466771709874939161146371)
                ·
                  refine ⟨12700157564812408741719557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8466771709874939161146371 12700157564812408741719557)
                  ·
                    refine ⟨2381279543402326639072417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12700157564812408741719557 2381279543402326639072417)
                    ·
                      refine ⟨1785959657551744979304313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2381279543402326639072417 1785959657551744979304313)
                      ·
                        rfl

theorem cell23_3478144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 1, 4, 2].length) (baseStart_3478144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478144 prefixEnd_3478144 := by exact prefixLift 3478144
  have htrace : WordTrace (prefixWord ++ tailWord_3478144) baseStart_3478144 baseEnd_3478144 := by
    simpa [prefixWord, tailWord_3478144, baseEnd_3478144] using wordTrace_append hprefix tailTrace_3478144
  have hstable : (prefixWord ++ tailWord_3478144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478144).length < 2 ^ (prefixWord ++ tailWord_3478144).sum := by decide
  have hdescent : baseEnd_3478144 < baseStart_3478144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478164 : List Nat := [2, 4, 2, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_3478164 : Nat := 118140960795 + 3478164 * 2 ^ 59
def prefixEnd_3478164 : Nat := 4983230072969 + 3 ^ 40 * 3478164 * 2
def baseEnd_3478164 : Nat := 1785969927164834901054221

theorem tailTrace_3478164 : CollatzResearch.WordTrace tailWord_3478164 prefixEnd_3478164 1785969927164834901054221 := by
  unfold tailWord_3478164
  simp only [CollatzResearch.WordTrace]
  refine ⟨63429531485606662981856773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84572708647475550642475697 63429531485606662981856773)
  ·
    refine ⟨11893037153551249309098145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63429531485606662981856773 11893037153551249309098145)
    ·
      refine ⟨8919777865163436981823609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11893037153551249309098145 8919777865163436981823609)
      ·
        refine ⟨6689833398872577736367707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8919777865163436981823609 6689833398872577736367707)
        ·
          refine ⟨10034750098308866604551561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6689833398872577736367707 10034750098308866604551561)
          ·
            refine ⟨7526062573731649953413671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10034750098308866604551561 7526062573731649953413671)
            ·
              refine ⟨11289093860597474930120507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7526062573731649953413671 11289093860597474930120507)
              ·
                refine ⟨16933640790896212395180761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11289093860597474930120507 16933640790896212395180761)
                ·
                  refine ⟨12700230593172159296385571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16933640790896212395180761 12700230593172159296385571)
                  ·
                    refine ⟨19050345889758238944578357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12700230593172159296385571 19050345889758238944578357)
                    ·
                      refine ⟨1785969927164834901054221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19050345889758238944578357 1785969927164834901054221)
                      ·
                        rfl

theorem cell23_3478164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_3478164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478164 prefixEnd_3478164 := by exact prefixLift 3478164
  have htrace : WordTrace (prefixWord ++ tailWord_3478164) baseStart_3478164 baseEnd_3478164 := by
    simpa [prefixWord, tailWord_3478164, baseEnd_3478164] using wordTrace_append hprefix tailTrace_3478164
  have hstable : (prefixWord ++ tailWord_3478164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478164).length < 2 ^ (prefixWord ++ tailWord_3478164).sum := by decide
  have hdescent : baseEnd_3478164 < baseStart_3478164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478234 : List Nat := [3, 1, 1, 2, 2, 2, 2, 2, 2, 4, 2]
def baseStart_3478234 : Nat := 118140960795 + 3478234 * 2 ^ 59
def prefixEnd_3478234 : Nat := 4983230072969 + 3 ^ 40 * 3478234 * 2
def baseEnd_3478234 : Nat := 1786005870810649627178899

theorem tailTrace_3478234 : CollatzResearch.WordTrace tailWord_3478234 prefixEnd_3478234 1786005870810649627178899 := by
  unfold tailWord_3478234
  simp only [CollatzResearch.WordTrace]
  refine ⟨31715404020239931979690439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84574410720639818612507837 31715404020239931979690439)
  ·
    refine ⟨47573106030359897969535659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31715404020239931979690439 47573106030359897969535659)
    ·
      refine ⟨71359659045539846954303489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47573106030359897969535659 71359659045539846954303489)
      ·
        refine ⟨53519744284154885215727617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71359659045539846954303489 53519744284154885215727617)
        ·
          refine ⟨40139808213116163911795713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53519744284154885215727617 40139808213116163911795713)
          ·
            refine ⟨30104856159837122933846785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40139808213116163911795713 30104856159837122933846785)
            ·
              refine ⟨22578642119877842200385089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30104856159837122933846785 22578642119877842200385089)
              ·
                refine ⟨16933981589908381650288817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22578642119877842200385089 16933981589908381650288817)
                ·
                  refine ⟨12700486192431286237716613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16933981589908381650288817 12700486192431286237716613)
                  ·
                    refine ⟨2381341161080866169571865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12700486192431286237716613 2381341161080866169571865)
                    ·
                      refine ⟨1786005870810649627178899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2381341161080866169571865 1786005870810649627178899)
                      ·
                        rfl

theorem cell23_3478234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 2, 4, 2].length) (baseStart_3478234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478234 prefixEnd_3478234 := by exact prefixLift 3478234
  have htrace : WordTrace (prefixWord ++ tailWord_3478234) baseStart_3478234 baseEnd_3478234 := by
    simpa [prefixWord, tailWord_3478234, baseEnd_3478234] using wordTrace_append hprefix tailTrace_3478234
  have hstable : (prefixWord ++ tailWord_3478234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478234).length < 2 ^ (prefixWord ++ tailWord_3478234).sum := by decide
  have hdescent : baseEnd_3478234 < baseStart_3478234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478257 : List Nat := [1, 2, 2, 2, 2, 2, 1, 5, 6]
def baseStart_3478257 : Nat := 118140960795 + 3478257 * 2 ^ 59
def prefixEnd_3478257 : Nat := 4983230072969 + 3 ^ 40 * 3478257 * 2
def baseEnd_3478257 : Nat := 198446408985078115243477

theorem tailTrace_3478257 : CollatzResearch.WordTrace tailWord_3478257 prefixEnd_3478257 198446408985078115243477 := by
  unfold tailWord_3478257
  simp only [CollatzResearch.WordTrace]
  refine ⟨126862454959876402846849025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84574969973250935231232683 126862454959876402846849025)
  ·
    refine ⟨95146841219907302135136769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126862454959876402846849025 95146841219907302135136769)
    ·
      refine ⟨71360130914930476601352577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95146841219907302135136769 71360130914930476601352577)
      ·
        refine ⟨53520098186197857451014433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71360130914930476601352577 53520098186197857451014433)
        ·
          refine ⟨40140073639648393088260825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53520098186197857451014433 40140073639648393088260825)
          ·
            refine ⟨30105055229736294816195619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40140073639648393088260825 30105055229736294816195619)
            ·
              refine ⟨45157582844604442224293429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30105055229736294816195619 45157582844604442224293429)
              ·
                refine ⟨4233523391681666458527509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45157582844604442224293429 4233523391681666458527509)
                ·
                  refine ⟨198446408985078115243477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4233523391681666458527509 198446408985078115243477)
                  ·
                    rfl

theorem cell23_3478257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 6].length) (baseStart_3478257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478257 prefixEnd_3478257 := by exact prefixLift 3478257
  have htrace : WordTrace (prefixWord ++ tailWord_3478257) baseStart_3478257 baseEnd_3478257 := by
    simpa [prefixWord, tailWord_3478257, baseEnd_3478257] using wordTrace_append hprefix tailTrace_3478257
  have hstable : (prefixWord ++ tailWord_3478257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478257).length < 2 ^ (prefixWord ++ tailWord_3478257).sum := by decide
  have hdescent : baseEnd_3478257 < baseStart_3478257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478284 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 7, 1, 3]
def baseStart_3478284 : Nat := 118140960795 + 3478284 * 2 ^ 59
def prefixEnd_3478284 : Nat := 4983230072969 + 3 ^ 40 * 3478284 * 2
def baseEnd_3478284 : Nat := 1786031544843374431553669

theorem tailTrace_3478284 : CollatzResearch.WordTrace tailWord_3478284 prefixEnd_3478284 1786031544843374431553669 := by
  unfold tailWord_3478284
  simp only [CollatzResearch.WordTrace]
  refine ⟨63431719865389293229040953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84575626487185724305387937 63431719865389293229040953)
  ·
    refine ⟨47573789899041969921780715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63431719865389293229040953 47573789899041969921780715)
    ·
      refine ⟨71360684848562954882671073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47573789899041969921780715 71360684848562954882671073)
      ·
        refine ⟨53520513636422216162003305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71360684848562954882671073 53520513636422216162003305)
        ·
          refine ⟨40140385227316662121502479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53520513636422216162003305 40140385227316662121502479)
          ·
            refine ⟨60210577840974993182253719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40140385227316662121502479 60210577840974993182253719)
            ·
              refine ⟨90315866761462489773380579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60210577840974993182253719 90315866761462489773380579)
              ·
                refine ⟨135473800142193734660070869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90315866761462489773380579 135473800142193734660070869)
                ·
                  refine ⟨3175167190832665656095411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 135473800142193734660070869 3175167190832665656095411)
                  ·
                    refine ⟨4762750786248998484143117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3175167190832665656095411 4762750786248998484143117)
                    ·
                      refine ⟨1786031544843374431553669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4762750786248998484143117 1786031544843374431553669)
                      ·
                        rfl

theorem cell23_3478284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_3478284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478284 prefixEnd_3478284 := by exact prefixLift 3478284
  have htrace : WordTrace (prefixWord ++ tailWord_3478284) baseStart_3478284 baseEnd_3478284 := by
    simpa [prefixWord, tailWord_3478284, baseEnd_3478284] using wordTrace_append hprefix tailTrace_3478284
  have hstable : (prefixWord ++ tailWord_3478284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478284).length < 2 ^ (prefixWord ++ tailWord_3478284).sum := by decide
  have hdescent : baseEnd_3478284 < baseStart_3478284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478318 : List Nat := [4, 1, 3, 2, 1, 1, 2, 2, 3, 1, 3]
def baseStart_3478318 : Nat := 118140960795 + 3478318 * 2 ^ 59
def prefixEnd_3478318 : Nat := 4983230072969 + 3 ^ 40 * 3478318 * 2
def baseEnd_3478318 : Nat := 1786049003185627298528513

theorem tailTrace_3478318 : CollatzResearch.WordTrace tailWord_3478318 prefixEnd_3478318 1786049003185627298528513 := by
  unfold tailWord_3478318
  simp only [CollatzResearch.WordTrace]
  refine ⟨15858084976581926283102451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84576453208436940176546405 15858084976581926283102451)
  ·
    refine ⟨23787127464872889424653677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15858084976581926283102451 23787127464872889424653677)
    ·
      refine ⟨8920172799327333534245129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23787127464872889424653677 8920172799327333534245129)
      ·
        refine ⟨6690129599495500150683847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8920172799327333534245129 6690129599495500150683847)
        ·
          refine ⟨10035194399243250226025771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6690129599495500150683847 10035194399243250226025771)
          ·
            refine ⟨15052791598864875339038657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10035194399243250226025771 15052791598864875339038657)
            ·
              refine ⟨11289593699148656504278993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15052791598864875339038657 11289593699148656504278993)
              ·
                refine ⟨8467195274361492378209245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11289593699148656504278993 8467195274361492378209245)
                ·
                  refine ⟨3175198227885559641828467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8467195274361492378209245 3175198227885559641828467)
                  ·
                    refine ⟨4762797341828339462742701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3175198227885559641828467 4762797341828339462742701)
                    ·
                      refine ⟨1786049003185627298528513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4762797341828339462742701 1786049003185627298528513)
                      ·
                        rfl

theorem cell23_3478318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_3478318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478318 prefixEnd_3478318 := by exact prefixLift 3478318
  have htrace : WordTrace (prefixWord ++ tailWord_3478318) baseStart_3478318 baseEnd_3478318 := by
    simpa [prefixWord, tailWord_3478318, baseEnd_3478318] using wordTrace_append hprefix tailTrace_3478318
  have hstable : (prefixWord ++ tailWord_3478318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478318).length < 2 ^ (prefixWord ++ tailWord_3478318).sum := by decide
  have hdescent : baseEnd_3478318 < baseStart_3478318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478327 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 5]
def baseStart_3478327 : Nat := 118140960795 + 3478327 * 2 ^ 59
def prefixEnd_3478327 : Nat := 4983230072969 + 3 ^ 40 * 3478327 * 2
def baseEnd_3478327 : Nat := 1786053624511517763315971

theorem tailTrace_3478327 : CollatzResearch.WordTrace tailWord_3478327 prefixEnd_3478327 1786053624511517763315971 := by
  unfold tailWord_3478327
  simp only [CollatzResearch.WordTrace]
  refine ⟨126865008069622804801897235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84576672046415203201264823 126865008069622804801897235)
  ·
    refine ⟨190297512104434207202845853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126865008069622804801897235 190297512104434207202845853)
    ·
      refine ⟨71361567039162827701067195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190297512104434207202845853 71361567039162827701067195)
      ·
        refine ⟨107042350558744241551600793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71361567039162827701067195 107042350558744241551600793)
        ·
          refine ⟨80281762919058181163700595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107042350558744241551600793 80281762919058181163700595)
          ·
            refine ⟨120422644378587271745550893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80281762919058181163700595 120422644378587271745550893)
            ·
              refine ⟨45158491641970226904581585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120422644378587271745550893 45158491641970226904581585)
              ·
                refine ⟨33868868731477670178436189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45158491641970226904581585 33868868731477670178436189)
                ·
                  refine ⟨12700825774304126316913571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33868868731477670178436189 12700825774304126316913571)
                  ·
                    refine ⟨19051238661456189475370357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12700825774304126316913571 19051238661456189475370357)
                    ·
                      refine ⟨1786053624511517763315971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19051238661456189475370357 1786053624511517763315971)
                      ·
                        rfl

theorem cell23_3478327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_3478327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478327 prefixEnd_3478327 := by exact prefixLift 3478327
  have htrace : WordTrace (prefixWord ++ tailWord_3478327) baseStart_3478327 baseEnd_3478327 := by
    simpa [prefixWord, tailWord_3478327, baseEnd_3478327] using wordTrace_append hprefix tailTrace_3478327
  have hstable : (prefixWord ++ tailWord_3478327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478327).length < 2 ^ (prefixWord ++ tailWord_3478327).sum := by decide
  have hdescent : baseEnd_3478327 < baseStart_3478327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478335 : List Nat := [1, 1, 2, 2, 5, 3, 1, 3, 1, 1, 3]
def baseStart_3478335 : Nat := 118140960795 + 3478335 * 2 ^ 59
def prefixEnd_3478335 : Nat := 4983230072969 + 3 ^ 40 * 3478335 * 2
def baseEnd_3478335 : Nat := 1786057732356753732015935

theorem tailTrace_3478335 : CollatzResearch.WordTrace tailWord_3478335 prefixEnd_3478335 1786057732356753732015935 := by
  unfold tailWord_3478335
  simp only [CollatzResearch.WordTrace]
  refine ⟨126865299853593822168188459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84576866569062548112125639 126865299853593822168188459)
  ·
    refine ⟨190297949780390733252282689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126865299853593822168188459 190297949780390733252282689)
    ·
      refine ⟨142723462335293049939212017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190297949780390733252282689 142723462335293049939212017)
      ·
        refine ⟨107042596751469787454409013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142723462335293049939212017 107042596751469787454409013)
        ·
          refine ⟨10035243445450292573850845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107042596751469787454409013 10035243445450292573850845)
          ·
            refine ⟨3763216292043859715194067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10035243445450292573850845 3763216292043859715194067)
            ·
              refine ⟨5644824438065789572791101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3763216292043859715194067 5644824438065789572791101)
              ·
                refine ⟨2116809164274671089796663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5644824438065789572791101 2116809164274671089796663)
                ·
                  refine ⟨3175213746412006634694995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2116809164274671089796663 3175213746412006634694995)
                  ·
                    refine ⟨4762820619618009952042493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3175213746412006634694995 4762820619618009952042493)
                    ·
                      refine ⟨1786057732356753732015935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4762820619618009952042493 1786057732356753732015935)
                      ·
                        rfl

theorem cell23_3478335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 3, 1, 1, 3].length) (baseStart_3478335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478335 prefixEnd_3478335 := by exact prefixLift 3478335
  have htrace : WordTrace (prefixWord ++ tailWord_3478335) baseStart_3478335 baseEnd_3478335 := by
    simpa [prefixWord, tailWord_3478335, baseEnd_3478335] using wordTrace_append hprefix tailTrace_3478335
  have hstable : (prefixWord ++ tailWord_3478335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478335).length < 2 ^ (prefixWord ++ tailWord_3478335).sum := by decide
  have hdescent : baseEnd_3478335 < baseStart_3478335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478344 : List Nat := [2, 1, 3, 1, 1, 3, 4, 1, 1, 1, 5]
def baseStart_3478344 : Nat := 118140960795 + 3478344 * 2 ^ 59
def prefixEnd_3478344 : Nat := 4983230072969 + 3 ^ 40 * 3478344 * 2
def baseEnd_3478344 : Nat := 1786062353682644196803393

theorem tailTrace_3478344 : CollatzResearch.WordTrace tailWord_3478344 prefixEnd_3478344 1786062353682644196803393 := by
  unfold tailWord_3478344
  simp only [CollatzResearch.WordTrace]
  refine ⟨63432814055280608352633043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84577085407040811136844057 63432814055280608352633043)
  ·
    refine ⟨95149221082920912528949565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63432814055280608352633043 95149221082920912528949565)
    ·
      refine ⟨35680957906095342198356087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95149221082920912528949565 35680957906095342198356087)
      ·
        refine ⟨53521436859143013297534131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35680957906095342198356087 53521436859143013297534131)
        ·
          refine ⟨80282155288714519946301197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53521436859143013297534131 80282155288714519946301197)
          ·
            refine ⟨30105808233267944979862949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80282155288714519946301197 30105808233267944979862949)
            ·
              refine ⟨5644839043737739683724303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30105808233267944979862949 5644839043737739683724303)
              ·
                refine ⟨8467258565606609525586455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5644839043737739683724303 8467258565606609525586455)
                ·
                  refine ⟨12700887848409914288379683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8467258565606609525586455 12700887848409914288379683)
                  ·
                    refine ⟨19051331772614871432569525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12700887848409914288379683 19051331772614871432569525)
                    ·
                      refine ⟨1786062353682644196803393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19051331772614871432569525 1786062353682644196803393)
                      ·
                        rfl

theorem cell23_3478344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_3478344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478344 prefixEnd_3478344 := by exact prefixLift 3478344
  have htrace : WordTrace (prefixWord ++ tailWord_3478344) baseStart_3478344 baseEnd_3478344 := by
    simpa [prefixWord, tailWord_3478344, baseEnd_3478344] using wordTrace_append hprefix tailTrace_3478344
  have hstable : (prefixWord ++ tailWord_3478344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478344).length < 2 ^ (prefixWord ++ tailWord_3478344).sum := by decide
  have hdescent : baseEnd_3478344 < baseStart_3478344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478364 : List Nat := [2, 2, 4, 2, 1, 1, 1, 10]
def baseStart_3478364 : Nat := 118140960795 + 3478364 * 2 ^ 59
def prefixEnd_3478364 : Nat := 4983230072969 + 3 ^ 40 * 3478364 * 2
def baseEnd_3478364 : Nat := 66150837899842004390863

theorem tailTrace_3478364 : CollatzResearch.WordTrace tailWord_3478364 prefixEnd_3478364 66150837899842004390863 := by
  unfold tailWord_3478364
  simp only [CollatzResearch.WordTrace]
  refine ⟨63433178785244380060497073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84577571713659173413996097 63433178785244380060497073)
  ·
    refine ⟨47574884088933285045372805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63433178785244380060497073 47574884088933285045372805)
    ·
      refine ⟨8920290766674990946007401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47574884088933285045372805 8920290766674990946007401)
      ·
        refine ⟨6690218075006243209505551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8920290766674990946007401 6690218075006243209505551)
        ·
          refine ⟨10035327112509364814258327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6690218075006243209505551 10035327112509364814258327)
          ·
            refine ⟨15052990668764047221387491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10035327112509364814258327 15052990668764047221387491)
            ·
              refine ⟨22579486003146070832081237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15052990668764047221387491 22579486003146070832081237)
              ·
                refine ⟨66150837899842004390863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 22579486003146070832081237 66150837899842004390863)
                ·
                  rfl

theorem cell23_3478364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 10].length) (baseStart_3478364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478364 prefixEnd_3478364 := by exact prefixLift 3478364
  have htrace : WordTrace (prefixWord ++ tailWord_3478364) baseStart_3478364 baseEnd_3478364 := by
    simpa [prefixWord, tailWord_3478364, baseEnd_3478364] using wordTrace_append hprefix tailTrace_3478364
  have hstable : (prefixWord ++ tailWord_3478364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478364).length < 2 ^ (prefixWord ++ tailWord_3478364).sum := by decide
  have hdescent : baseEnd_3478364 < baseStart_3478364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478367 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 6]
def baseStart_3478367 : Nat := 118140960795 + 3478367 * 2 ^ 59
def prefixEnd_3478367 : Nat := 4983230072969 + 3 ^ 40 * 3478367 * 2
def baseEnd_3478367 : Nat := 1786074163737697606815787

theorem tailTrace_3478367 : CollatzResearch.WordTrace tailWord_3478367 prefixEnd_3478367 1786074163737697606815787 := by
  unfold tailWord_3478367
  simp only [CollatzResearch.WordTrace]
  refine ⟨126866466989477891633353355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84577644659651927755568903 126866466989477891633353355)
  ·
    refine ⟨190299700484216837450030033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126866466989477891633353355 190299700484216837450030033)
    ·
      refine ⟨142724775363162628087522525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190299700484216837450030033 142724775363162628087522525)
      ·
        refine ⟨53521790761185985532820947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142724775363162628087522525 53521790761185985532820947)
        ·
          refine ⟨80282686141778978299231421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53521790761185985532820947 80282686141778978299231421)
          ·
            refine ⟨30106007303167116862211783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80282686141778978299231421 30106007303167116862211783)
            ·
              refine ⟨45159010954750675293317675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30106007303167116862211783 45159010954750675293317675)
              ·
                refine ⟨67738516432126012939976513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45159010954750675293317675 67738516432126012939976513)
                ·
                  refine ⟨50803887324094509704982385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67738516432126012939976513 50803887324094509704982385)
                  ·
                    refine ⟨38102915493070882278736789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50803887324094509704982385 38102915493070882278736789)
                    ·
                      refine ⟨1786074163737697606815787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38102915493070882278736789 1786074163737697606815787)
                      ·
                        rfl

theorem cell23_3478367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_3478367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478367 prefixEnd_3478367 := by exact prefixLift 3478367
  have htrace : WordTrace (prefixWord ++ tailWord_3478367) baseStart_3478367 baseEnd_3478367 := by
    simpa [prefixWord, tailWord_3478367, baseEnd_3478367] using wordTrace_append hprefix tailTrace_3478367
  have hstable : (prefixWord ++ tailWord_3478367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478367).length < 2 ^ (prefixWord ++ tailWord_3478367).sum := by decide
  have hdescent : baseEnd_3478367 < baseStart_3478367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478387 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 5]
def baseStart_3478387 : Nat := 118140960795 + 3478387 * 2 ^ 59
def prefixEnd_3478387 : Nat := 4983230072969 + 3 ^ 40 * 3478387 * 2
def baseEnd_3478387 : Nat := 1786084433350787528565695

theorem tailTrace_3478387 : CollatzResearch.WordTrace tailWord_3478387 prefixEnd_3478387 1786084433350787528565695 := by
  unfold tailWord_3478387
  simp only [CollatzResearch.WordTrace]
  refine ⟨126867196449405435049081415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84578130966270290032720943 126867196449405435049081415)
  ·
    refine ⟨190300794674108152573622123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126867196449405435049081415 190300794674108152573622123)
    ·
      refine ⟨285451192011162228860433185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190300794674108152573622123 285451192011162228860433185)
      ·
        refine ⟨214088394008371671645324889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285451192011162228860433185 214088394008371671645324889)
        ·
          refine ⟨160566295506278753733993667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214088394008371671645324889 160566295506278753733993667)
          ·
            refine ⟨240849443259418130600990501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160566295506278753733993667 240849443259418130600990501)
            ·
              refine ⟨45159270611140899487685719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 240849443259418130600990501 45159270611140899487685719)
              ·
                refine ⟨67738905916711349231528579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45159270611140899487685719 67738905916711349231528579)
                ·
                  refine ⟨101608358875067023847292869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67738905916711349231528579 101608358875067023847292869)
                  ·
                    refine ⟨19051567289075066971367413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101608358875067023847292869 19051567289075066971367413)
                    ·
                      refine ⟨1786084433350787528565695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19051567289075066971367413 1786084433350787528565695)
                      ·
                        rfl

theorem cell23_3478387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 5].length) (baseStart_3478387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478387 prefixEnd_3478387 := by exact prefixLift 3478387
  have htrace : WordTrace (prefixWord ++ tailWord_3478387) baseStart_3478387 baseEnd_3478387 := by
    simpa [prefixWord, tailWord_3478387, baseEnd_3478387] using wordTrace_append hprefix tailTrace_3478387
  have hstable : (prefixWord ++ tailWord_3478387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478387).length < 2 ^ (prefixWord ++ tailWord_3478387).sum := by decide
  have hdescent : baseEnd_3478387 < baseStart_3478387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478402 : List Nat := [3, 4, 2, 2, 1, 1, 2, 2, 2, 4]
def baseStart_3478402 : Nat := 118140960795 + 3478402 * 2 ^ 59
def prefixEnd_3478402 : Nat := 4983230072969 + 3 ^ 40 * 3478402 * 2
def baseEnd_3478402 : Nat := 595364045186868323292709

theorem tailTrace_3478402 : CollatzResearch.WordTrace tailWord_3478402 prefixEnd_3478402 595364045186868323292709 := by
  unfold tailWord_3478402
  simp only [CollatzResearch.WordTrace]
  refine ⟨31716935886087773152719365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84578495696234061740584973 31716935886087773152719365)
  ·
    refine ⟨5946925478641457466134881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31716935886087773152719365 5946925478641457466134881)
    ·
      refine ⟨4460194108981093099601161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5946925478641457466134881 4460194108981093099601161)
      ·
        refine ⟨3345145581735819824700871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4460194108981093099601161 3345145581735819824700871)
        ·
          refine ⟨5017718372603729737051307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3345145581735819824700871 5017718372603729737051307)
          ·
            refine ⟨7526577558905594605576961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5017718372603729737051307 7526577558905594605576961)
            ·
              refine ⟨5644933169179195954182721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7526577558905594605576961 5644933169179195954182721)
              ·
                refine ⟨4233699876884396965637041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5644933169179195954182721 4233699876884396965637041)
                ·
                  refine ⟨3175274907663297724227781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4233699876884396965637041 3175274907663297724227781)
                  ·
                    refine ⟨595364045186868323292709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3175274907663297724227781 595364045186868323292709)
                    ·
                      rfl

theorem cell23_3478402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_3478402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478402 prefixEnd_3478402 := by exact prefixLift 3478402
  have htrace : WordTrace (prefixWord ++ tailWord_3478402) baseStart_3478402 baseEnd_3478402 := by
    simpa [prefixWord, tailWord_3478402, baseEnd_3478402] using wordTrace_append hprefix tailTrace_3478402
  have hstable : (prefixWord ++ tailWord_3478402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478402).length < 2 ^ (prefixWord ++ tailWord_3478402).sum := by decide
  have hdescent : baseEnd_3478402 < baseStart_3478402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478408 : List Nat := [2, 1, 3, 3, 2, 1, 1, 4, 2, 1, 3]
def baseStart_3478408 : Nat := 118140960795 + 3478408 * 2 ^ 59
def prefixEnd_3478408 : Nat := 4983230072969 + 3 ^ 40 * 3478408 * 2
def baseEnd_3478408 : Nat := 1786095216444531946403099

theorem tailTrace_3478408 : CollatzResearch.WordTrace tailWord_3478408 prefixEnd_3478408 1786095216444531946403099 := by
  unfold tailWord_3478408
  simp only [CollatzResearch.WordTrace]
  refine ⟨63433981191164677817797939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84578641588219570423730585 63433981191164677817797939)
  ·
    refine ⟨95150971786747016726696909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63433981191164677817797939 95150971786747016726696909)
    ·
      refine ⟨35681614420030131272511341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95150971786747016726696909 35681614420030131272511341)
      ·
        refine ⟨13380605407511299227191753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35681614420030131272511341 13380605407511299227191753)
        ·
          refine ⟨10035454055633474420393815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13380605407511299227191753 10035454055633474420393815)
          ·
            refine ⟨15053181083450211630590723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10035454055633474420393815 15053181083450211630590723)
            ·
              refine ⟨22579771625175317445886085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15053181083450211630590723 22579771625175317445886085)
              ·
                refine ⟨4233707179720372021103641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22579771625175317445886085 4233707179720372021103641)
                ·
                  refine ⟨3175280384790279015827731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4233707179720372021103641 3175280384790279015827731)
                  ·
                    refine ⟨4762920577185418523741597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3175280384790279015827731 4762920577185418523741597)
                    ·
                      refine ⟨1786095216444531946403099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4762920577185418523741597 1786095216444531946403099)
                      ·
                        rfl

theorem cell23_3478408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_3478408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478408 prefixEnd_3478408 := by exact prefixLift 3478408
  have htrace : WordTrace (prefixWord ++ tailWord_3478408) baseStart_3478408 baseEnd_3478408 := by
    simpa [prefixWord, tailWord_3478408, baseEnd_3478408] using wordTrace_append hprefix tailTrace_3478408
  have hstable : (prefixWord ++ tailWord_3478408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478408).length < 2 ^ (prefixWord ++ tailWord_3478408).sum := by decide
  have hdescent : baseEnd_3478408 < baseStart_3478408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478452 : List Nat := [2, 5, 2, 1, 1, 2, 1, 3, 1, 3, 2]
def baseStart_3478452 : Nat := 118140960795 + 3478452 * 2 ^ 59
def prefixEnd_3478452 : Nat := 4983230072969 + 3 ^ 40 * 3478452 * 2
def baseEnd_3478452 : Nat := 1786117809593329774252897

theorem tailTrace_3478452 : CollatzResearch.WordTrace tailWord_3478452 prefixEnd_3478452 1786117809593329774252897 := by
  unfold tailWord_3478452
  simp only [CollatzResearch.WordTrace]
  refine ⟨63434783597084975575098805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84579711462779967433465073 63434783597084975575098805)
  ·
    refine ⟨5947010962226716460165513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63434783597084975575098805 5947010962226716460165513)
    ·
      refine ⟨4460258221670037345124135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5947010962226716460165513 4460258221670037345124135)
      ·
        refine ⟨6690387332505056017686203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4460258221670037345124135 6690387332505056017686203)
        ·
          refine ⟨10035580998757584026529305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6690387332505056017686203 10035580998757584026529305)
          ·
            refine ⟨7526685749068188019896979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10035580998757584026529305 7526685749068188019896979)
            ·
              refine ⟨11290028623602282029845469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7526685749068188019896979 11290028623602282029845469)
              ·
                refine ⟨4233760733850855761192051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11290028623602282029845469 4233760733850855761192051)
                ·
                  refine ⟨6350641100776283641788077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4233760733850855761192051 6350641100776283641788077)
                  ·
                    refine ⟨2381490412791106365670529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6350641100776283641788077 2381490412791106365670529)
                    ·
                      refine ⟨1786117809593329774252897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2381490412791106365670529 1786117809593329774252897)
                      ·
                        rfl

theorem cell23_3478452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_3478452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478452 prefixEnd_3478452 := by exact prefixLift 3478452
  have htrace : WordTrace (prefixWord ++ tailWord_3478452) baseStart_3478452 baseEnd_3478452 := by
    simpa [prefixWord, tailWord_3478452, baseEnd_3478452] using wordTrace_append hprefix tailTrace_3478452
  have hstable : (prefixWord ++ tailWord_3478452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478452).length < 2 ^ (prefixWord ++ tailWord_3478452).sum := by decide
  have hdescent : baseEnd_3478452 < baseStart_3478452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478471 : List Nat := [1, 1, 4, 1, 1, 2, 4, 4, 5]
def baseStart_3478471 : Nat := 118140960795 + 3478471 * 2 ^ 59
def prefixEnd_3478471 : Nat := 4983230072969 + 3 ^ 40 * 3478471 * 2
def baseEnd_3478471 : Nat := 198458618413973911101701

theorem tailTrace_3478471 : CollatzResearch.WordTrace tailWord_3478471 prefixEnd_3478471 198458618413973911101701 := by
  unfold tailWord_3478471
  simp only [CollatzResearch.WordTrace]
  refine ⟨126870260181101117395139267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84580173454067411596759511 126870260181101117395139267)
  ·
    refine ⟨190305390271651676092708901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126870260181101117395139267 190305390271651676092708901)
    ·
      refine ⟨35682260675934689267382919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190305390271651676092708901 35682260675934689267382919)
      ·
        refine ⟨53523391013902033901074379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35682260675934689267382919 53523391013902033901074379)
        ·
          refine ⟨80285086520853050851611569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53523391013902033901074379 80285086520853050851611569)
          ·
            refine ⟨60213814890639788138708677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80285086520853050851611569 60213814890639788138708677)
            ·
              refine ⟨11290090291994960276007877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60213814890639788138708677 11290090291994960276007877)
              ·
                refine ⟨2116891929749055051751477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11290090291994960276007877 2116891929749055051751477)
                ·
                  refine ⟨198458618413973911101701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2116891929749055051751477 198458618413973911101701)
                  ·
                    rfl

theorem cell23_3478471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 4, 5].length) (baseStart_3478471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478471 prefixEnd_3478471 := by exact prefixLift 3478471
  have htrace : WordTrace (prefixWord ++ tailWord_3478471) baseStart_3478471 baseEnd_3478471 := by
    simpa [prefixWord, tailWord_3478471, baseEnd_3478471] using wordTrace_append hprefix tailTrace_3478471
  have hstable : (prefixWord ++ tailWord_3478471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478471).length < 2 ^ (prefixWord ++ tailWord_3478471).sum := by decide
  have hdescent : baseEnd_3478471 < baseStart_3478471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478518 : List Nat := [5, 1, 1, 1, 3, 2, 1, 2, 2, 5]
def baseStart_3478518 : Nat := 118140960795 + 3478518 * 2 ^ 59
def prefixEnd_3478518 : Nat := 4983230072969 + 3 ^ 40 * 3478518 * 2
def baseEnd_3478518 : Nat := 595383899772175505342531

theorem tailTrace_3478518 : CollatzResearch.WordTrace tailWord_3478518 prefixEnd_3478518 595383899772175505342531 := by
  unfold tailWord_3478518
  simp only [CollatzResearch.WordTrace]
  refine ⟨7929498400745677776381263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84581316274620562948066805 7929498400745677776381263)
  ·
    refine ⟨11894247601118516664571895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7929498400745677776381263 11894247601118516664571895)
    ·
      refine ⟨17841371401677774996857843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11894247601118516664571895 17841371401677774996857843)
      ·
        refine ⟨26762057102516662495286765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17841371401677774996857843 26762057102516662495286765)
        ·
          refine ⟨10035771413443748435732537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26762057102516662495286765 10035771413443748435732537)
          ·
            refine ⟨7526828560082811326799403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10035771413443748435732537 7526828560082811326799403)
            ·
              refine ⟨11290242840124216990199105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7526828560082811326799403 11290242840124216990199105)
              ·
                refine ⟨8467682130093162742649329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11290242840124216990199105 8467682130093162742649329)
                ·
                  refine ⟨6350761597569872056986997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8467682130093162742649329 6350761597569872056986997)
                  ·
                    refine ⟨595383899772175505342531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6350761597569872056986997 595383899772175505342531)
                    ·
                      rfl

theorem cell23_3478518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_3478518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478518 prefixEnd_3478518 := by exact prefixLift 3478518
  have htrace : WordTrace (prefixWord ++ tailWord_3478518) baseStart_3478518 baseEnd_3478518 := by
    simpa [prefixWord, tailWord_3478518, baseEnd_3478518] using wordTrace_append hprefix tailTrace_3478518
  have hstable : (prefixWord ++ tailWord_3478518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478518).length < 2 ^ (prefixWord ++ tailWord_3478518).sum := by decide
  have hdescent : baseEnd_3478518 < baseStart_3478518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478521 : List Nat := [1, 2, 1, 3, 1, 3, 3, 2, 2, 1, 4]
def baseStart_3478521 : Nat := 118140960795 + 3478521 * 2 ^ 59
def prefixEnd_3478521 : Nat := 4983230072969 + 3 ^ 40 * 3478521 * 2
def baseEnd_3478521 : Nat := 1786153239758490004290079

theorem tailTrace_3478521 : CollatzResearch.WordTrace tailWord_3478521 prefixEnd_3478521 1786153239758490004290079 := by
  unfold tailWord_3478521
  simp only [CollatzResearch.WordTrace]
  refine ⟨126872083830919975934459417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84581389220613317289639611 126872083830919975934459417)
  ·
    refine ⟨95154062873189981950844563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126872083830919975934459417 95154062873189981950844563)
    ·
      refine ⟨142731094309784972926266845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95154062873189981950844563 142731094309784972926266845)
      ·
        refine ⟨53524160366169364847350067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142731094309784972926266845 53524160366169364847350067)
        ·
          refine ⟨80286240549254047271025101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53524160366169364847350067 80286240549254047271025101)
          ·
            refine ⟨30107340205970267726634413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80286240549254047271025101 30107340205970267726634413)
            ·
              refine ⟨11290252577238850397487905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30107340205970267726634413 11290252577238850397487905)
              ·
                refine ⟨8467689432929137798115929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11290252577238850397487905 8467689432929137798115929)
                ·
                  refine ⟨6350767074696853348586947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8467689432929137798115929 6350767074696853348586947)
                  ·
                    refine ⟨9526150612045280022880421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6350767074696853348586947 9526150612045280022880421)
                    ·
                      refine ⟨1786153239758490004290079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9526150612045280022880421 1786153239758490004290079)
                      ·
                        rfl

theorem cell23_3478521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_3478521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478521 prefixEnd_3478521 := by exact prefixLift 3478521
  have htrace : WordTrace (prefixWord ++ tailWord_3478521) baseStart_3478521 baseEnd_3478521 := by
    simpa [prefixWord, tailWord_3478521, baseEnd_3478521] using wordTrace_append hprefix tailTrace_3478521
  have hstable : (prefixWord ++ tailWord_3478521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478521).length < 2 ^ (prefixWord ++ tailWord_3478521).sum := by decide
  have hdescent : baseEnd_3478521 < baseStart_3478521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478582 : List Nat := [5, 1, 2, 1, 1, 3, 1, 4, 1, 4]
def baseStart_3478582 : Nat := 118140960795 + 3478582 * 2 ^ 59
def prefixEnd_3478582 : Nat := 4983230072969 + 3 ^ 40 * 3478582 * 2
def baseEnd_3478582 : Nat := 595394854026138088542433

theorem tailTrace_3478582 : CollatzResearch.WordTrace tailWord_3478582 prefixEnd_3478582 595394854026138088542433 := by
  unfold tailWord_3478582
  simp only [CollatzResearch.WordTrace]
  refine ⟨7929644292731186459526875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84582872455799322234953333 7929644292731186459526875)
  ·
    refine ⟨11894466439096779689290313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7929644292731186459526875 11894466439096779689290313)
    ·
      refine ⟨8920849829322584766967735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11894466439096779689290313 8920849829322584766967735)
      ·
        refine ⟨13381274743983877150451603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8920849829322584766967735 13381274743983877150451603)
        ·
          refine ⟨20071912115975815725677405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13381274743983877150451603 20071912115975815725677405)
          ·
            refine ⟨7526967043490930897129027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20071912115975815725677405 7526967043490930897129027)
            ·
              refine ⟨11290450565236396345693541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7526967043490930897129027 11290450565236396345693541)
              ·
                refine ⟨2116959480981824314817539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11290450565236396345693541 2116959480981824314817539)
                ·
                  refine ⟨3175439221472736472226309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2116959480981824314817539 3175439221472736472226309)
                  ·
                    refine ⟨595394854026138088542433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3175439221472736472226309 595394854026138088542433)
                    ·
                      rfl

theorem cell23_3478582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_3478582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478582 prefixEnd_3478582 := by exact prefixLift 3478582
  have htrace : WordTrace (prefixWord ++ tailWord_3478582) baseStart_3478582 baseEnd_3478582 := by
    simpa [prefixWord, tailWord_3478582, baseEnd_3478582] using wordTrace_append hprefix tailTrace_3478582
  have hstable : (prefixWord ++ tailWord_3478582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478582).length < 2 ^ (prefixWord ++ tailWord_3478582).sum := by decide
  have hdescent : baseEnd_3478582 < baseStart_3478582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478605 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 5, 1, 3]
def baseStart_3478605 : Nat := 118140960795 + 3478605 * 2 ^ 59
def prefixEnd_3478605 : Nat := 4983230072969 + 3 ^ 40 * 3478605 * 2
def baseEnd_3478605 : Nat := 1786196372133467675639693

theorem tailTrace_3478605 : CollatzResearch.WordTrace tailWord_3478605 prefixEnd_3478605 1786196372133467675639693 := by
  unfold tailWord_3478605
  simp only [CollatzResearch.WordTrace]
  refine ⟨126875147562615658280517269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84583431708410438853678179 126875147562615658280517269)
  ·
    refine ⟨5947272541997608981899247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 126875147562615658280517269 5947272541997608981899247)
    ·
      refine ⟨8920908812996413472848871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5947272541997608981899247 8920908812996413472848871)
      ·
        refine ⟨13381363219494620209273307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8920908812996413472848871 13381363219494620209273307)
        ·
          refine ⟨20072044829241930313909961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13381363219494620209273307 20072044829241930313909961)
          ·
            refine ⟨15054033621931447735432471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20072044829241930313909961 15054033621931447735432471)
            ·
              refine ⟨22581050432897171603148707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15054033621931447735432471 22581050432897171603148707)
              ·
                refine ⟨33871575649345757404723061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22581050432897171603148707 33871575649345757404723061)
                ·
                  refine ⟨3175460217126164756692787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33871575649345757404723061 3175460217126164756692787)
                  ·
                    refine ⟨4763190325689247135039181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3175460217126164756692787 4763190325689247135039181)
                    ·
                      refine ⟨1786196372133467675639693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4763190325689247135039181 1786196372133467675639693)
                      ·
                        rfl

theorem cell23_3478605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_3478605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478605 prefixEnd_3478605 := by exact prefixLift 3478605
  have htrace : WordTrace (prefixWord ++ tailWord_3478605) baseStart_3478605 baseEnd_3478605 := by
    simpa [prefixWord, tailWord_3478605, baseEnd_3478605] using wordTrace_append hprefix tailTrace_3478605
  have hstable : (prefixWord ++ tailWord_3478605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478605).length < 2 ^ (prefixWord ++ tailWord_3478605).sum := by decide
  have hdescent : baseEnd_3478605 < baseStart_3478605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478665 : List Nat := [1, 2, 1, 1, 4, 4, 2, 2, 1, 2, 3]
def baseStart_3478665 : Nat := 118140960795 + 3478665 * 2 ^ 59
def prefixEnd_3478665 : Nat := 4983230072969 + 3 ^ 40 * 3478665 * 2
def baseEnd_3478665 : Nat := 1786227180972737440889417

theorem tailTrace_3478665 : CollatzResearch.WordTrace tailWord_3478665 prefixEnd_3478665 1786227180972737440889417 := by
  unfold tailWord_3478665
  simp only [CollatzResearch.WordTrace]
  refine ⟨126877335942398288527701449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84584890628265525685134299 126877335942398288527701449)
  ·
    refine ⟨95158001956798716395776087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126877335942398288527701449 95158001956798716395776087)
    ·
      refine ⟨142737002935198074593664131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95158001956798716395776087 142737002935198074593664131)
      ·
        refine ⟨214105504402797111890496197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142737002935198074593664131 214105504402797111890496197)
        ·
          refine ⟨40144782075524458479468037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214105504402797111890496197 40144782075524458479468037)
          ·
            refine ⟨7527146639160835964900257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40144782075524458479468037 7527146639160835964900257)
            ·
              refine ⟨5645359979370626973675193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7527146639160835964900257 5645359979370626973675193)
              ·
                refine ⟨4234019984527970230256395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5645359979370626973675193 4234019984527970230256395)
                ·
                  refine ⟨6351029976791955345384593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4234019984527970230256395 6351029976791955345384593)
                  ·
                    refine ⟨4763272482593966509038445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6351029976791955345384593 4763272482593966509038445)
                    ·
                      refine ⟨1786227180972737440889417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4763272482593966509038445 1786227180972737440889417)
                      ·
                        rfl

theorem cell23_3478665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 2, 3].length) (baseStart_3478665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478665 prefixEnd_3478665 := by exact prefixLift 3478665
  have htrace : WordTrace (prefixWord ++ tailWord_3478665) baseStart_3478665 baseEnd_3478665 := by
    simpa [prefixWord, tailWord_3478665, baseEnd_3478665] using wordTrace_append hprefix tailTrace_3478665
  have hstable : (prefixWord ++ tailWord_3478665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478665).length < 2 ^ (prefixWord ++ tailWord_3478665).sum := by decide
  have hdescent : baseEnd_3478665 < baseStart_3478665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478679 : List Nat := [1, 1, 3, 3, 3, 1, 3, 3, 1, 2, 2]
def baseStart_3478679 : Nat := 118140960795 + 3478679 * 2 ^ 59
def prefixEnd_3478679 : Nat := 4983230072969 + 3 ^ 40 * 3478679 * 2
def baseEnd_3478679 : Nat := 1786234369701900386114353

theorem tailTrace_3478679 : CollatzResearch.WordTrace tailWord_3478679 prefixEnd_3478679 1786234369701900386114353 := by
  unfold tailWord_3478679
  simp only [CollatzResearch.WordTrace]
  refine ⟨126877846564347568918711091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84585231042898379279140727 126877846564347568918711091)
  ·
    refine ⟨190316769846521353378066637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126877846564347568918711091 190316769846521353378066637)
    ·
      refine ⟨71368788692445507516774989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190316769846521353378066637 71368788692445507516774989)
      ·
        refine ⟨26763295759667065318790621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71368788692445507516774989 26763295759667065318790621)
        ·
          refine ⟨10036235909875149494546483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26763295759667065318790621 10036235909875149494546483)
          ·
            refine ⟨15054353864812724241819725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10036235909875149494546483 15054353864812724241819725)
            ·
              refine ⟨5645382699304771590682397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15054353864812724241819725 5645382699304771590682397)
              ·
                refine ⟨2117018512239289346505899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5645382699304771590682397 2117018512239289346505899)
                ·
                  refine ⟨3175527768358934019758849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2117018512239289346505899 3175527768358934019758849)
                  ·
                    refine ⟨2381645826269200514819137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3175527768358934019758849 2381645826269200514819137)
                    ·
                      refine ⟨1786234369701900386114353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2381645826269200514819137 1786234369701900386114353)
                      ·
                        rfl

theorem cell23_3478679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_3478679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478679 prefixEnd_3478679 := by exact prefixLift 3478679
  have htrace : WordTrace (prefixWord ++ tailWord_3478679) baseStart_3478679 baseEnd_3478679 := by
    simpa [prefixWord, tailWord_3478679, baseEnd_3478679] using wordTrace_append hprefix tailTrace_3478679
  have hstable : (prefixWord ++ tailWord_3478679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478679).length < 2 ^ (prefixWord ++ tailWord_3478679).sum := by decide
  have hdescent : baseEnd_3478679 < baseStart_3478679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478711 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 1, 8]
def baseStart_3478711 : Nat := 118140960795 + 3478711 * 2 ^ 59
def prefixEnd_3478711 : Nat := 4983230072969 + 3 ^ 40 * 3478711 * 2
def baseEnd_3478711 : Nat := 595416933694281420304735

theorem tailTrace_3478711 : CollatzResearch.WordTrace tailWord_3478711 prefixEnd_3478711 595416933694281420304735 := by
  unfold tailWord_3478711
  simp only [CollatzResearch.WordTrace]
  refine ⟨126879013700231638383875987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84586009133487758922583991 126879013700231638383875987)
  ·
    refine ⟨190318520550347457575813981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126879013700231638383875987 190318520550347457575813981)
    ·
      refine ⟨71369445206380296590930243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190318520550347457575813981 71369445206380296590930243)
      ·
        refine ⟨107054167809570444886395365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71369445206380296590930243 107054167809570444886395365)
        ·
          refine ⟨20072656464294458416199131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107054167809570444886395365 20072656464294458416199131)
          ·
            refine ⟨30108984696441687624298697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20072656464294458416199131 30108984696441687624298697)
            ·
              refine ⟨22581738522331265718224023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30108984696441687624298697 22581738522331265718224023)
              ·
                refine ⟨33872607783496898577336035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22581738522331265718224023 33872607783496898577336035)
                ·
                  refine ⟨50808911675245347866004053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33872607783496898577336035 50808911675245347866004053)
                  ·
                    refine ⟨595416933694281420304735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50808911675245347866004053 595416933694281420304735)
                    ·
                      rfl

theorem cell23_3478711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 8].length) (baseStart_3478711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478711 prefixEnd_3478711 := by exact prefixLift 3478711
  have htrace : WordTrace (prefixWord ++ tailWord_3478711) baseStart_3478711 baseEnd_3478711 := by
    simpa [prefixWord, tailWord_3478711, baseEnd_3478711] using wordTrace_append hprefix tailTrace_3478711
  have hstable : (prefixWord ++ tailWord_3478711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478711).length < 2 ^ (prefixWord ++ tailWord_3478711).sum := by decide
  have hdescent : baseEnd_3478711 < baseStart_3478711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478731 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 4]
def baseStart_3478731 : Nat := 118140960795 + 3478731 * 2 ^ 59
def prefixEnd_3478731 : Nat := 4983230072969 + 3 ^ 40 * 3478731 * 2
def baseEnd_3478731 : Nat := 1786261070695934182664113

theorem tailTrace_3478731 : CollatzResearch.WordTrace tailWord_3478731 prefixEnd_3478731 1786261070695934182664113 := by
  unfold tailWord_3478731
  simp only [CollatzResearch.WordTrace]
  refine ⟨126879743160159181799604047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84586495440106121199736031 126879743160159181799604047)
  ·
    refine ⟨190319614740238772699406071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126879743160159181799604047 190319614740238772699406071)
    ·
      refine ⟨285479422110358159049109107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190319614740238772699406071 285479422110358159049109107)
      ·
        refine ⟨428219133165537238573663661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285479422110358159049109107 428219133165537238573663661)
        ·
          refine ⟨160582174937076464465123873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 428219133165537238573663661 160582174937076464465123873)
          ·
            refine ⟨120436631202807348348842905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160582174937076464465123873 120436631202807348348842905)
            ·
              refine ⟨90327473402105511261632179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120436631202807348348842905 90327473402105511261632179)
              ·
                refine ⟨135491210103158266892448269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90327473402105511261632179 135491210103158266892448269)
                ·
                  refine ⟨50809203788684350084668101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135491210103158266892448269 50809203788684350084668101)
                  ·
                    refine ⟨9526725710378315640875269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50809203788684350084668101 9526725710378315640875269)
                    ·
                      refine ⟨1786261070695934182664113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9526725710378315640875269 1786261070695934182664113)
                      ·
                        rfl

theorem cell23_3478731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 4].length) (baseStart_3478731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478731 prefixEnd_3478731 := by exact prefixLift 3478731
  have htrace : WordTrace (prefixWord ++ tailWord_3478731) baseStart_3478731 baseEnd_3478731 := by
    simpa [prefixWord, tailWord_3478731, baseEnd_3478731] using wordTrace_append hprefix tailTrace_3478731
  have hstable : (prefixWord ++ tailWord_3478731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478731).length < 2 ^ (prefixWord ++ tailWord_3478731).sum := by decide
  have hdescent : baseEnd_3478731 < baseStart_3478731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478735 : List Nat := [1, 1, 2, 1, 1, 3, 2, 4, 4, 2, 2]
def baseStart_3478735 : Nat := 118140960795 + 3478735 * 2 ^ 59
def prefixEnd_3478735 : Nat := 4983230072969 + 3 ^ 40 * 3478735 * 2
def baseEnd_3478735 : Nat := 1786263124618552167014095

theorem tailTrace_3478735 : CollatzResearch.WordTrace tailWord_3478735 prefixEnd_3478735 1786263124618552167014095 := by
  unfold tailWord_3478735
  simp only [CollatzResearch.WordTrace]
  refine ⟨126879889052144690482749659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84586592701429793655166439 126879889052144690482749659)
  ·
    refine ⟨190319833578217035724124489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126879889052144690482749659 190319833578217035724124489)
    ·
      refine ⟨142739875183662776793093367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190319833578217035724124489 142739875183662776793093367)
      ·
        refine ⟨214109812775494165189640051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142739875183662776793093367 214109812775494165189640051)
        ·
          refine ⟨321164719163241247784460077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214109812775494165189640051 321164719163241247784460077)
          ·
            refine ⟨120436769686215467919172529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 321164719163241247784460077 120436769686215467919172529)
            ·
              refine ⟨90327577264661600939379397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120436769686215467919172529 90327577264661600939379397)
              ·
                refine ⟨16936420737124050176133637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90327577264661600939379397 16936420737124050176133637)
                ·
                  refine ⟨3175578888210759408025057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16936420737124050176133637 3175578888210759408025057)
                  ·
                    refine ⟨2381684166158069556018793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3175578888210759408025057 2381684166158069556018793)
                    ·
                      refine ⟨1786263124618552167014095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2381684166158069556018793 1786263124618552167014095)
                      ·
                        rfl

theorem cell23_3478735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 4, 2, 2].length) (baseStart_3478735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478735 prefixEnd_3478735 := by exact prefixLift 3478735
  have htrace : WordTrace (prefixWord ++ tailWord_3478735) baseStart_3478735 baseEnd_3478735 := by
    simpa [prefixWord, tailWord_3478735, baseEnd_3478735] using wordTrace_append hprefix tailTrace_3478735
  have hstable : (prefixWord ++ tailWord_3478735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478735).length < 2 ^ (prefixWord ++ tailWord_3478735).sum := by decide
  have hdescent : baseEnd_3478735 < baseStart_3478735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478738 : List Nat := [3, 2, 2, 2, 1, 1, 1, 3, 2, 1, 5]
def baseStart_3478738 : Nat := 118140960795 + 3478738 * 2 ^ 59
def prefixEnd_3478738 : Nat := 4983230072969 + 3 ^ 40 * 3478738 * 2
def baseEnd_3478738 : Nat := 1786264665060515655276581

theorem tailTrace_3478738 : CollatzResearch.WordTrace tailWord_3478738 prefixEnd_3478738 1786264665060515655276581 := by
  unfold tailWord_3478738
  simp only [CollatzResearch.WordTrace]
  refine ⟨31719999617783455498777217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84586665647422547996739245 31719999617783455498777217)
  ·
    refine ⟨23789999713337591624082913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31719999617783455498777217 23789999713337591624082913)
    ·
      refine ⟨17842499785003193718062185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23789999713337591624082913 17842499785003193718062185)
      ·
        refine ⟨13381874838752395288546639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17842499785003193718062185 13381874838752395288546639)
        ·
          refine ⟨20072812258128592932819959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13381874838752395288546639 20072812258128592932819959)
          ·
            refine ⟨30109218387192889399229939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20072812258128592932819959 30109218387192889399229939)
            ·
              refine ⟨45163827580789334098844909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30109218387192889399229939 45163827580789334098844909)
              ·
                refine ⟨16936435342796000287066841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45163827580789334098844909 16936435342796000287066841)
                ·
                  refine ⟨12702326507097000215300131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16936435342796000287066841 12702326507097000215300131)
                  ·
                    refine ⟨19053489760645500322950197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12702326507097000215300131 19053489760645500322950197)
                    ·
                      refine ⟨1786264665060515655276581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19053489760645500322950197 1786264665060515655276581)
                      ·
                        rfl

theorem cell23_3478738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_3478738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478738 prefixEnd_3478738 := by exact prefixLift 3478738
  have htrace : WordTrace (prefixWord ++ tailWord_3478738) baseStart_3478738 baseEnd_3478738 := by
    simpa [prefixWord, tailWord_3478738, baseEnd_3478738] using wordTrace_append hprefix tailTrace_3478738
  have hstable : (prefixWord ++ tailWord_3478738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478738).length < 2 ^ (prefixWord ++ tailWord_3478738).sum := by decide
  have hdescent : baseEnd_3478738 < baseStart_3478738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478751 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 7]
def baseStart_3478751 : Nat := 118140960795 + 3478751 * 2 ^ 59
def prefixEnd_3478751 : Nat := 4983230072969 + 3 ^ 40 * 3478751 * 2
def baseEnd_3478751 : Nat := 1786271340309024104414021

theorem tailTrace_3478751 : CollatzResearch.WordTrace tailWord_3478751 prefixEnd_3478751 1786271340309024104414021 := by
  unfold tailWord_3478751
  simp only [CollatzResearch.WordTrace]
  refine ⟨126880472620086725215332107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84586981746724483476888071 126880472620086725215332107)
  ·
    refine ⟨190320708930130087822998161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126880472620086725215332107 190320708930130087822998161)
    ·
      refine ⟨142740531697597565867248621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190320708930130087822998161 142740531697597565867248621)
      ·
        refine ⟨53527699386599087200218233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142740531697597565867248621 53527699386599087200218233)
        ·
          refine ⟨40145774539949315400163675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53527699386599087200218233 40145774539949315400163675)
          ·
            refine ⟨60218661809923973100245513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40145774539949315400163675 60218661809923973100245513)
            ·
              refine ⟨45163996357442979825184135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60218661809923973100245513 45163996357442979825184135)
              ·
                refine ⟨67745994536164469737776203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45163996357442979825184135 67745994536164469737776203)
                ·
                  refine ⟨101618991804246704606664305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67745994536164469737776203 101618991804246704606664305)
                  ·
                    refine ⟨76214243853185028454998229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101618991804246704606664305 76214243853185028454998229)
                    ·
                      refine ⟨1786271340309024104414021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 76214243853185028454998229 1786271340309024104414021)
                      ·
                        rfl

theorem cell23_3478751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_3478751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478751 prefixEnd_3478751 := by exact prefixLift 3478751
  have htrace : WordTrace (prefixWord ++ tailWord_3478751) baseStart_3478751 baseEnd_3478751 := by
    simpa [prefixWord, tailWord_3478751, baseEnd_3478751] using wordTrace_append hprefix tailTrace_3478751
  have hstable : (prefixWord ++ tailWord_3478751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478751).length < 2 ^ (prefixWord ++ tailWord_3478751).sum := by decide
  have hdescent : baseEnd_3478751 < baseStart_3478751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478752 : List Nat := [2, 1, 1, 3, 1, 4, 1, 4, 2, 2, 2]
def baseStart_3478752 : Nat := 118140960795 + 3478752 * 2 ^ 59
def prefixEnd_3478752 : Nat := 4983230072969 + 3 ^ 40 * 3478752 * 2
def baseEnd_3478752 : Nat := 1786271853789678600501517

theorem tailTrace_3478752 : CollatzResearch.WordTrace tailWord_3478752 prefixEnd_3478752 1786271853789678600501517 := by
  unfold tailWord_3478752
  simp only [CollatzResearch.WordTrace]
  refine ⟨63440254546541551193059255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84587006062055401590745673 63440254546541551193059255)
  ·
    refine ⟨95160381819812326789588883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63440254546541551193059255 95160381819812326789588883)
    ·
      refine ⟨142740572729718490184383325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95160381819812326789588883 142740572729718490184383325)
      ·
        refine ⟨53527714773644433819143747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142740572729718490184383325 53527714773644433819143747)
        ·
          refine ⟨80291572160466650728715621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53527714773644433819143747 80291572160466650728715621)
          ·
            refine ⟨15054669780087497011634179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80291572160466650728715621 15054669780087497011634179)
            ·
              refine ⟨22582004670131245517451269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15054669780087497011634179 22582004670131245517451269)
              ·
                refine ⟨4234125875649608534522113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22582004670131245517451269 4234125875649608534522113)
                ·
                  refine ⟨3175594406737206400891585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4234125875649608534522113 3175594406737206400891585)
                  ·
                    refine ⟨2381695805052904800668689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3175594406737206400891585 2381695805052904800668689)
                    ·
                      refine ⟨1786271853789678600501517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2381695805052904800668689 1786271853789678600501517)
                      ·
                        rfl

theorem cell23_3478752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 2, 2, 2].length) (baseStart_3478752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478752 prefixEnd_3478752 := by exact prefixLift 3478752
  have htrace : WordTrace (prefixWord ++ tailWord_3478752) baseStart_3478752 baseEnd_3478752 := by
    simpa [prefixWord, tailWord_3478752, baseEnd_3478752] using wordTrace_append hprefix tailTrace_3478752
  have hstable : (prefixWord ++ tailWord_3478752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478752).length < 2 ^ (prefixWord ++ tailWord_3478752).sum := by decide
  have hdescent : baseEnd_3478752 < baseStart_3478752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478765 : List Nat := [1, 5, 1, 2, 2, 2, 1, 1, 2, 2, 4]
def baseStart_3478765 : Nat := 118140960795 + 3478765 * 2 ^ 59
def prefixEnd_3478765 : Nat := 4983230072969 + 3 ^ 40 * 3478765 * 2
def baseEnd_3478765 : Nat := 1786278529038187049638957

theorem tailTrace_3478765 : CollatzResearch.WordTrace tailWord_3478765 prefixEnd_3478765 1786278529038187049638957 := by
  unfold tailWord_3478765
  simp only [CollatzResearch.WordTrace]
  refine ⟨126880983242036005606341749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84587322161357337070894499 126880983242036005606341749)
  ·
    refine ⟨11895092178940875525594539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126880983242036005606341749 11895092178940875525594539)
    ·
      refine ⟨17842638268411313288391809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11895092178940875525594539 17842638268411313288391809)
      ·
        refine ⟨13381978701308484966293857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17842638268411313288391809 13381978701308484966293857)
        ·
          refine ⟨10036484025981363724720393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13381978701308484966293857 10036484025981363724720393)
          ·
            refine ⟨7527363019486022793540295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10036484025981363724720393 7527363019486022793540295)
            ·
              refine ⟨11291044529229034190310443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7527363019486022793540295 11291044529229034190310443)
              ·
                refine ⟨16936566793843551285465665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11291044529229034190310443 16936566793843551285465665)
                ·
                  refine ⟨12702425095382663464099249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16936566793843551285465665 12702425095382663464099249)
                  ·
                    refine ⟨9526818821536997598074437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12702425095382663464099249 9526818821536997598074437)
                    ·
                      refine ⟨1786278529038187049638957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9526818821536997598074437 1786278529038187049638957)
                      ·
                        rfl

theorem cell23_3478765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_3478765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478765 prefixEnd_3478765 := by exact prefixLift 3478765
  have htrace : WordTrace (prefixWord ++ tailWord_3478765) baseStart_3478765 baseEnd_3478765 := by
    simpa [prefixWord, tailWord_3478765, baseEnd_3478765] using wordTrace_append hprefix tailTrace_3478765
  have hstable : (prefixWord ++ tailWord_3478765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478765).length < 2 ^ (prefixWord ++ tailWord_3478765).sum := by decide
  have hdescent : baseEnd_3478765 < baseStart_3478765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478792 : List Nat := [2, 1, 3, 2, 4, 1, 2, 3, 5]
def baseStart_3478792 : Nat := 118140960795 + 3478792 * 2 ^ 59
def prefixEnd_3478792 : Nat := 4983230072969 + 3 ^ 40 * 3478792 * 2
def baseEnd_3478792 : Nat := 198476932557317604889037

theorem tailTrace_3478792 : CollatzResearch.WordTrace tailWord_3478792 prefixEnd_3478792 198476932557317604889037 := by
  unfold tailWord_3478792
  simp only [CollatzResearch.WordTrace]
  refine ⟨63440984006469094608787315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84587978675292126145049753 63440984006469094608787315)
  ·
    refine ⟨95161476009703641913180973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63440984006469094608787315 95161476009703641913180973)
    ·
      refine ⟨35685553503638865717442865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95161476009703641913180973 35685553503638865717442865)
      ·
        refine ⟨26764165127729149288082149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35685553503638865717442865 26764165127729149288082149)
        ·
          refine ⟨5018280961449215491515403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26764165127729149288082149 5018280961449215491515403)
          ·
            refine ⟨7527421442173823237273105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5018280961449215491515403 7527421442173823237273105)
            ·
              refine ⟨5645566081630367427954829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7527421442173823237273105 5645566081630367427954829)
              ·
                refine ⟨2117087280611387785483061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5645566081630367427954829 2117087280611387785483061)
                ·
                  refine ⟨198476932557317604889037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2117087280611387785483061 198476932557317604889037)
                  ·
                    rfl

theorem cell23_3478792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 3, 5].length) (baseStart_3478792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478792 prefixEnd_3478792 := by exact prefixLift 3478792
  have htrace : WordTrace (prefixWord ++ tailWord_3478792) baseStart_3478792 baseEnd_3478792 := by
    simpa [prefixWord, tailWord_3478792, baseEnd_3478792] using wordTrace_append hprefix tailTrace_3478792
  have hstable : (prefixWord ++ tailWord_3478792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478792).length < 2 ^ (prefixWord ++ tailWord_3478792).sum := by decide
  have hdescent : baseEnd_3478792 < baseStart_3478792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478835 : List Nat := [1, 1, 1, 2, 5, 2, 2, 2, 3, 4]
def baseStart_3478835 : Nat := 118140960795 + 3478835 * 2 ^ 59
def prefixEnd_3478835 : Nat := 4983230072969 + 3 ^ 40 * 3478835 * 2
def baseEnd_3478835 : Nat := 595438157561333925254545

theorem tailTrace_3478835 : CollatzResearch.WordTrace tailWord_3478835 prefixEnd_3478835 595438157561333925254545 := by
  unfold tailWord_3478835
  simp only [CollatzResearch.WordTrace]
  refine ⟨126883536351782407561389959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84589024234521605040926639 126883536351782407561389959)
  ·
    refine ⟨190325304527673611342084939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126883536351782407561389959 190325304527673611342084939)
    ·
      refine ⟨285487956791510417013127409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190325304527673611342084939 285487956791510417013127409)
      ·
        refine ⟨214115967593632812759845557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285487956791510417013127409 214115967593632812759845557)
        ·
          refine ⟨20073371961903076196235521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 214115967593632812759845557 20073371961903076196235521)
          ·
            refine ⟨15055028971427307147176641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20073371961903076196235521 15055028971427307147176641)
            ·
              refine ⟨11291271728570480360382481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15055028971427307147176641 11291271728570480360382481)
              ·
                refine ⟨8468453796427860270286861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11291271728570480360382481 8468453796427860270286861)
                ·
                  refine ⟨3175670173660447601357573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8468453796427860270286861 3175670173660447601357573)
                  ·
                    refine ⟨595438157561333925254545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3175670173660447601357573 595438157561333925254545)
                    ·
                      rfl

theorem cell23_3478835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 3, 4].length) (baseStart_3478835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478835 prefixEnd_3478835 := by exact prefixLift 3478835
  have htrace : WordTrace (prefixWord ++ tailWord_3478835) baseStart_3478835 baseEnd_3478835 := by
    simpa [prefixWord, tailWord_3478835, baseEnd_3478835] using wordTrace_append hprefix tailTrace_3478835
  have hstable : (prefixWord ++ tailWord_3478835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478835).length < 2 ^ (prefixWord ++ tailWord_3478835).sum := by decide
  have hdescent : baseEnd_3478835 < baseStart_3478835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478909 : List Nat := [1, 4, 1, 1, 2, 2, 2, 5, 1, 1, 3]
def baseStart_3478909 : Nat := 118140960795 + 3478909 * 2 ^ 59
def prefixEnd_3478909 : Nat := 4983230072969 + 3 ^ 40 * 3478909 * 2
def baseEnd_3478909 : Nat := 1786352470252434486238295

theorem tailTrace_3478909 : CollatzResearch.WordTrace tailWord_3478909 prefixEnd_3478909 1786352470252434486238295 := by
  unfold tailWord_3478909
  simp only [CollatzResearch.WordTrace]
  refine ⟨126886235353514318199583781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84590823569009545466389187 126886235353514318199583781)
  ·
    refine ⟨23791169128783934662421959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126886235353514318199583781 23791169128783934662421959)
    ·
      refine ⟨35686753693175901993632939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23791169128783934662421959 35686753693175901993632939)
      ·
        refine ⟨53530130539763852990449409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35686753693175901993632939 53530130539763852990449409)
        ·
          refine ⟨40147597904822889742837057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53530130539763852990449409 40147597904822889742837057)
          ·
            refine ⟨30110698428617167307127793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40147597904822889742837057 30110698428617167307127793)
            ·
              refine ⟨22583023821462875480345845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30110698428617167307127793 22583023821462875480345845)
              ·
                refine ⟨2117158483262144576282423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22583023821462875480345845 2117158483262144576282423)
                ·
                  refine ⟨3175737724893216864423635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2117158483262144576282423 3175737724893216864423635)
                  ·
                    refine ⟨4763606587339825296635453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3175737724893216864423635 4763606587339825296635453)
                    ·
                      refine ⟨1786352470252434486238295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4763606587339825296635453 1786352470252434486238295)
                      ·
                        rfl

theorem cell23_3478909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 5, 1, 1, 3].length) (baseStart_3478909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478909 prefixEnd_3478909 := by exact prefixLift 3478909
  have htrace : WordTrace (prefixWord ++ tailWord_3478909) baseStart_3478909 baseEnd_3478909 := by
    simpa [prefixWord, tailWord_3478909, baseEnd_3478909] using wordTrace_append hprefix tailTrace_3478909
  have hstable : (prefixWord ++ tailWord_3478909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478909).length < 2 ^ (prefixWord ++ tailWord_3478909).sum := by decide
  have hdescent : baseEnd_3478909 < baseStart_3478909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478928 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 4]
def baseStart_3478928 : Nat := 118140960795 + 3478928 * 2 ^ 59
def prefixEnd_3478928 : Nat := 4983230072969 + 3 ^ 40 * 3478928 * 2
def baseEnd_3478928 : Nat := 1786362226384869911900707

theorem tailTrace_3478928 : CollatzResearch.WordTrace tailWord_3478928 prefixEnd_3478928 1786362226384869911900707 := by
  unfold tailWord_3478928
  simp only [CollatzResearch.WordTrace]
  refine ⟨63443464170222742222262719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84591285560296989629683625 63443464170222742222262719)
  ·
    refine ⟨95165196255334113333394079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63443464170222742222262719 95165196255334113333394079)
    ·
      refine ⟨142747794383001170000091119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95165196255334113333394079 142747794383001170000091119)
      ·
        refine ⟨214121691574501755000136679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142747794383001170000091119 214121691574501755000136679)
        ·
          refine ⟨321182537361752632500205019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214121691574501755000136679 321182537361752632500205019)
          ·
            refine ⟨481773806042628948750307529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321182537361752632500205019 481773806042628948750307529)
            ·
              refine ⟨361330354531971711562730647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481773806042628948750307529 361330354531971711562730647)
              ·
                refine ⟨541995531797957567344095971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361330354531971711562730647 541995531797957567344095971)
                ·
                  refine ⟨812993297696936351016143957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 541995531797957567344095971 812993297696936351016143957)
                  ·
                    refine ⟨9527265207385972863470437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 812993297696936351016143957 9527265207385972863470437)
                    ·
                      refine ⟨1786362226384869911900707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9527265207385972863470437 1786362226384869911900707)
                      ·
                        rfl

theorem cell23_3478928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 4].length) (baseStart_3478928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478928 prefixEnd_3478928 := by exact prefixLift 3478928
  have htrace : WordTrace (prefixWord ++ tailWord_3478928) baseStart_3478928 baseEnd_3478928 := by
    simpa [prefixWord, tailWord_3478928, baseEnd_3478928] using wordTrace_append hprefix tailTrace_3478928
  have hstable : (prefixWord ++ tailWord_3478928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478928).length < 2 ^ (prefixWord ++ tailWord_3478928).sum := by decide
  have hdescent : baseEnd_3478928 < baseStart_3478928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478932 : List Nat := [2, 4, 2, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_3478932 : Nat := 118140960795 + 3478932 * 2 ^ 59
def prefixEnd_3478932 : Nat := 4983230072969 + 3 ^ 40 * 3478932 * 2
def baseEnd_3478932 : Nat := 1786364280307487896250689

theorem tailTrace_3478932 : CollatzResearch.WordTrace tailWord_3478932 prefixEnd_3478932 1786364280307487896250689 := by
  unfold tailWord_3478932
  simp only [CollatzResearch.WordTrace]
  refine ⟨63443537116215496563835525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84591382821620662085114033 63443537116215496563835525)
  ·
    refine ⟨11895663209290405605719161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63443537116215496563835525 11895663209290405605719161)
    ·
      refine ⟨8921747406967804204289371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11895663209290405605719161 8921747406967804204289371)
      ·
        refine ⟨13382621110451706306434057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8921747406967804204289371 13382621110451706306434057)
        ·
          refine ⟨10036965832838779729825543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13382621110451706306434057 10036965832838779729825543)
          ·
            refine ⟨15055448749258169594738315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10036965832838779729825543 15055448749258169594738315)
            ·
              refine ⟨22583173123887254392107473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15055448749258169594738315 22583173123887254392107473)
              ·
                refine ⟨16937379842915440794080605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22583173123887254392107473 16937379842915440794080605)
                ·
                  refine ⟨6351517441093290297780227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16937379842915440794080605 6351517441093290297780227)
                  ·
                    refine ⟨9527276161639935446670341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6351517441093290297780227 9527276161639935446670341)
                    ·
                      refine ⟨1786364280307487896250689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9527276161639935446670341 1786364280307487896250689)
                      ·
                        rfl

theorem cell23_3478932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_3478932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478932 prefixEnd_3478932 := by exact prefixLift 3478932
  have htrace : WordTrace (prefixWord ++ tailWord_3478932) baseStart_3478932 baseEnd_3478932 := by
    simpa [prefixWord, tailWord_3478932, baseEnd_3478932] using wordTrace_append hprefix tailTrace_3478932
  have hstable : (prefixWord ++ tailWord_3478932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478932).length < 2 ^ (prefixWord ++ tailWord_3478932).sum := by decide
  have hdescent : baseEnd_3478932 < baseStart_3478932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478969 : List Nat := [1, 2, 1, 4, 4, 1, 1, 3, 1, 2, 3]
def baseStart_3478969 : Nat := 118140960795 + 3478969 * 2 ^ 59
def prefixEnd_3478969 : Nat := 4983230072969 + 3 ^ 40 * 3478969 * 2
def baseEnd_3478969 : Nat := 1786383279091704251488019

theorem tailTrace_3478969 : CollatzResearch.WordTrace tailWord_3478969 prefixEnd_3478969 1786383279091704251488019 := by
  unfold tailWord_3478969
  simp only [CollatzResearch.WordTrace]
  refine ⟨126888423733296948446767961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84592282488864632297845307 126888423733296948446767961)
  ·
    refine ⟨95166317799972711335075971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126888423733296948446767961 95166317799972711335075971)
    ·
      refine ⟨142749476699959067002613957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95166317799972711335075971 142749476699959067002613957)
      ·
        refine ⟨26765526881242325062990117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142749476699959067002613957 26765526881242325062990117)
        ·
          refine ⟨5018536290232935949310647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26765526881242325062990117 5018536290232935949310647)
          ·
            refine ⟨7527804435349403923965971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5018536290232935949310647 7527804435349403923965971)
            ·
              refine ⟨11291706653024105885948957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7527804435349403923965971 11291706653024105885948957)
              ·
                refine ⟨4234389994884039707230859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11291706653024105885948957 4234389994884039707230859)
                ·
                  refine ⟨6351584992326059560846289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4234389994884039707230859 6351584992326059560846289)
                  ·
                    refine ⟨4763688744244544670634717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6351584992326059560846289 4763688744244544670634717)
                    ·
                      refine ⟨1786383279091704251488019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4763688744244544670634717 1786383279091704251488019)
                      ·
                        rfl

theorem cell23_3478969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_3478969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478969 prefixEnd_3478969 := by exact prefixLift 3478969
  have htrace : WordTrace (prefixWord ++ tailWord_3478969) baseStart_3478969 baseEnd_3478969 := by
    simpa [prefixWord, tailWord_3478969, baseEnd_3478969] using wordTrace_append hprefix tailTrace_3478969
  have hstable : (prefixWord ++ tailWord_3478969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478969).length < 2 ^ (prefixWord ++ tailWord_3478969).sum := by decide
  have hdescent : baseEnd_3478969 < baseStart_3478969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478996 : List Nat := [2, 4, 1, 2, 4, 1, 1, 1, 1, 2, 4]
def baseStart_3478996 : Nat := 118140960795 + 3478996 * 2 ^ 59
def prefixEnd_3478996 : Nat := 4983230072969 + 3 ^ 40 * 3478996 * 2
def baseEnd_3478996 : Nat := 1786397143069375645850395

theorem tailTrace_3478996 : CollatzResearch.WordTrace tailWord_3478996 prefixEnd_3478996 1786397143069375645850395 := by
  unfold tailWord_3478996
  simp only [CollatzResearch.WordTrace]
  refine ⟨63444704252099566029000421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84592939002799421372000561 63444704252099566029000421)
  ·
    refine ⟨11895882047268668630437579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63444704252099566029000421 11895882047268668630437579)
    ·
      refine ⟨17843823070903002945656369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11895882047268668630437579 17843823070903002945656369)
      ·
        refine ⟨13382867303177252209242277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17843823070903002945656369 13382867303177252209242277)
        ·
          refine ⟨2509287619345734789232927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13382867303177252209242277 2509287619345734789232927)
          ·
            refine ⟨3763931429018602183849391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2509287619345734789232927 3763931429018602183849391)
            ·
              refine ⟨5645897143527903275774087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3763931429018602183849391 5645897143527903275774087)
              ·
                refine ⟨8468845715291854913661131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5645897143527903275774087 8468845715291854913661131)
                ·
                  refine ⟨12703268572937782370491697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8468845715291854913661131 12703268572937782370491697)
                  ·
                    refine ⟨9527451429703336777868773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12703268572937782370491697 9527451429703336777868773)
                    ·
                      refine ⟨1786397143069375645850395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9527451429703336777868773 1786397143069375645850395)
                      ·
                        rfl

theorem cell23_3478996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_3478996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3478996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3478996 prefixEnd_3478996 := by exact prefixLift 3478996
  have htrace : WordTrace (prefixWord ++ tailWord_3478996) baseStart_3478996 baseEnd_3478996 := by
    simpa [prefixWord, tailWord_3478996, baseEnd_3478996] using wordTrace_append hprefix tailTrace_3478996
  have hstable : (prefixWord ++ tailWord_3478996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478996).length < 2 ^ (prefixWord ++ tailWord_3478996).sum := by decide
  have hdescent : baseEnd_3478996 < baseStart_3478996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479009 : List Nat := [1, 2, 3, 1, 2, 3, 1, 4, 1, 3, 2]
def baseStart_3479009 : Nat := 118140960795 + 3479009 * 2 ^ 59
def prefixEnd_3479009 : Nat := 4983230072969 + 3 ^ 40 * 3479009 * 2
def baseEnd_3479009 : Nat := 1786403818317884094987835

theorem tailTrace_3479009 : CollatzResearch.WordTrace tailWord_3479009 prefixEnd_3479009 1786403818317884094987835 := by
  unfold tailWord_3479009
  simp only [CollatzResearch.WordTrace]
  refine ⟨126889882653152035278224081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84593255102101356852149387 126889882653152035278224081)
  ·
    refine ⟨95167411989864026458668061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126889882653152035278224081 95167411989864026458668061)
    ·
      refine ⟨35687779496199009922000523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95167411989864026458668061 35687779496199009922000523)
      ·
        refine ⟨53531669244298514883000785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35687779496199009922000523 53531669244298514883000785)
        ·
          refine ⟨40148751933223886162250589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53531669244298514883000785 40148751933223886162250589)
          ·
            refine ⟨15055781974958957310843971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40148751933223886162250589 15055781974958957310843971)
            ·
              refine ⟨22583672962438435966265957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15055781974958957310843971 22583672962438435966265957)
              ·
                refine ⟨4234438680457206743674867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22583672962438435966265957 4234438680457206743674867)
                ·
                  refine ⟨6351658020685810115512301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4234438680457206743674867 6351658020685810115512301)
                  ·
                    refine ⟨2381871757757178793317113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6351658020685810115512301 2381871757757178793317113)
                    ·
                      refine ⟨1786403818317884094987835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2381871757757178793317113 1786403818317884094987835)
                      ·
                        rfl

theorem cell23_3479009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 3, 2].length) (baseStart_3479009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479009 prefixEnd_3479009 := by exact prefixLift 3479009
  have htrace : WordTrace (prefixWord ++ tailWord_3479009) baseStart_3479009 baseEnd_3479009 := by
    simpa [prefixWord, tailWord_3479009, baseEnd_3479009] using wordTrace_append hprefix tailTrace_3479009
  have hstable : (prefixWord ++ tailWord_3479009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479009).length < 2 ^ (prefixWord ++ tailWord_3479009).sum := by decide
  have hdescent : baseEnd_3479009 < baseStart_3479009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479025 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 1, 3, 5]
def baseStart_3479025 : Nat := 118140960795 + 3479025 * 2 ^ 59
def prefixEnd_3479025 : Nat := 4983230072969 + 3 ^ 40 * 3479025 * 2
def baseEnd_3479025 : Nat := 1786412034008356032387761

theorem tailTrace_3479025 : CollatzResearch.WordTrace tailWord_3479025 prefixEnd_3479025 1786412034008356032387761 := by
  unfold tailWord_3479025
  simp only [CollatzResearch.WordTrace]
  refine ⟨126890466221094070010806529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84593644147396046673871019 126890466221094070010806529)
  ·
    refine ⟨95167849665820552508104897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126890466221094070010806529 95167849665820552508104897)
    ·
      refine ⟨71375887249365414381078673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95167849665820552508104897 71375887249365414381078673)
      ·
        refine ⟨53531915437024060785809005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71375887249365414381078673 53531915437024060785809005)
        ·
          refine ⟨20074468288884022794678377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53531915437024060785809005 20074468288884022794678377)
          ·
            refine ⟨15055851216663017096008783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20074468288884022794678377 15055851216663017096008783)
            ·
              refine ⟨22583776824994525644013175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15055851216663017096008783 22583776824994525644013175)
              ·
                refine ⟨33875665237491788466019763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22583776824994525644013175 33875665237491788466019763)
                ·
                  refine ⟨50813497856237682699029645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33875665237491788466019763 50813497856237682699029645)
                  ·
                    refine ⟨19055061696089131012136117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50813497856237682699029645 19055061696089131012136117)
                    ·
                      refine ⟨1786412034008356032387761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19055061696089131012136117 1786412034008356032387761)
                      ·
                        rfl

theorem cell23_3479025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_3479025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479025 prefixEnd_3479025 := by exact prefixLift 3479025
  have htrace : WordTrace (prefixWord ++ tailWord_3479025) baseStart_3479025 baseEnd_3479025 := by
    simpa [prefixWord, tailWord_3479025, baseEnd_3479025] using wordTrace_append hprefix tailTrace_3479025
  have hstable : (prefixWord ++ tailWord_3479025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479025).length < 2 ^ (prefixWord ++ tailWord_3479025).sum := by decide
  have hdescent : baseEnd_3479025 < baseStart_3479025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479026 : List Nat := [3, 2, 1, 4, 1, 1, 2, 3, 1, 3, 2]
def baseStart_3479026 : Nat := 118140960795 + 3479026 * 2 ^ 59
def prefixEnd_3479026 : Nat := 4983230072969 + 3 ^ 40 * 3479026 * 2
def baseEnd_3479026 : Nat := 1786412547489010528475257

theorem tailTrace_3479026 : CollatzResearch.WordTrace tailWord_3479026 prefixEnd_3479026 1786412547489010528475257 := by
  unfold tailWord_3479026
  simp only [CollatzResearch.WordTrace]
  refine ⟨31722625673522611795398233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84593668462726964787728621 31722625673522611795398233)
  ·
    refine ⟨23791969255141958846548675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31722625673522611795398233 23791969255141958846548675)
    ·
      refine ⟨35687953882712938269823013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23791969255141958846548675 35687953882712938269823013)
      ·
        refine ⟨6691491353008675925591815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35687953882712938269823013 6691491353008675925591815)
        ·
          refine ⟨10037237029513013888387723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6691491353008675925591815 10037237029513013888387723)
          ·
            refine ⟨15055855544269520832581585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10037237029513013888387723 15055855544269520832581585)
            ·
              refine ⟨11291891658202140624436189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15055855544269520832581585 11291891658202140624436189)
              ·
                refine ⟨4234459371825802734163571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11291891658202140624436189 4234459371825802734163571)
                ·
                  refine ⟨6351689057738704101245357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4234459371825802734163571 6351689057738704101245357)
                  ·
                    refine ⟨2381883396652014037967009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6351689057738704101245357 2381883396652014037967009)
                    ·
                      refine ⟨1786412547489010528475257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2381883396652014037967009 1786412547489010528475257)
                      ·
                        rfl

theorem cell23_3479026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_3479026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479026 prefixEnd_3479026 := by exact prefixLift 3479026
  have htrace : WordTrace (prefixWord ++ tailWord_3479026) baseStart_3479026 baseEnd_3479026 := by
    simpa [prefixWord, tailWord_3479026, baseEnd_3479026] using wordTrace_append hprefix tailTrace_3479026
  have hstable : (prefixWord ++ tailWord_3479026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479026).length < 2 ^ (prefixWord ++ tailWord_3479026).sum := by decide
  have hdescent : baseEnd_3479026 < baseStart_3479026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479060 : List Nat := [2, 4, 3, 1, 2, 2, 1, 2, 1, 3, 2]
def baseStart_3479060 : Nat := 118140960795 + 3479060 * 2 ^ 59
def prefixEnd_3479060 : Nat := 4983230072969 + 3 ^ 40 * 3479060 * 2
def baseEnd_3479060 : Nat := 1786430005831263395450101

theorem tailTrace_3479060 : CollatzResearch.WordTrace tailWord_3479060 prefixEnd_3479060 1786430005831263395450101 := by
  unfold tailWord_3479060
  simp only [CollatzResearch.WordTrace]
  refine ⟨63445871387983635494165317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84594495183978180658887089 63445871387983635494165317)
  ·
    refine ⟨11896100885246931655155997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63445871387983635494165317 11896100885246931655155997)
    ·
      refine ⟨4461037831967599370683499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11896100885246931655155997 4461037831967599370683499)
      ·
        refine ⟨6691556747951399056025249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4461037831967599370683499 6691556747951399056025249)
        ·
          refine ⟨5018667560963549292018937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6691556747951399056025249 5018667560963549292018937)
          ·
            refine ⟨3764000670722661969014203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5018667560963549292018937 3764000670722661969014203)
            ·
              refine ⟨5646001006083992953521305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3764000670722661969014203 5646001006083992953521305)
              ·
                refine ⟨4234500754562994715140979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5646001006083992953521305 4234500754562994715140979)
                ·
                  refine ⟨6351751131844492072711469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4234500754562994715140979 6351751131844492072711469)
                  ·
                    refine ⟨2381906674441684527266801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6351751131844492072711469 2381906674441684527266801)
                    ·
                      refine ⟨1786430005831263395450101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2381906674441684527266801 1786430005831263395450101)
                      ·
                        rfl

theorem cell23_3479060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_3479060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479060 prefixEnd_3479060 := by exact prefixLift 3479060
  have htrace : WordTrace (prefixWord ++ tailWord_3479060) baseStart_3479060 baseEnd_3479060 := by
    simpa [prefixWord, tailWord_3479060, baseEnd_3479060] using wordTrace_append hprefix tailTrace_3479060
  have hstable : (prefixWord ++ tailWord_3479060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479060).length < 2 ^ (prefixWord ++ tailWord_3479060).sum := by decide
  have hdescent : baseEnd_3479060 < baseStart_3479060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479096 : List Nat := [2, 1, 2, 1, 4, 4, 2, 2, 5]
def baseStart_3479096 : Nat := 118140960795 + 3479096 * 2 ^ 59
def prefixEnd_3479096 : Nat := 4983230072969 + 3 ^ 40 * 3479096 * 2
def baseEnd_3479096 : Nat := 198494276792758361622215

theorem tailTrace_3479096 : CollatzResearch.WordTrace tailWord_3479096 prefixEnd_3479096 198494276792758361622215 := by
  unfold tailWord_3479096
  simp only [CollatzResearch.WordTrace]
  refine ⟨63446527901918424568320571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84595370535891232757760761 63446527901918424568320571)
  ·
    refine ⟨95169791852877636852480857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63446527901918424568320571 95169791852877636852480857)
    ·
      refine ⟨71377343889658227639360643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95169791852877636852480857 71377343889658227639360643)
      ·
        refine ⟨107066015834487341459040965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71377343889658227639360643 107066015834487341459040965)
        ·
          refine ⟨20074877968966376523570181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107066015834487341459040965 20074877968966376523570181)
          ·
            refine ⟨3764039619181195598169409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20074877968966376523570181 3764039619181195598169409)
            ·
              refine ⟨2823029714385896698627057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3764039619181195598169409 2823029714385896698627057)
              ·
                refine ⟨2117272285789422523970293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2823029714385896698627057 2117272285789422523970293)
                ·
                  refine ⟨198494276792758361622215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2117272285789422523970293 198494276792758361622215)
                  ·
                    rfl

theorem cell23_3479096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 2, 5].length) (baseStart_3479096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479096 prefixEnd_3479096 := by exact prefixLift 3479096
  have htrace : WordTrace (prefixWord ++ tailWord_3479096) baseStart_3479096 baseEnd_3479096 := by
    simpa [prefixWord, tailWord_3479096, baseEnd_3479096] using wordTrace_append hprefix tailTrace_3479096
  have hstable : (prefixWord ++ tailWord_3479096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479096).length < 2 ^ (prefixWord ++ tailWord_3479096).sum := by decide
  have hdescent : baseEnd_3479096 < baseStart_3479096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479152 : List Nat := [2, 1, 1, 1, 6, 2, 1, 1, 8]
def baseStart_3479152 : Nat := 118140960795 + 3479152 * 2 ^ 59
def prefixEnd_3479152 : Nat := 4983230072969 + 3 ^ 40 * 3479152 * 2
def baseEnd_3479152 : Nat := 198497471783497448388853

theorem tailTrace_3479152 : CollatzResearch.WordTrace tailWord_3479152 prefixEnd_3479152 198497471783497448388853 := by
  unfold tailWord_3479152
  simp only [CollatzResearch.WordTrace]
  refine ⟨63447549145816985350339855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84596732194422647133786473 63447549145816985350339855)
  ·
    refine ⟨95171323718725478025509783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63447549145816985350339855 95171323718725478025509783)
    ·
      refine ⟨142756985578088217038264675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95171323718725478025509783 142756985578088217038264675)
      ·
        refine ⟨214135478367132325557397013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142756985578088217038264675 214135478367132325557397013)
        ·
          refine ⟨10037600548459327760502985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 214135478367132325557397013 10037600548459327760502985)
          ·
            refine ⟨7528200411344495820377239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10037600548459327760502985 7528200411344495820377239)
            ·
              refine ⟨11292300617016743730565859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7528200411344495820377239 11292300617016743730565859)
              ·
                refine ⟨16938450925525115595848789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11292300617016743730565859 16938450925525115595848789)
                ·
                  refine ⟨198497471783497448388853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16938450925525115595848789 198497471783497448388853)
                  ·
                    rfl

theorem cell23_3479152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 8].length) (baseStart_3479152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479152 prefixEnd_3479152 := by exact prefixLift 3479152
  have htrace : WordTrace (prefixWord ++ tailWord_3479152) baseStart_3479152 baseEnd_3479152 := by
    simpa [prefixWord, tailWord_3479152, baseEnd_3479152] using wordTrace_append hprefix tailTrace_3479152
  have hstable : (prefixWord ++ tailWord_3479152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479152).length < 2 ^ (prefixWord ++ tailWord_3479152).sum := by decide
  have hdescent : baseEnd_3479152 < baseStart_3479152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479179 : List Nat := [1, 1, 1, 1, 4, 1, 3, 4, 3, 1, 3]
def baseStart_3479179 : Nat := 118140960795 + 3479179 * 2 ^ 59
def prefixEnd_3479179 : Nat := 4983230072969 + 3 ^ 40 * 3479179 * 2
def baseEnd_3479179 : Nat := 1786491110029148429862053

theorem tailTrace_3479179 : CollatzResearch.WordTrace tailWord_3479179 prefixEnd_3479179 1786491110029148429862053 := by
  unfold tailWord_3479179
  simp only [CollatzResearch.WordTrace]
  refine ⟨126896083062536154311912591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84597388708357436207941727 126896083062536154311912591)
  ·
    refine ⟨190344124593804231467868887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126896083062536154311912591 190344124593804231467868887)
    ·
      refine ⟨285516186890706347201803331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190344124593804231467868887 285516186890706347201803331)
      ·
        refine ⟨428274280336059520802704997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285516186890706347201803331 428274280336059520802704997)
        ·
          refine ⟨80301427563011160150507187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 428274280336059520802704997 80301427563011160150507187)
          ·
            refine ⟨120452141344516740225760781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80301427563011160150507187 120452141344516740225760781)
            ·
              refine ⟨45169553004193777584660293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120452141344516740225760781 45169553004193777584660293)
              ·
                refine ⟨8469291188286333297123805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45169553004193777584660293 8469291188286333297123805)
                ·
                  refine ⟨3175984195607374986421427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8469291188286333297123805 3175984195607374986421427)
                  ·
                    refine ⟨4763976293411062479632141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3175984195607374986421427 4763976293411062479632141)
                    ·
                      refine ⟨1786491110029148429862053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4763976293411062479632141 1786491110029148429862053)
                      ·
                        rfl

theorem cell23_3479179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 3, 1, 3].length) (baseStart_3479179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479179 prefixEnd_3479179 := by exact prefixLift 3479179
  have htrace : WordTrace (prefixWord ++ tailWord_3479179) baseStart_3479179 baseEnd_3479179 := by
    simpa [prefixWord, tailWord_3479179, baseEnd_3479179] using wordTrace_append hprefix tailTrace_3479179
  have hstable : (prefixWord ++ tailWord_3479179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479179).length < 2 ^ (prefixWord ++ tailWord_3479179).sum := by decide
  have hdescent : baseEnd_3479179 < baseStart_3479179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479189 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 6, 3, 2]
def baseStart_3479189 : Nat := 118140960795 + 3479189 * 2 ^ 59
def prefixEnd_3479189 : Nat := 4983230072969 + 3 ^ 40 * 3479189 * 2
def baseEnd_3479189 : Nat := 1786496244835693390737007

theorem tailTrace_3479189 : CollatzResearch.WordTrace tailWord_3479189 prefixEnd_3479189 1786496244835693390737007 := by
  unfold tailWord_3479189
  simp only [CollatzResearch.WordTrace]
  refine ⟨126896447792499926019776621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84597631861666617346517747 126896447792499926019776621)
  ·
    refine ⟨47586167922187472257416233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126896447792499926019776621 47586167922187472257416233)
    ·
      refine ⟨35689625941640604193062175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47586167922187472257416233 35689625941640604193062175)
      ·
        refine ⟨53534438912460906289593263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35689625941640604193062175 53534438912460906289593263)
        ·
          refine ⟨80301658368691359434389895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53534438912460906289593263 80301658368691359434389895)
          ·
            refine ⟨120452487553037039151584843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80301658368691359434389895 120452487553037039151584843)
            ·
              refine ⟨180678731329555558727377265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120452487553037039151584843 180678731329555558727377265)
              ·
                refine ⟨135509048497166669045532949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180678731329555558727377265 135509048497166669045532949)
                ·
                  refine ⟨6351986648304687611509357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135509048497166669045532949 6351986648304687611509357)
                  ·
                    refine ⟨2381994993114257854316009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6351986648304687611509357 2381994993114257854316009)
                    ·
                      refine ⟨1786496244835693390737007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2381994993114257854316009 1786496244835693390737007)
                      ·
                        rfl

theorem cell23_3479189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 3, 2].length) (baseStart_3479189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479189 prefixEnd_3479189 := by exact prefixLift 3479189
  have htrace : WordTrace (prefixWord ++ tailWord_3479189) baseStart_3479189 baseEnd_3479189 := by
    simpa [prefixWord, tailWord_3479189, baseEnd_3479189] using wordTrace_append hprefix tailTrace_3479189
  have hstable : (prefixWord ++ tailWord_3479189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479189).length < 2 ^ (prefixWord ++ tailWord_3479189).sum := by decide
  have hdescent : baseEnd_3479189 < baseStart_3479189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479232 : List Nat := [2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 6]
def baseStart_3479232 : Nat := 118140960795 + 3479232 * 2 ^ 59
def prefixEnd_3479232 : Nat := 4983230072969 + 3 ^ 40 * 3479232 * 2
def baseEnd_3479232 : Nat := 1786518324503836722499309

theorem tailTrace_3479232 : CollatzResearch.WordTrace tailWord_3479232 prefixEnd_3479232 1786518324503836722499309 := by
  unfold tailWord_3479232
  simp only [CollatzResearch.WordTrace]
  refine ⟨63449008065672072181795975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84598677420896096242394633 63449008065672072181795975)
  ·
    refine ⟨95173512098508108272693963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63449008065672072181795975 95173512098508108272693963)
    ·
      refine ⟨142760268147762162409040945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95173512098508108272693963 142760268147762162409040945)
      ·
        refine ⟨107070201110821621806780709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142760268147762162409040945 107070201110821621806780709)
        ·
          refine ⟨20075662708279054088771383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107070201110821621806780709 20075662708279054088771383)
          ·
            refine ⟨30113494062418581133157075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20075662708279054088771383 30113494062418581133157075)
            ·
              refine ⟨45170241093627871699735613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30113494062418581133157075 45170241093627871699735613)
              ·
                refine ⟨16938840410110451887400855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45170241093627871699735613 16938840410110451887400855)
                ·
                  refine ⟨25408260615165677831101283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16938840410110451887400855 25408260615165677831101283)
                  ·
                    refine ⟨38112390922748516746651925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25408260615165677831101283 38112390922748516746651925)
                    ·
                      refine ⟨1786518324503836722499309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38112390922748516746651925 1786518324503836722499309)
                      ·
                        rfl

theorem cell23_3479232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_3479232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479232 prefixEnd_3479232 := by exact prefixLift 3479232
  have htrace : WordTrace (prefixWord ++ tailWord_3479232) baseStart_3479232 baseEnd_3479232 := by
    simpa [prefixWord, tailWord_3479232, baseEnd_3479232] using wordTrace_append hprefix tailTrace_3479232
  have hstable : (prefixWord ++ tailWord_3479232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479232).length < 2 ^ (prefixWord ++ tailWord_3479232).sum := by decide
  have hdescent : baseEnd_3479232 < baseStart_3479232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479239 : List Nat := [1, 1, 4, 1, 1, 1, 5, 1, 3, 2, 3]
def baseStart_3479239 : Nat := 118140960795 + 3479239 * 2 ^ 59
def prefixEnd_3479239 : Nat := 4983230072969 + 3 ^ 40 * 3479239 * 2
def baseEnd_3479239 : Nat := 1786521918868418195111777

theorem tailTrace_3479239 : CollatzResearch.WordTrace tailWord_3479239 prefixEnd_3479239 1786521918868418195111777 := by
  unfold tailWord_3479239
  simp only [CollatzResearch.WordTrace]
  refine ⟨126898271442318784559096771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84598847628212523039397847 126898271442318784559096771)
  ·
    refine ⟨190347407163478176838645157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126898271442318784559096771 190347407163478176838645157)
    ·
      refine ⟨35690138843152158157245967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190347407163478176838645157 35690138843152158157245967)
      ·
        refine ⟨53535208264728237235868951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35690138843152158157245967 53535208264728237235868951)
        ·
          refine ⟨80302812397092355853803427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53535208264728237235868951 80302812397092355853803427)
          ·
            refine ⟨120454218595638533780705141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80302812397092355853803427 120454218595638533780705141)
            ·
              refine ⟨11292582993341112541941107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120454218595638533780705141 11292582993341112541941107)
              ·
                refine ⟨16938874490011668812911661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11292582993341112541941107 16938874490011668812911661)
                ·
                  refine ⟨6352077933754375804841873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16938874490011668812911661 6352077933754375804841873)
                  ·
                    refine ⟨4764058450315781853631405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6352077933754375804841873 4764058450315781853631405)
                    ·
                      refine ⟨1786521918868418195111777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4764058450315781853631405 1786521918868418195111777)
                      ·
                        rfl

theorem cell23_3479239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_3479239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479239 prefixEnd_3479239 := by exact prefixLift 3479239
  have htrace : WordTrace (prefixWord ++ tailWord_3479239) baseStart_3479239 baseEnd_3479239 := by
    simpa [prefixWord, tailWord_3479239, baseEnd_3479239] using wordTrace_append hprefix tailTrace_3479239
  have hstable : (prefixWord ++ tailWord_3479239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479239).length < 2 ^ (prefixWord ++ tailWord_3479239).sum := by decide
  have hdescent : baseEnd_3479239 < baseStart_3479239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479249 : List Nat := [1, 2, 2, 1, 2, 5, 1, 2, 1, 2, 4]
def baseStart_3479249 : Nat := 118140960795 + 3479249 * 2 ^ 59
def prefixEnd_3479249 : Nat := 4983230072969 + 3 ^ 40 * 3479249 * 2
def baseEnd_3479249 : Nat := 1786527053674963155986731

theorem tailTrace_3479249 : CollatzResearch.WordTrace tailWord_3479249 prefixEnd_3479249 1786527053674963155986731 := by
  unfold tailWord_3479249
  simp only [CollatzResearch.WordTrace]
  refine ⟨126898636172282556266960801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84599090781521704177973867 126898636172282556266960801)
  ·
    refine ⟨95173977129211917200220601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126898636172282556266960801 95173977129211917200220601)
    ·
      refine ⟨71380482846908937900165451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95173977129211917200220601 71380482846908937900165451)
      ·
        refine ⟨107070724270363406850248177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71380482846908937900165451 107070724270363406850248177)
        ·
          refine ⟨80303043202772555137686133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107070724270363406850248177 80303043202772555137686133)
          ·
            refine ⟨7528410300259927044158075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80303043202772555137686133 7528410300259927044158075)
            ·
              refine ⟨11292615450389890566237113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7528410300259927044158075 11292615450389890566237113)
              ·
                refine ⟨8469461587792417924677835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11292615450389890566237113 8469461587792417924677835)
                ·
                  refine ⟨12704192381688626887016753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8469461587792417924677835 12704192381688626887016753)
                  ·
                    refine ⟨9528144286266470165262565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12704192381688626887016753 9528144286266470165262565)
                    ·
                      refine ⟨1786527053674963155986731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9528144286266470165262565 1786527053674963155986731)
                      ·
                        rfl

theorem cell23_3479249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_3479249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479249 prefixEnd_3479249 := by exact prefixLift 3479249
  have htrace : WordTrace (prefixWord ++ tailWord_3479249) baseStart_3479249 baseEnd_3479249 := by
    simpa [prefixWord, tailWord_3479249, baseEnd_3479249] using wordTrace_append hprefix tailTrace_3479249
  have hstable : (prefixWord ++ tailWord_3479249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479249).length < 2 ^ (prefixWord ++ tailWord_3479249).sum := by decide
  have hdescent : baseEnd_3479249 < baseStart_3479249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479269 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 3, 3, 3]
def baseStart_3479269 : Nat := 118140960795 + 3479269 * 2 ^ 59
def prefixEnd_3479269 : Nat := 4983230072969 + 3 ^ 40 * 3479269 * 2
def baseEnd_3479269 : Nat := 1786537323288053077736639

theorem tailTrace_3479269 : CollatzResearch.WordTrace tailWord_3479269 prefixEnd_3479269 1786537323288053077736639 := by
  unfold tailWord_3479269
  simp only [CollatzResearch.WordTrace]
  refine ⟨126899365632210099682688861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84599577088140066455125907 126899365632210099682688861)
  ·
    refine ⟨47587262112078787381008323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126899365632210099682688861 47587262112078787381008323)
    ·
      refine ⟨71380893168118181071512485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47587262112078787381008323 71380893168118181071512485)
      ·
        refine ⟨13383917469022158950908591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71380893168118181071512485 13383917469022158950908591)
        ·
          refine ⟨20075876203533238426362887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13383917469022158950908591 20075876203533238426362887)
          ·
            refine ⟨30113814305299857639544331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20075876203533238426362887 30113814305299857639544331)
            ·
              refine ⟨45170721457949786459316497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30113814305299857639544331 45170721457949786459316497)
              ·
                refine ⟨33878041093462339844487373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45170721457949786459316497 33878041093462339844487373)
                ·
                  refine ⟨12704265410048377441682765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33878041093462339844487373 12704265410048377441682765)
                  ·
                    refine ⟨4764099528768141540631037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12704265410048377441682765 4764099528768141540631037)
                    ·
                      refine ⟨1786537323288053077736639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4764099528768141540631037 1786537323288053077736639)
                      ·
                        rfl

theorem cell23_3479269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_3479269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479269 prefixEnd_3479269 := by exact prefixLift 3479269
  have htrace : WordTrace (prefixWord ++ tailWord_3479269) baseStart_3479269 baseEnd_3479269 := by
    simpa [prefixWord, tailWord_3479269, baseEnd_3479269] using wordTrace_append hprefix tailTrace_3479269
  have hstable : (prefixWord ++ tailWord_3479269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479269).length < 2 ^ (prefixWord ++ tailWord_3479269).sum := by decide
  have hdescent : baseEnd_3479269 < baseStart_3479269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479286 : List Nat := [5, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3]
def baseStart_3479286 : Nat := 118140960795 + 3479286 * 2 ^ 59
def prefixEnd_3479286 : Nat := 4983230072969 + 3 ^ 40 * 3479286 * 2
def baseEnd_3479286 : Nat := 1786546052459179511224061

theorem tailTrace_3479286 : CollatzResearch.WordTrace tailWord_3479286 prefixEnd_3479286 1786546052459179511224061 := by
  unfold tailWord_3479286
  simp only [CollatzResearch.WordTrace]
  refine ⟨7931249104571781974128607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84599990448765674390705141 7931249104571781974128607)
  ·
    refine ⟨11896873656857672961192911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7931249104571781974128607 11896873656857672961192911)
    ·
      refine ⟨17845310485286509441789367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11896873656857672961192911 17845310485286509441789367)
      ·
        refine ⟨26767965727929764162684051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17845310485286509441789367 26767965727929764162684051)
        ·
          refine ⟨40151948591894646244026077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26767965727929764162684051 40151948591894646244026077)
          ·
            refine ⟨15056980721960492341509779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40151948591894646244026077 15056980721960492341509779)
            ·
              refine ⟨22585471082940738512264669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15056980721960492341509779 22585471082940738512264669)
              ·
                refine ⟨8469551656102776942099251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22585471082940738512264669 8469551656102776942099251)
                ·
                  refine ⟨12704327484154165413148877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8469551656102776942099251 12704327484154165413148877)
                  ·
                    refine ⟨4764122806557812029930829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12704327484154165413148877 4764122806557812029930829)
                    ·
                      refine ⟨1786546052459179511224061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4764122806557812029930829 1786546052459179511224061)
                      ·
                        rfl

theorem cell23_3479286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_3479286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479286 prefixEnd_3479286 := by exact prefixLift 3479286
  have htrace : WordTrace (prefixWord ++ tailWord_3479286) baseStart_3479286 baseEnd_3479286 := by
    simpa [prefixWord, tailWord_3479286, baseEnd_3479286] using wordTrace_append hprefix tailTrace_3479286
  have hstable : (prefixWord ++ tailWord_3479286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479286).length < 2 ^ (prefixWord ++ tailWord_3479286).sum := by decide
  have hdescent : baseEnd_3479286 < baseStart_3479286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479319 : List Nat := [1, 1, 3, 4, 2, 1, 1, 2, 2, 6]
def baseStart_3479319 : Nat := 118140960795 + 3479319 * 2 ^ 59
def prefixEnd_3479319 : Nat := 4983230072969 + 3 ^ 40 * 3479319 * 2
def baseEnd_3479319 : Nat := 595520999106925960703803

theorem tailTrace_3479319 : CollatzResearch.WordTrace tailWord_3479319 prefixEnd_3479319 595520999106925960703803 := by
  unfold tailWord_3479319
  simp only [CollatzResearch.WordTrace]
  refine ⟨126901189282028958222009011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84600792854685972148006007 126901189282028958222009011)
  ·
    refine ⟨190351783923043437333013517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126901189282028958222009011 190351783923043437333013517)
    ·
      refine ⟨71381918971141288999880069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190351783923043437333013517 71381918971141288999880069)
      ·
        refine ⟨13384109807088991687477513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71381918971141288999880069 13384109807088991687477513)
        ·
          refine ⟨10038082355316743765608135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13384109807088991687477513 10038082355316743765608135)
          ·
            refine ⟨15057123532975115648412203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10038082355316743765608135 15057123532975115648412203)
            ·
              refine ⟨22585685299462673472618305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15057123532975115648412203 22585685299462673472618305)
              ·
                refine ⟨16939263974597005104463729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22585685299462673472618305 16939263974597005104463729)
                ·
                  refine ⟨12704447980947753828347797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16939263974597005104463729 12704447980947753828347797)
                  ·
                    refine ⟨595520999106925960703803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12704447980947753828347797 595520999106925960703803)
                    ·
                      rfl

theorem cell23_3479319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 6].length) (baseStart_3479319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479319 prefixEnd_3479319 := by exact prefixLift 3479319
  have htrace : WordTrace (prefixWord ++ tailWord_3479319) baseStart_3479319 baseEnd_3479319 := by
    simpa [prefixWord, tailWord_3479319, baseEnd_3479319] using wordTrace_append hprefix tailTrace_3479319
  have hstable : (prefixWord ++ tailWord_3479319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479319).length < 2 ^ (prefixWord ++ tailWord_3479319).sum := by decide
  have hdescent : baseEnd_3479319 < baseStart_3479319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479383 : List Nat := [1, 1, 3, 2, 6, 1, 1, 1, 7]
def baseStart_3479383 : Nat := 118140960795 + 3479383 * 2 ^ 59
def prefixEnd_3479383 : Nat := 4983230072969 + 3 ^ 40 * 3479383 * 2
def baseEnd_3479383 : Nat := 198510651120296181301235

theorem tailTrace_3479383 : CollatzResearch.WordTrace tailWord_3479383 prefixEnd_3479383 198510651120296181301235 := by
  unfold tailWord_3479383
  simp only [CollatzResearch.WordTrace]
  refine ⟨126903523553797097152338803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84602349035864731434892535 126903523553797097152338803)
  ·
    refine ⟨190355285330695645728508205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126903523553797097152338803 190355285330695645728508205)
    ·
      refine ⟨71383231999010867148190577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190355285330695645728508205 71383231999010867148190577)
      ·
        refine ⟨53537423999258150361142933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71383231999010867148190577 53537423999258150361142933)
        ·
          refine ⟨2509566749965225798178575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53537423999258150361142933 2509566749965225798178575)
          ·
            refine ⟨3764350124947838697267863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2509566749965225798178575 3764350124947838697267863)
            ·
              refine ⟨5646525187421758045901795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3764350124947838697267863 5646525187421758045901795)
              ·
                refine ⟨8469787781132637068852693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5646525187421758045901795 8469787781132637068852693)
                ·
                  refine ⟨198510651120296181301235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8469787781132637068852693 198510651120296181301235)
                  ·
                    rfl

theorem cell23_3479383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 7].length) (baseStart_3479383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479383 prefixEnd_3479383 := by exact prefixLift 3479383
  have htrace : WordTrace (prefixWord ++ tailWord_3479383) baseStart_3479383 baseEnd_3479383 := by
    simpa [prefixWord, tailWord_3479383, baseEnd_3479383] using wordTrace_append hprefix tailTrace_3479383
  have hstable : (prefixWord ++ tailWord_3479383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479383).length < 2 ^ (prefixWord ++ tailWord_3479383).sum := by decide
  have hdescent : baseEnd_3479383 < baseStart_3479383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479386 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 2, 5, 2]
def baseStart_3479386 : Nat := 118140960795 + 3479386 * 2 ^ 59
def prefixEnd_3479386 : Nat := 4983230072969 + 3 ^ 40 * 3479386 * 2
def baseEnd_3479386 : Nat := 1786597400524629119973601

theorem tailTrace_3479386 : CollatzResearch.WordTrace tailWord_3479386 prefixEnd_3479386 1786597400524629119973601 := by
  unfold tailWord_3479386
  simp only [CollatzResearch.WordTrace]
  refine ⟨31725908243196557166174503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84602421981857485776465341 31725908243196557166174503)
  ·
    refine ⟨47588862364794835749261755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31725908243196557166174503 47588862364794835749261755)
    ·
      refine ⟨71383293547192253623892633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47588862364794835749261755 71383293547192253623892633)
      ·
        refine ⟨53537470160394190217919475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71383293547192253623892633 53537470160394190217919475)
        ·
          refine ⟨80306205240591285326879213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53537470160394190217919475 80306205240591285326879213)
          ·
            refine ⟨30114826965221731997579705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80306205240591285326879213 30114826965221731997579705)
            ·
              refine ⟨22586120223916298998184779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30114826965221731997579705 22586120223916298998184779)
              ·
                refine ⟨33879180335874448497277169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22586120223916298998184779 33879180335874448497277169)
                ·
                  refine ⟨25409385251905836372957877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33879180335874448497277169 25409385251905836372957877)
                  ·
                    refine ⟨2382129867366172159964801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25409385251905836372957877 2382129867366172159964801)
                    ·
                      refine ⟨1786597400524629119973601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2382129867366172159964801 1786597400524629119973601)
                      ·
                        rfl

theorem cell23_3479386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 2, 5, 2].length) (baseStart_3479386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479386 prefixEnd_3479386 := by exact prefixLift 3479386
  have htrace : WordTrace (prefixWord ++ tailWord_3479386) baseStart_3479386 baseEnd_3479386 := by
    simpa [prefixWord, tailWord_3479386, baseEnd_3479386] using wordTrace_append hprefix tailTrace_3479386
  have hstable : (prefixWord ++ tailWord_3479386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479386).length < 2 ^ (prefixWord ++ tailWord_3479386).sum := by decide
  have hdescent : baseEnd_3479386 < baseStart_3479386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479394 : List Nat := [3, 3, 2, 1, 2, 3, 2, 1, 2, 2, 2]
def baseStart_3479394 : Nat := 118140960795 + 3479394 * 2 ^ 59
def prefixEnd_3479394 : Nat := 4983230072969 + 3 ^ 40 * 3479394 * 2
def baseEnd_3479394 : Nat := 1786601508369865088673565

theorem tailTrace_3479394 : CollatzResearch.WordTrace tailWord_3479394 prefixEnd_3479394 1786601508369865088673565 := by
  unfold tailWord_3479394
  simp only [CollatzResearch.WordTrace]
  refine ⟨31725981189189311507747309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84602616504504830687326157 31725981189189311507747309)
  ·
    refine ⟨11897242945945991815405241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31725981189189311507747309 11897242945945991815405241)
    ·
      refine ⟨8922932209459493861553931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11897242945945991815405241 8922932209459493861553931)
      ·
        refine ⟨13384398314189240792330897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8922932209459493861553931 13384398314189240792330897)
        ·
          refine ⟨10038298735641930594248173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13384398314189240792330897 10038298735641930594248173)
          ·
            refine ⟨3764362025865723972843065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10038298735641930594248173 3764362025865723972843065)
            ·
              refine ⟨2823271519399292979632299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3764362025865723972843065 2823271519399292979632299)
              ·
                refine ⟨4234907279098939469448449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2823271519399292979632299 4234907279098939469448449)
                ·
                  refine ⟨3176180459324204602086337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4234907279098939469448449 3176180459324204602086337)
                  ·
                    refine ⟨2382135344493153451564753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3176180459324204602086337 2382135344493153451564753)
                    ·
                      refine ⟨1786601508369865088673565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2382135344493153451564753 1786601508369865088673565)
                      ·
                        rfl

theorem cell23_3479394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_3479394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479394 prefixEnd_3479394 := by exact prefixLift 3479394
  have htrace : WordTrace (prefixWord ++ tailWord_3479394) baseStart_3479394 baseEnd_3479394 := by
    simpa [prefixWord, tailWord_3479394, baseEnd_3479394] using wordTrace_append hprefix tailTrace_3479394
  have hstable : (prefixWord ++ tailWord_3479394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479394).length < 2 ^ (prefixWord ++ tailWord_3479394).sum := by decide
  have hdescent : baseEnd_3479394 < baseStart_3479394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479429 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 2, 1, 6]
def baseStart_3479429 : Nat := 118140960795 + 3479429 * 2 ^ 59
def prefixEnd_3479429 : Nat := 4983230072969 + 3 ^ 40 * 3479429 * 2
def baseEnd_3479429 : Nat := 1786619480192772451735903

theorem tailTrace_3479429 : CollatzResearch.WordTrace tailWord_3479429 prefixEnd_3479429 1786619480192772451735903 := by
  unfold tailWord_3479429
  simp only [CollatzResearch.WordTrace]
  refine ⟨126905201311630447008513341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84603467541086964672342227 126905201311630447008513341)
  ·
    refine ⟨47589450491861417628192503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126905201311630447008513341 47589450491861417628192503)
    ·
      refine ⟨71384175737792126442288755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47589450491861417628192503 71384175737792126442288755)
      ·
        refine ⟨107076263606688189663433133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71384175737792126442288755 107076263606688189663433133)
        ·
          refine ⟨40153598852508071123787425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107076263606688189663433133 40153598852508071123787425)
          ·
            refine ⟨30115199139381053342840569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40153598852508071123787425 30115199139381053342840569)
            ·
              refine ⟨22586399354535790007130427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30115199139381053342840569 22586399354535790007130427)
              ·
                refine ⟨33879599031803685010695641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22586399354535790007130427 33879599031803685010695641)
                ·
                  refine ⟨25409699273852763758021731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33879599031803685010695641 25409699273852763758021731)
                  ·
                    refine ⟨38114548910779145637032597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25409699273852763758021731 38114548910779145637032597)
                    ·
                      refine ⟨1786619480192772451735903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38114548910779145637032597 1786619480192772451735903)
                      ·
                        rfl

theorem cell23_3479429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_3479429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479429 prefixEnd_3479429 := by exact prefixLift 3479429
  have htrace : WordTrace (prefixWord ++ tailWord_3479429) baseStart_3479429 baseEnd_3479429 := by
    simpa [prefixWord, tailWord_3479429, baseEnd_3479429] using wordTrace_append hprefix tailTrace_3479429
  have hstable : (prefixWord ++ tailWord_3479429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479429).length < 2 ^ (prefixWord ++ tailWord_3479429).sum := by decide
  have hdescent : baseEnd_3479429 < baseStart_3479429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479479 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 5]
def baseStart_3479479 : Nat := 118140960795 + 3479479 * 2 ^ 59
def prefixEnd_3479479 : Nat := 4983230072969 + 3 ^ 40 * 3479479 * 2
def baseEnd_3479479 : Nat := 1786645154225497256110673

theorem tailTrace_3479479 : CollatzResearch.WordTrace tailWord_3479479 prefixEnd_3479479 1786645154225497256110673 := by
  unfold tailWord_3479479
  simp only [CollatzResearch.WordTrace]
  refine ⟨126907024961449305547833491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84604683307632870365222327 126907024961449305547833491)
  ·
    refine ⟨190360537442173958321750237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126907024961449305547833491 190360537442173958321750237)
    ·
      refine ⟨71385201540815234370656339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190360537442173958321750237 71385201540815234370656339)
      ·
        refine ⟨107077802311222851555984509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71385201540815234370656339 107077802311222851555984509)
        ·
          refine ⟨40154175866708569333494191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107077802311222851555984509 40154175866708569333494191)
          ·
            refine ⟨60231263800062854000241287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40154175866708569333494191 60231263800062854000241287)
            ·
              refine ⟨90346895700094281000361931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60231263800062854000241287 90346895700094281000361931)
              ·
                refine ⟨135520343550141421500542897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90346895700094281000361931 135520343550141421500542897)
                ·
                  refine ⟨101640257662606066125407173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135520343550141421500542897 101640257662606066125407173)
                  ·
                    refine ⟨19057548311738637398513845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101640257662606066125407173 19057548311738637398513845)
                    ·
                      refine ⟨1786645154225497256110673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19057548311738637398513845 1786645154225497256110673)
                      ·
                        rfl

theorem cell23_3479479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_3479479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479479 prefixEnd_3479479 := by exact prefixLift 3479479
  have htrace : WordTrace (prefixWord ++ tailWord_3479479) baseStart_3479479 baseEnd_3479479 := by
    simpa [prefixWord, tailWord_3479479, baseEnd_3479479] using wordTrace_append hprefix tailTrace_3479479
  have hstable : (prefixWord ++ tailWord_3479479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479479).length < 2 ^ (prefixWord ++ tailWord_3479479).sum := by decide
  have hdescent : baseEnd_3479479 < baseStart_3479479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479500 : List Nat := [2, 2, 1, 4, 1, 3, 2, 1, 3, 1, 3]
def baseStart_3479500 : Nat := 118140960795 + 3479500 * 2 ^ 59
def prefixEnd_3479500 : Nat := 4983230072969 + 3 ^ 40 * 3479500 * 2
def baseEnd_3479500 : Nat := 1786655937319241673948077

theorem tailTrace_3479500 : CollatzResearch.WordTrace tailWord_3479500 prefixEnd_3479500 1786655937319241673948077 := by
  unfold tailWord_3479500
  simp only [CollatzResearch.WordTrace]
  refine ⟨63453895447186613067173977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84605193929582150756231969 63453895447186613067173977)
  ·
    refine ⟨47590421585389959800380483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63453895447186613067173977 47590421585389959800380483)
    ·
      refine ⟨71385632378084939700570725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47590421585389959800380483 71385632378084939700570725)
      ·
        refine ⟨13384806070890926193857011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71385632378084939700570725 13384806070890926193857011)
        ·
          refine ⟨20077209106336389290785517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13384806070890926193857011 20077209106336389290785517)
          ·
            refine ⟨7528953414876145984044569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20077209106336389290785517 7528953414876145984044569)
            ·
              refine ⟨5646715061157109488033427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7528953414876145984044569 5646715061157109488033427)
              ·
                refine ⟨8470072591735664232050141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5646715061157109488033427 8470072591735664232050141)
                ·
                  refine ⟨3176277221900874087018803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8470072591735664232050141 3176277221900874087018803)
                  ·
                    refine ⟨4764415832851311130528205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3176277221900874087018803 4764415832851311130528205)
                    ·
                      refine ⟨1786655937319241673948077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4764415832851311130528205 1786655937319241673948077)
                      ·
                        rfl

theorem cell23_3479500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_3479500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479500 prefixEnd_3479500 := by exact prefixLift 3479500
  have htrace : WordTrace (prefixWord ++ tailWord_3479500) baseStart_3479500 baseEnd_3479500 := by
    simpa [prefixWord, tailWord_3479500, baseEnd_3479500] using wordTrace_append hprefix tailTrace_3479500
  have hstable : (prefixWord ++ tailWord_3479500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479500).length < 2 ^ (prefixWord ++ tailWord_3479500).sum := by decide
  have hdescent : baseEnd_3479500 < baseStart_3479500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479523 : List Nat := [1, 1, 1, 6, 1, 2, 1, 4, 1, 1, 4]
def baseStart_3479523 : Nat := 118140960795 + 3479523 * 2 ^ 59
def prefixEnd_3479523 : Nat := 4983230072969 + 3 ^ 40 * 3479523 * 2
def baseEnd_3479523 : Nat := 1786667747374295083960471

theorem tailTrace_3479523 : CollatzResearch.WordTrace tailWord_3479523 prefixEnd_3479523 1786667747374295083960471 := by
  unfold tailWord_3479523
  simp only [CollatzResearch.WordTrace]
  refine ⟨126908629773289901062435223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84605753182193267374956815 126908629773289901062435223)
  ·
    refine ⟨190362944659934851593652835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126908629773289901062435223 190362944659934851593652835)
    ·
      refine ⟨285544416989902277390479253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190362944659934851593652835 285544416989902277390479253)
      ·
        refine ⟨13384894546401669252678715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 285544416989902277390479253 13384894546401669252678715)
        ·
          refine ⟨20077341819602503879018073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13384894546401669252678715 20077341819602503879018073)
          ·
            refine ⟨15058006364701877909263555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20077341819602503879018073 15058006364701877909263555)
            ·
              refine ⟨22587009547052816863895333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15058006364701877909263555 22587009547052816863895333)
              ·
                refine ⟨4235064290072403161980375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22587009547052816863895333 4235064290072403161980375)
                ·
                  refine ⟨6352596435108604742970563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4235064290072403161980375 6352596435108604742970563)
                  ·
                    refine ⟨9528894652662907114455845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6352596435108604742970563 9528894652662907114455845)
                    ·
                      refine ⟨1786667747374295083960471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9528894652662907114455845 1786667747374295083960471)
                      ·
                        rfl

theorem cell23_3479523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_3479523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479523 prefixEnd_3479523 := by exact prefixLift 3479523
  have htrace : WordTrace (prefixWord ++ tailWord_3479523) baseStart_3479523 baseEnd_3479523 := by
    simpa [prefixWord, tailWord_3479523, baseEnd_3479523] using wordTrace_append hprefix tailTrace_3479523
  have hstable : (prefixWord ++ tailWord_3479523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479523).length < 2 ^ (prefixWord ++ tailWord_3479523).sum := by decide
  have hdescent : baseEnd_3479523 < baseStart_3479523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479534 : List Nat := [4, 1, 2, 1, 3, 3, 1, 3, 1, 1, 3]
def baseStart_3479534 : Nat := 118140960795 + 3479534 * 2 ^ 59
def prefixEnd_3479534 : Nat := 4983230072969 + 3 ^ 40 * 3479534 * 2
def baseEnd_3479534 : Nat := 1786673395661494540922921

theorem tailTrace_3479534 : CollatzResearch.WordTrace tailWord_3479534 prefixEnd_3479534 1786673395661494540922921 := by
  unfold tailWord_3479534
  simp only [CollatzResearch.WordTrace]
  refine ⟨15863628872031256242635707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84606020650833366627390437 15863628872031256242635707)
  ·
    refine ⟨23795443308046884363953561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15863628872031256242635707 23795443308046884363953561)
    ·
      refine ⟨17846582481035163272965171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23795443308046884363953561 17846582481035163272965171)
      ·
        refine ⟨26769873721552744909447757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17846582481035163272965171 26769873721552744909447757)
        ·
          refine ⟨10038702645582279341042909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26769873721552744909447757 10038702645582279341042909)
          ·
            refine ⟨3764513492093354752891091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10038702645582279341042909 3764513492093354752891091)
            ·
              refine ⟨5646770238140032129336637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3764513492093354752891091 5646770238140032129336637)
              ·
                refine ⟨2117538839302512048501239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5646770238140032129336637 2117538839302512048501239)
                ·
                  refine ⟨3176308258953768072751859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2117538839302512048501239 3176308258953768072751859)
                  ·
                    refine ⟨4764462388430652109127789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3176308258953768072751859 4764462388430652109127789)
                    ·
                      refine ⟨1786673395661494540922921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4764462388430652109127789 1786673395661494540922921)
                      ·
                        rfl

theorem cell23_3479534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_3479534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479534 prefixEnd_3479534 := by exact prefixLift 3479534
  have htrace : WordTrace (prefixWord ++ tailWord_3479534) baseStart_3479534 baseEnd_3479534 := by
    simpa [prefixWord, tailWord_3479534, baseEnd_3479534] using wordTrace_append hprefix tailTrace_3479534
  have hstable : (prefixWord ++ tailWord_3479534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479534).length < 2 ^ (prefixWord ++ tailWord_3479534).sum := by decide
  have hdescent : baseEnd_3479534 < baseStart_3479534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479536 : List Nat := [2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 4]
def baseStart_3479536 : Nat := 118140960795 + 3479536 * 2 ^ 59
def prefixEnd_3479536 : Nat := 4983230072969 + 3 ^ 40 * 3479536 * 2
def baseEnd_3479536 : Nat := 1786674422622803533097911

theorem tailTrace_3479536 : CollatzResearch.WordTrace tailWord_3479536 prefixEnd_3479536 1786674422622803533097911 := by
  unfold tailWord_3479536
  simp only [CollatzResearch.WordTrace]
  refine ⟨63454551961121402141329231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84606069281495202855105641 63454551961121402141329231)
  ·
    refine ⟨95181827941682103211993847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63454551961121402141329231 95181827941682103211993847)
    ·
      refine ⟨142772741912523154817990771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95181827941682103211993847 142772741912523154817990771)
      ·
        refine ⟨214159112868784732226986157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142772741912523154817990771 214159112868784732226986157)
        ·
          refine ⟨80309667325794274585119809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214159112868784732226986157 80309667325794274585119809)
          ·
            refine ⟨60232250494345705938839857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80309667325794274585119809 60232250494345705938839857)
            ·
              refine ⟨45174187870759279454129893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60232250494345705938839857 45174187870759279454129893)
              ·
                refine ⟨8470160225767364897649355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45174187870759279454129893 8470160225767364897649355)
                ·
                  refine ⟨12705240338651047346474033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8470160225767364897649355 12705240338651047346474033)
                  ·
                    refine ⟨9528930253988285509855525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12705240338651047346474033 9528930253988285509855525)
                    ·
                      refine ⟨1786674422622803533097911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9528930253988285509855525 1786674422622803533097911)
                      ·
                        rfl

theorem cell23_3479536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 4].length) (baseStart_3479536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479536 prefixEnd_3479536 := by exact prefixLift 3479536
  have htrace : WordTrace (prefixWord ++ tailWord_3479536) baseStart_3479536 baseEnd_3479536 := by
    simpa [prefixWord, tailWord_3479536, baseEnd_3479536] using wordTrace_append hprefix tailTrace_3479536
  have hstable : (prefixWord ++ tailWord_3479536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479536).length < 2 ^ (prefixWord ++ tailWord_3479536).sum := by decide
  have hdescent : baseEnd_3479536 < baseStart_3479536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479550 : List Nat := [4, 2, 2, 2, 1, 1, 2, 1, 4, 4]
def baseStart_3479550 : Nat := 118140960795 + 3479550 * 2 ^ 59
def prefixEnd_3479550 : Nat := 4983230072969 + 3 ^ 40 * 3479550 * 2
def baseEnd_3479550 : Nat := 595560537117322159440949

theorem tailTrace_3479550 : CollatzResearch.WordTrace tailWord_3479550 prefixEnd_3479550 595560537117322159440949 := by
  unfold tailWord_3479550
  simp only [CollatzResearch.WordTrace]
  refine ⟨15863701818024010584208513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84606409696128056449112069 15863701818024010584208513)
  ·
    refine ⟨11897776363518007938156385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15863701818024010584208513 11897776363518007938156385)
    ·
      refine ⟨8923332272638505953617289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11897776363518007938156385 8923332272638505953617289)
      ·
        refine ⟨6692499204478879465212967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8923332272638505953617289 6692499204478879465212967)
        ·
          refine ⟨10038748806718319197819451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6692499204478879465212967 10038748806718319197819451)
          ·
            refine ⟨15058123210077478796729177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10038748806718319197819451 15058123210077478796729177)
            ·
              refine ⟨11293592407558109097546883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15058123210077478796729177 11293592407558109097546883)
              ·
                refine ⟨16940388611337163646320325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11293592407558109097546883 16940388611337163646320325)
                ·
                  refine ⟨3176322864625718183685061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16940388611337163646320325 3176322864625718183685061)
                  ·
                    refine ⟨595560537117322159440949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3176322864625718183685061 595560537117322159440949)
                    ·
                      rfl

theorem cell23_3479550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_3479550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479550 prefixEnd_3479550 := by exact prefixLift 3479550
  have htrace : WordTrace (prefixWord ++ tailWord_3479550) baseStart_3479550 baseEnd_3479550 := by
    simpa [prefixWord, tailWord_3479550, baseEnd_3479550] using wordTrace_append hprefix tailTrace_3479550
  have hstable : (prefixWord ++ tailWord_3479550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479550).length < 2 ^ (prefixWord ++ tailWord_3479550).sum := by decide
  have hdescent : baseEnd_3479550 < baseStart_3479550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479557 : List Nat := [1, 3, 1, 1, 2, 6, 1, 1, 3, 2, 2]
def baseStart_3479557 : Nat := 118140960795 + 3479557 * 2 ^ 59
def prefixEnd_3479557 : Nat := 4983230072969 + 3 ^ 40 * 3479557 * 2
def baseEnd_3479557 : Nat := 1786685205716547950935315

theorem tailTrace_3479557 : CollatzResearch.WordTrace tailWord_3479557 prefixEnd_3479557 1786685205716547950935315 := by
  unfold tailWord_3479557
  simp only [CollatzResearch.WordTrace]
  refine ⟨126909869855166724869172925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84606579903444483246115283 126909869855166724869172925)
  ·
    refine ⟨47591201195687521825939847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126909869855166724869172925 47591201195687521825939847)
    ·
      refine ⟨71386801793531282738909771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47591201195687521825939847 71386801793531282738909771)
      ·
        refine ⟨107080202690296924108364657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71386801793531282738909771 107080202690296924108364657)
        ·
          refine ⟨80310152017722693081273493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107080202690296924108364657 80310152017722693081273493)
          ·
            refine ⟨3764538375830751238184695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 80310152017722693081273493 3764538375830751238184695)
            ·
              refine ⟨5646807563746126857277043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3764538375830751238184695 5646807563746126857277043)
              ·
                refine ⟨8470211345619190285915565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5646807563746126857277043 8470211345619190285915565)
                ·
                  refine ⟨3176329254607196357218337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8470211345619190285915565 3176329254607196357218337)
                  ·
                    refine ⟨2382246940955397267913753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3176329254607196357218337 2382246940955397267913753)
                    ·
                      refine ⟨1786685205716547950935315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2382246940955397267913753 1786685205716547950935315)
                      ·
                        rfl

theorem cell23_3479557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 3, 2, 2].length) (baseStart_3479557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479557 prefixEnd_3479557 := by exact prefixLift 3479557
  have htrace : WordTrace (prefixWord ++ tailWord_3479557) baseStart_3479557 baseEnd_3479557 := by
    simpa [prefixWord, tailWord_3479557, baseEnd_3479557] using wordTrace_append hprefix tailTrace_3479557
  have hstable : (prefixWord ++ tailWord_3479557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479557).length < 2 ^ (prefixWord ++ tailWord_3479557).sum := by decide
  have hdescent : baseEnd_3479557 < baseStart_3479557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479558 : List Nat := [6, 2, 1, 2, 2, 1, 2, 1, 6]
def baseStart_3479558 : Nat := 118140960795 + 3479558 * 2 ^ 59
def prefixEnd_3479558 : Nat := 4983230072969 + 3 ^ 40 * 3479558 * 2
def baseEnd_3479558 : Nat := 198520635466355827446979

theorem tailTrace_3479558 : CollatzResearch.WordTrace tailWord_3479558 prefixEnd_3479558 198520635466355827446979 := by
  unfold tailWord_3479558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3965934572755096938748729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84606604218775401359972885 3965934572755096938748729)
  ·
    refine ⟨2974450929566322704061547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3965934572755096938748729 2974450929566322704061547)
    ·
      refine ⟨4461676394349484056092321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2974450929566322704061547 4461676394349484056092321)
      ·
        refine ⟨3346257295762113042069241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4461676394349484056092321 3346257295762113042069241)
        ·
          refine ⟨2509692971821584781551931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3346257295762113042069241 2509692971821584781551931)
          ·
            refine ⟨3764539457732377172327897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2509692971821584781551931 3764539457732377172327897)
            ·
              refine ⟨2823404593299282879245923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3764539457732377172327897 2823404593299282879245923)
              ·
                refine ⟨4235106889948924318868885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2823404593299282879245923 4235106889948924318868885)
                ·
                  refine ⟨198520635466355827446979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4235106889948924318868885 198520635466355827446979)
                  ·
                    rfl

theorem cell23_3479558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_3479558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479558 prefixEnd_3479558 := by exact prefixLift 3479558
  have htrace : WordTrace (prefixWord ++ tailWord_3479558) baseStart_3479558 baseEnd_3479558 := by
    simpa [prefixWord, tailWord_3479558, baseEnd_3479558] using wordTrace_append hprefix tailTrace_3479558
  have hstable : (prefixWord ++ tailWord_3479558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479558).length < 2 ^ (prefixWord ++ tailWord_3479558).sum := by decide
  have hdescent : baseEnd_3479558 < baseStart_3479558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479566 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6]
def baseStart_3479566 : Nat := 118140960795 + 3479566 * 2 ^ 59
def prefixEnd_3479566 : Nat := 4983230072969 + 3 ^ 40 * 3479566 * 2
def baseEnd_3479566 : Nat := 1786689827042438415722773

theorem tailTrace_3479566 : CollatzResearch.WordTrace tailWord_3479566 prefixEnd_3479566 1786689827042438415722773 := by
  unfold tailWord_3479566
  simp only [CollatzResearch.WordTrace]
  refine ⟨15863774764016764925781319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84606798741422746270833701 15863774764016764925781319)
  ·
    refine ⟨23795662146025147388671979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15863774764016764925781319 23795662146025147388671979)
    ·
      refine ⟨35693493219037721083007969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23795662146025147388671979 35693493219037721083007969)
      ·
        refine ⟨26770119914278290812255977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35693493219037721083007969 26770119914278290812255977)
        ·
          refine ⟨20077589935708718109191983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26770119914278290812255977 20077589935708718109191983)
          ·
            refine ⟨30116384903563077163787975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20077589935708718109191983 30116384903563077163787975)
            ·
              refine ⟨45174577355344615745681963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30116384903563077163787975 45174577355344615745681963)
              ·
                refine ⟨67761866033016923618522945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45174577355344615745681963 67761866033016923618522945)
                ·
                  refine ⟨50821399524762692713892209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67761866033016923618522945 50821399524762692713892209)
                  ·
                    refine ⟨38116049643572019535419157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50821399524762692713892209 38116049643572019535419157)
                    ·
                      refine ⟨1786689827042438415722773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38116049643572019535419157 1786689827042438415722773)
                      ·
                        rfl

theorem cell23_3479566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_3479566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479566 prefixEnd_3479566 := by exact prefixLift 3479566
  have htrace : WordTrace (prefixWord ++ tailWord_3479566) baseStart_3479566 baseEnd_3479566 := by
    simpa [prefixWord, tailWord_3479566, baseEnd_3479566] using wordTrace_append hprefix tailTrace_3479566
  have hstable : (prefixWord ++ tailWord_3479566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479566).length < 2 ^ (prefixWord ++ tailWord_3479566).sum := by decide
  have hdescent : baseEnd_3479566 < baseStart_3479566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479608 : List Nat := [2, 1, 2, 1, 7, 1, 2, 2, 1, 2, 2]
def baseStart_3479608 : Nat := 118140960795 + 3479608 * 2 ^ 59
def prefixEnd_3479608 : Nat := 4983230072969 + 3 ^ 40 * 3479608 * 2
def baseEnd_3479608 : Nat := 1786711393229927251397581

theorem tailTrace_3479608 : CollatzResearch.WordTrace tailWord_3479608 prefixEnd_3479608 1786711393229927251397581 := by
  unfold tailWord_3479608
  simp only [CollatzResearch.WordTrace]
  refine ⟨63455864988990980289639739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84607819985321307052852985 63455864988990980289639739)
  ·
    refine ⟨95183797483486470434459609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63455864988990980289639739 95183797483486470434459609)
    ·
      refine ⟨71387848112614852825844707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95183797483486470434459609 71387848112614852825844707)
      ·
        refine ⟨107081772168922279238767061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71387848112614852825844707 107081772168922279238767061)
        ·
          refine ⟨2509729035209115919658603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 107081772168922279238767061 2509729035209115919658603)
          ·
            refine ⟨3764593552813673879487905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2509729035209115919658603 3764593552813673879487905)
            ·
              refine ⟨2823445164610255409615929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3764593552813673879487905 2823445164610255409615929)
              ·
                refine ⟨2117583873457691557211947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2823445164610255409615929 2117583873457691557211947)
                ·
                  refine ⟨3176375810186537335817921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2117583873457691557211947 3176375810186537335817921)
                  ·
                    refine ⟨2382281857639903001863441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3176375810186537335817921 2382281857639903001863441)
                    ·
                      refine ⟨1786711393229927251397581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2382281857639903001863441 1786711393229927251397581)
                      ·
                        rfl

theorem cell23_3479608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 2, 1, 2, 2].length) (baseStart_3479608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479608 prefixEnd_3479608 := by exact prefixLift 3479608
  have htrace : WordTrace (prefixWord ++ tailWord_3479608) baseStart_3479608 baseEnd_3479608 := by
    simpa [prefixWord, tailWord_3479608, baseEnd_3479608] using wordTrace_append hprefix tailTrace_3479608
  have hstable : (prefixWord ++ tailWord_3479608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479608).length < 2 ^ (prefixWord ++ tailWord_3479608).sum := by decide
  have hdescent : baseEnd_3479608 < baseStart_3479608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479630 : List Nat := [4, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2]
def baseStart_3479630 : Nat := 118140960795 + 3479630 * 2 ^ 59
def prefixEnd_3479630 : Nat := 4983230072969 + 3 ^ 40 * 3479630 * 2
def baseEnd_3479630 : Nat := 1786722689804326165322479

theorem tailTrace_3479630 : CollatzResearch.WordTrace tailWord_3479630 prefixEnd_3479630 1786722689804326165322479 := by
  unfold tailWord_3479630
  simp only [CollatzResearch.WordTrace]
  refine ⟨15864066547987782292072543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84608354922601505557720229 15864066547987782292072543)
  ·
    refine ⟨23796099821981673438108815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15864066547987782292072543 23796099821981673438108815)
    ·
      refine ⟨35694149732972510157163223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23796099821981673438108815 35694149732972510157163223)
      ·
        refine ⟨53541224599458765235744835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35694149732972510157163223 53541224599458765235744835)
        ·
          refine ⟨80311836899188147853617253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53541224599458765235744835 80311836899188147853617253)
          ·
            refine ⟨15058469418597777722553235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80311836899188147853617253 15058469418597777722553235)
            ·
              refine ⟨22587704127896666583829853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15058469418597777722553235 22587704127896666583829853)
              ·
                refine ⟨8470389047961249968936195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22587704127896666583829853 8470389047961249968936195)
                ·
                  refine ⟨12705583571941874953404293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8470389047961249968936195 12705583571941874953404293)
                  ·
                    refine ⟨2382296919739101553763305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12705583571941874953404293 2382296919739101553763305)
                    ·
                      refine ⟨1786722689804326165322479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2382296919739101553763305 1786722689804326165322479)
                      ·
                        rfl

theorem cell23_3479630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2].length) (baseStart_3479630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479630 prefixEnd_3479630 := by exact prefixLift 3479630
  have htrace : WordTrace (prefixWord ++ tailWord_3479630) baseStart_3479630 baseEnd_3479630 := by
    simpa [prefixWord, tailWord_3479630, baseEnd_3479630] using wordTrace_append hprefix tailTrace_3479630
  have hstable : (prefixWord ++ tailWord_3479630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479630).length < 2 ^ (prefixWord ++ tailWord_3479630).sum := by decide
  have hdescent : baseEnd_3479630 < baseStart_3479630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479663 : List Nat := [1, 1, 2, 1, 3, 4, 1, 2, 2, 3, 3]
def baseStart_3479663 : Nat := 118140960795 + 3479663 * 2 ^ 59
def prefixEnd_3479663 : Nat := 4983230072969 + 3 ^ 40 * 3479663 * 2
def baseEnd_3479663 : Nat := 1786739634665924536209827

theorem tailTrace_3479663 : CollatzResearch.WordTrace tailWord_3479663 prefixEnd_3479663 1786739634665924536209827 := by
  unfold tailWord_3479663
  simp only [CollatzResearch.WordTrace]
  refine ⟨126913735992782704972531643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84609157328521803315021095 126913735992782704972531643)
  ·
    refine ⟨190370603989174057458797465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126913735992782704972531643 190370603989174057458797465)
    ·
      refine ⟨142777952991880543094098099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190370603989174057458797465 142777952991880543094098099)
      ·
        refine ⟨214166929487820814641147149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142777952991880543094098099 214166929487820814641147149)
        ·
          refine ⟨80312598557932805490430181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214166929487820814641147149 80312598557932805490430181)
          ·
            refine ⟨15058612229612401029455659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80312598557932805490430181 15058612229612401029455659)
            ·
              refine ⟨22587918344418601544183489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15058612229612401029455659 22587918344418601544183489)
              ·
                refine ⟨16940938758313951158137617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22587918344418601544183489 16940938758313951158137617)
                ·
                  refine ⟨12705704068735463368603213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16940938758313951158137617 12705704068735463368603213)
                  ·
                    refine ⟨4764639025775798763226205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12705704068735463368603213 4764639025775798763226205)
                    ·
                      refine ⟨1786739634665924536209827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4764639025775798763226205 1786739634665924536209827)
                      ·
                        rfl

theorem cell23_3479663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 3, 3].length) (baseStart_3479663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479663 prefixEnd_3479663 := by exact prefixLift 3479663
  have htrace : WordTrace (prefixWord ++ tailWord_3479663) baseStart_3479663 baseEnd_3479663 := by
    simpa [prefixWord, tailWord_3479663, baseEnd_3479663] using wordTrace_append hprefix tailTrace_3479663
  have hstable : (prefixWord ++ tailWord_3479663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479663).length < 2 ^ (prefixWord ++ tailWord_3479663).sum := by decide
  have hdescent : baseEnd_3479663 < baseStart_3479663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479664 : List Nat := [2, 1, 1, 1, 5, 4, 1, 2, 2, 2, 2]
def baseStart_3479664 : Nat := 118140960795 + 3479664 * 2 ^ 59
def prefixEnd_3479664 : Nat := 4983230072969 + 3 ^ 40 * 3479664 * 2
def baseEnd_3479664 : Nat := 1786740148146579032297323

theorem tailTrace_3479664 : CollatzResearch.WordTrace tailWord_3479664 prefixEnd_3479664 1786740148146579032297323 := by
  unfold tailWord_3479664
  simp only [CollatzResearch.WordTrace]
  refine ⟨63456886232889541071659023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84609181643852721428878697 63456886232889541071659023)
  ·
    refine ⟨95185329349334311607488535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63456886232889541071659023 95185329349334311607488535)
    ·
      refine ⟨142777994024001467411232803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95185329349334311607488535 142777994024001467411232803)
      ·
        refine ⟨214166991036002201116849205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142777994024001467411232803 214166991036002201116849205)
        ·
          refine ⟨20078155409625206354704613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 214166991036002201116849205 20078155409625206354704613)
          ·
            refine ⟨3764654139304726191507115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20078155409625206354704613 3764654139304726191507115)
            ·
              refine ⟨5646981208957089287260673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3764654139304726191507115 5646981208957089287260673)
              ·
                refine ⟨4235235906717816965445505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5646981208957089287260673 4235235906717816965445505)
                ·
                  refine ⟨3176426930038362724084129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4235235906717816965445505 3176426930038362724084129)
                  ·
                    refine ⟨2382320197528772043063097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3176426930038362724084129 2382320197528772043063097)
                    ·
                      refine ⟨1786740148146579032297323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2382320197528772043063097 1786740148146579032297323)
                      ·
                        rfl

theorem cell23_3479664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 2, 2, 2].length) (baseStart_3479664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479664 prefixEnd_3479664 := by exact prefixLift 3479664
  have htrace : WordTrace (prefixWord ++ tailWord_3479664) baseStart_3479664 baseEnd_3479664 := by
    simpa [prefixWord, tailWord_3479664, baseEnd_3479664] using wordTrace_append hprefix tailTrace_3479664
  have hstable : (prefixWord ++ tailWord_3479664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479664).length < 2 ^ (prefixWord ++ tailWord_3479664).sum := by decide
  have hdescent : baseEnd_3479664 < baseStart_3479664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479670 : List Nat := [5, 1, 1, 2, 1, 3, 2, 1, 7]
def baseStart_3479670 : Nat := 118140960795 + 3479670 * 2 ^ 59
def prefixEnd_3479670 : Nat := 4983230072969 + 3 ^ 40 * 3479670 * 2
def baseEnd_3479670 : Nat := 198527025447834000980255

theorem tailTrace_3479670 : CollatzResearch.WordTrace tailWord_3479670 prefixEnd_3479670 198527025447834000980255 := by
  unfold tailWord_3479670
  simp only [CollatzResearch.WordTrace]
  refine ⟨7932124456484834073002279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84609327535838230112024309 7932124456484834073002279)
  ·
    refine ⟨11898186684727251109503419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7932124456484834073002279 11898186684727251109503419)
    ·
      refine ⟨17847280027090876664255129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11898186684727251109503419 17847280027090876664255129)
      ·
        refine ⟨13385460020318157498191347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17847280027090876664255129 13385460020318157498191347)
        ·
          refine ⟨20078190030477236247287021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13385460020318157498191347 20078190030477236247287021)
          ·
            refine ⟨7529321261428963592732633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20078190030477236247287021 7529321261428963592732633)
            ·
              refine ⟨5646990946071722694549475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7529321261428963592732633 5646990946071722694549475)
              ·
                refine ⟨8470486419107584041824213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5646990946071722694549475 8470486419107584041824213)
                ·
                  refine ⟨198527025447834000980255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8470486419107584041824213 198527025447834000980255)
                  ·
                    rfl

theorem cell23_3479670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_3479670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479670 prefixEnd_3479670 := by exact prefixLift 3479670
  have htrace : WordTrace (prefixWord ++ tailWord_3479670) baseStart_3479670 baseEnd_3479670 := by
    simpa [prefixWord, tailWord_3479670, baseEnd_3479670] using wordTrace_append hprefix tailTrace_3479670
  have hstable : (prefixWord ++ tailWord_3479670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479670).length < 2 ^ (prefixWord ++ tailWord_3479670).sum := by decide
  have hdescent : baseEnd_3479670 < baseStart_3479670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479681 : List Nat := [1, 2, 4, 2, 3, 1, 3, 1, 2, 2, 2]
def baseStart_3479681 : Nat := 118140960795 + 3479681 * 2 ^ 59
def prefixEnd_3479681 : Nat := 4983230072969 + 3 ^ 40 * 3479681 * 2
def baseEnd_3479681 : Nat := 1786748877317705465784745

theorem tailTrace_3479681 : CollatzResearch.WordTrace tailWord_3479681 prefixEnd_3479681 1786748877317705465784745 := by
  unfold tailWord_3479681
  simp only [CollatzResearch.WordTrace]
  refine ⟨126914392506717494046686897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84609595004478329364457931 126914392506717494046686897)
  ·
    refine ⟨95185794380038120535015173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126914392506717494046686897 95185794380038120535015173)
    ·
      refine ⟨17847336446257147600315345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95185794380038120535015173 17847336446257147600315345)
      ·
        refine ⟨13385502334692860700236509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17847336446257147600315345 13385502334692860700236509)
        ·
          refine ⟨5019563375509822762588691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13385502334692860700236509 5019563375509822762588691)
          ·
            refine ⟨7529345063264734143883037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5019563375509822762588691 7529345063264734143883037)
            ·
              refine ⟨2823504398724275303956139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7529345063264734143883037 2823504398724275303956139)
              ·
                refine ⟨4235256598086412955934209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2823504398724275303956139 4235256598086412955934209)
                ·
                  refine ⟨3176442448564809716950657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4235256598086412955934209 3176442448564809716950657)
                  ·
                    refine ⟨2382331836423607287712993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3176442448564809716950657 2382331836423607287712993)
                    ·
                      refine ⟨1786748877317705465784745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2382331836423607287712993 1786748877317705465784745)
                      ·
                        rfl

theorem cell23_3479681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_3479681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479681 prefixEnd_3479681 := by exact prefixLift 3479681
  have htrace : WordTrace (prefixWord ++ tailWord_3479681) baseStart_3479681 baseEnd_3479681 := by
    simpa [prefixWord, tailWord_3479681, baseEnd_3479681] using wordTrace_append hprefix tailTrace_3479681
  have hstable : (prefixWord ++ tailWord_3479681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479681).length < 2 ^ (prefixWord ++ tailWord_3479681).sum := by decide
  have hdescent : baseEnd_3479681 < baseStart_3479681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479696 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 2, 8]
def baseStart_3479696 : Nat := 118140960795 + 3479696 * 2 ^ 59
def prefixEnd_3479696 : Nat := 4983230072969 + 3 ^ 40 * 3479696 * 2
def baseEnd_3479696 : Nat := 595585526509174302365725

theorem tailTrace_3479696 : CollatzResearch.WordTrace tailWord_3479696 prefixEnd_3479696 595585526509174302365725 := by
  unfold tailWord_3479696
  simp only [CollatzResearch.WordTrace]
  refine ⟨63457469800831575804241471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84609959734442101072321961 63457469800831575804241471)
  ·
    refine ⟨95186204701247363706362207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63457469800831575804241471 95186204701247363706362207)
    ·
      refine ⟨142779307051871045559543311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95186204701247363706362207 142779307051871045559543311)
      ·
        refine ⟨214168960577806568339314967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142779307051871045559543311 214168960577806568339314967)
        ·
          refine ⟨321253440866709852508972451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214168960577806568339314967 321253440866709852508972451)
          ·
            refine ⟨481880161300064778763458677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321253440866709852508972451 481880161300064778763458677)
            ·
              refine ⟨45176265121881073009074251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 481880161300064778763458677 45176265121881073009074251)
              ·
                refine ⟨67764397682821609513611377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45176265121881073009074251 67764397682821609513611377)
                ·
                  refine ⟨50823298262116207135208533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67764397682821609513611377 50823298262116207135208533)
                  ·
                    refine ⟨595585526509174302365725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50823298262116207135208533 595585526509174302365725)
                    ·
                      rfl

theorem cell23_3479696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 2, 8].length) (baseStart_3479696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479696 prefixEnd_3479696 := by exact prefixLift 3479696
  have htrace : WordTrace (prefixWord ++ tailWord_3479696) baseStart_3479696 baseEnd_3479696 := by
    simpa [prefixWord, tailWord_3479696, baseEnd_3479696] using wordTrace_append hprefix tailTrace_3479696
  have hstable : (prefixWord ++ tailWord_3479696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479696).length < 2 ^ (prefixWord ++ tailWord_3479696).sum := by decide
  have hdescent : baseEnd_3479696 < baseStart_3479696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479704 : List Nat := [2, 1, 2, 4, 4, 1, 1, 3, 5]
def baseStart_3479704 : Nat := 118140960795 + 3479704 * 2 ^ 59
def prefixEnd_3479704 : Nat := 4983230072969 + 3 ^ 40 * 3479704 * 2
def baseEnd_3479704 : Nat := 198528965263639875088571

theorem tailTrace_3479704 : CollatzResearch.WordTrace tailWord_3479704 prefixEnd_3479704 198528965263639875088571 := by
  unfold tailWord_3479704
  simp only [CollatzResearch.WordTrace]
  refine ⟨63457615692817084487387083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84610154257089445983182777 63457615692817084487387083)
  ·
    refine ⟨95186423539225626731080625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63457615692817084487387083 95186423539225626731080625)
    ·
      refine ⟨71389817654419220048310469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95186423539225626731080625 71389817654419220048310469)
      ·
        refine ⟨13385590810203603759058213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71389817654419220048310469 13385590810203603759058213)
        ·
          refine ⟨2509798276913175704823415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13385590810203603759058213 2509798276913175704823415)
          ·
            refine ⟨3764697415369763557235123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2509798276913175704823415 3764697415369763557235123)
            ·
              refine ⟨5647046123054645335852685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3764697415369763557235123 5647046123054645335852685)
              ·
                refine ⟨2117642296145492000944757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5647046123054645335852685 2117642296145492000944757)
                ·
                  refine ⟨198528965263639875088571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2117642296145492000944757 198528965263639875088571)
                  ·
                    rfl

theorem cell23_3479704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 3, 5].length) (baseStart_3479704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479704 prefixEnd_3479704 := by exact prefixLift 3479704
  have htrace : WordTrace (prefixWord ++ tailWord_3479704) baseStart_3479704 baseEnd_3479704 := by
    simpa [prefixWord, tailWord_3479704, baseEnd_3479704] using wordTrace_append hprefix tailTrace_3479704
  have hstable : (prefixWord ++ tailWord_3479704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479704).length < 2 ^ (prefixWord ++ tailWord_3479704).sum := by decide
  have hdescent : baseEnd_3479704 < baseStart_3479704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479732 : List Nat := [2, 5, 3, 1, 1, 2, 2, 1, 2, 2, 2]
def baseStart_3479732 : Nat := 118140960795 + 3479732 * 2 ^ 59
def prefixEnd_3479732 : Nat := 4983230072969 + 3 ^ 40 * 3479732 * 2
def baseEnd_3479732 : Nat := 1786775064831084766247011

theorem tailTrace_3479732 : CollatzResearch.WordTrace tailWord_3479732 prefixEnd_3479732 1786775064831084766247011 := by
  unfold tailWord_3479732
  simp only [CollatzResearch.WordTrace]
  refine ⟨63458126314766364878396725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84610835086355153171195633 63458126314766364878396725)
  ·
    refine ⟨5949199342009346707349693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63458126314766364878396725 5949199342009346707349693)
    ·
      refine ⟨2230949753253505015256135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5949199342009346707349693 2230949753253505015256135)
      ·
        refine ⟨3346424629880257522884203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2230949753253505015256135 3346424629880257522884203)
        ·
          refine ⟨5019636944820386284326305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3346424629880257522884203 5019636944820386284326305)
          ·
            refine ⟨3764727708615289713244729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5019636944820386284326305 3764727708615289713244729)
            ·
              refine ⟨2823545781461467284933547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3764727708615289713244729 2823545781461467284933547)
              ·
                refine ⟨4235318672192200927400321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2823545781461467284933547 4235318672192200927400321)
                ·
                  refine ⟨3176489004144150695550241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4235318672192200927400321 3176489004144150695550241)
                  ·
                    refine ⟨2382366753108113021662681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3176489004144150695550241 2382366753108113021662681)
                    ·
                      refine ⟨1786775064831084766247011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2382366753108113021662681 1786775064831084766247011)
                      ·
                        rfl

theorem cell23_3479732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_3479732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479732 prefixEnd_3479732 := by exact prefixLift 3479732
  have htrace : WordTrace (prefixWord ++ tailWord_3479732) baseStart_3479732 baseEnd_3479732 := by
    simpa [prefixWord, tailWord_3479732, baseEnd_3479732] using wordTrace_append hprefix tailTrace_3479732
  have hstable : (prefixWord ++ tailWord_3479732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479732).length < 2 ^ (prefixWord ++ tailWord_3479732).sum := by decide
  have hdescent : baseEnd_3479732 < baseStart_3479732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479780 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 3, 5, 2]
def baseStart_3479780 : Nat := 118140960795 + 3479780 * 2 ^ 59
def prefixEnd_3479780 : Nat := 4983230072969 + 3 ^ 40 * 3479780 * 2
def baseEnd_3479780 : Nat := 1786799711902500578446789

theorem tailTrace_3479780 : CollatzResearch.WordTrace tailWord_3479780 prefixEnd_3479780 1786799711902500578446789 := by
  unfold tailWord_3479780
  simp only [CollatzResearch.WordTrace]
  refine ⟨63459001666679416977270397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84612002222239222636360529 63459001666679416977270397)
  ·
    refine ⟨23797125625004781366476399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63459001666679416977270397 23797125625004781366476399)
    ·
      refine ⟨35695688437507172049714599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23797125625004781366476399 35695688437507172049714599)
      ·
        refine ⟨53543532656260758074571899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35695688437507172049714599 53543532656260758074571899)
        ·
          refine ⟨80315298984391137111857849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53543532656260758074571899 80315298984391137111857849)
          ·
            refine ⟨60236474238293352833893387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80315298984391137111857849 60236474238293352833893387)
            ·
              refine ⟨90354711357440029250840081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60236474238293352833893387 90354711357440029250840081)
              ·
                refine ⟨67766033518080021938130061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90354711357440029250840081 67766033518080021938130061)
                ·
                  refine ⟨25412262569280008226798773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67766033518080021938130061 25412262569280008226798773)
                  ·
                    refine ⟨2382399615870000771262385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25412262569280008226798773 2382399615870000771262385)
                    ·
                      refine ⟨1786799711902500578446789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2382399615870000771262385 1786799711902500578446789)
                      ·
                        rfl

theorem cell23_3479780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 3, 5, 2].length) (baseStart_3479780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479780 prefixEnd_3479780 := by exact prefixLift 3479780
  have htrace : WordTrace (prefixWord ++ tailWord_3479780) baseStart_3479780 baseEnd_3479780 := by
    simpa [prefixWord, tailWord_3479780, baseEnd_3479780] using wordTrace_append hprefix tailTrace_3479780
  have hstable : (prefixWord ++ tailWord_3479780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479780).length < 2 ^ (prefixWord ++ tailWord_3479780).sum := by decide
  have hdescent : baseEnd_3479780 < baseStart_3479780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479781 : List Nat := [1, 3, 1, 4, 2, 3, 2, 2, 1, 4]
def baseStart_3479781 : Nat := 118140960795 + 3479781 * 2 ^ 59
def prefixEnd_3479781 : Nat := 4983230072969 + 3 ^ 40 * 3479781 * 2
def baseEnd_3479781 : Nat := 595600075127718358178095

theorem tailTrace_3479781 : CollatzResearch.WordTrace tailWord_3479781 prefixEnd_3479781 595600075127718358178095 := by
  unfold tailWord_3479781
  simp only [CollatzResearch.WordTrace]
  refine ⟨126918039806355211125327197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84612026537570140750218131 126918039806355211125327197)
  ·
    refine ⟨47594264927383204171997699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126918039806355211125327197 47594264927383204171997699)
    ·
      refine ⟨71391397391074806257996549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47594264927383204171997699 71391397391074806257996549)
      ·
        refine ⟨13385887010826526173374353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71391397391074806257996549 13385887010826526173374353)
        ·
          refine ⟨10039415258119894630030765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13385887010826526173374353 10039415258119894630030765)
          ·
            refine ⟨3764780721794960486261537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10039415258119894630030765 3764780721794960486261537)
            ·
              refine ⟨2823585541346220364696153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3764780721794960486261537 2823585541346220364696153)
              ·
                refine ⟨2117689156009665273522115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2823585541346220364696153 2117689156009665273522115)
                ·
                  refine ⟨3176533734014497910283173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2117689156009665273522115 3176533734014497910283173)
                  ·
                    refine ⟨595600075127718358178095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3176533734014497910283173 595600075127718358178095)
                    ·
                      rfl

theorem cell23_3479781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 2, 1, 4].length) (baseStart_3479781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479781 prefixEnd_3479781 := by exact prefixLift 3479781
  have htrace : WordTrace (prefixWord ++ tailWord_3479781) baseStart_3479781 baseEnd_3479781 := by
    simpa [prefixWord, tailWord_3479781, baseEnd_3479781] using wordTrace_append hprefix tailTrace_3479781
  have hstable : (prefixWord ++ tailWord_3479781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479781).length < 2 ^ (prefixWord ++ tailWord_3479781).sum := by decide
  have hdescent : baseEnd_3479781 < baseStart_3479781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479813 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 5, 1, 5]
def baseStart_3479813 : Nat := 118140960795 + 3479813 * 2 ^ 59
def prefixEnd_3479813 : Nat := 4983230072969 + 3 ^ 40 * 3479813 * 2
def baseEnd_3479813 : Nat := 1786816656764098949334137

theorem tailTrace_3479813 : CollatzResearch.WordTrace tailWord_3479813 prefixEnd_3479813 1786816656764098949334137 := by
  unfold tailWord_3479813
  simp only [CollatzResearch.WordTrace]
  refine ⟨126919206942239280590492093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84612804628159520393661395 126919206942239280590492093)
  ·
    refine ⟨47594702603339730221434535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126919206942239280590492093 47594702603339730221434535)
    ·
      refine ⟨71392053905009595332151803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47594702603339730221434535 71392053905009595332151803)
      ·
        refine ⟨107088080857514392998227705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71392053905009595332151803 107088080857514392998227705)
        ·
          refine ⟨80316060643135794748670779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107088080857514392998227705 80316060643135794748670779)
          ·
            refine ⟨120474090964703692123006169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80316060643135794748670779 120474090964703692123006169)
            ·
              refine ⟨90355568223527769092254627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120474090964703692123006169 90355568223527769092254627)
              ·
                refine ⟨135533352335291653638381941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90355568223527769092254627 135533352335291653638381941)
                ·
                  refine ⟨12706251781433592528598307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135533352335291653638381941 12706251781433592528598307)
                  ·
                    refine ⟨19059377672150388792897461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12706251781433592528598307 19059377672150388792897461)
                    ·
                      refine ⟨1786816656764098949334137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19059377672150388792897461 1786816656764098949334137)
                      ·
                        rfl

theorem cell23_3479813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_3479813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479813 prefixEnd_3479813 := by exact prefixLift 3479813
  have htrace : WordTrace (prefixWord ++ tailWord_3479813) baseStart_3479813 baseEnd_3479813 := by
    simpa [prefixWord, tailWord_3479813, baseEnd_3479813] using wordTrace_append hprefix tailTrace_3479813
  have hstable : (prefixWord ++ tailWord_3479813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479813).length < 2 ^ (prefixWord ++ tailWord_3479813).sum := by decide
  have hdescent : baseEnd_3479813 < baseStart_3479813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479820 : List Nat := [2, 2, 1, 2, 2, 2, 2, 2, 4, 4]
def baseStart_3479820 : Nat := 118140960795 + 3479820 * 2 ^ 59
def prefixEnd_3479820 : Nat := 4983230072969 + 3 ^ 40 * 3479820 * 2
def baseEnd_3479820 : Nat := 595606750376226807315535

theorem tailTrace_3479820 : CollatzResearch.WordTrace tailWord_3479820 prefixEnd_3479820 595606750376226807315535 := by
  unfold tailWord_3479820
  simp only [CollatzResearch.WordTrace]
  refine ⟨63459731126606960392998457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84612974835475947190664609 63459731126606960392998457)
  ·
    refine ⟨47594798344955220294748843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63459731126606960392998457 47594798344955220294748843)
    ·
      refine ⟨71392197517432830442123265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47594798344955220294748843 71392197517432830442123265)
      ·
        refine ⟨53544148138074622831592449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71392197517432830442123265 53544148138074622831592449)
        ·
          refine ⟨40158111103555967123694337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53544148138074622831592449 40158111103555967123694337)
          ·
            refine ⟨30118583327666975342770753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40158111103555967123694337 30118583327666975342770753)
            ·
              refine ⟨22588937495750231507078065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30118583327666975342770753 22588937495750231507078065)
              ·
                refine ⟨16941703121812673630308549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22588937495750231507078065 16941703121812673630308549)
                ·
                  refine ⟨3176569335339876305682853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16941703121812673630308549 3176569335339876305682853)
                  ·
                    refine ⟨595606750376226807315535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3176569335339876305682853 595606750376226807315535)
                    ·
                      rfl

theorem cell23_3479820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 4, 4].length) (baseStart_3479820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479820 prefixEnd_3479820 := by exact prefixLift 3479820
  have htrace : WordTrace (prefixWord ++ tailWord_3479820) baseStart_3479820 baseEnd_3479820 := by
    simpa [prefixWord, tailWord_3479820, baseEnd_3479820] using wordTrace_append hprefix tailTrace_3479820
  have hstable : (prefixWord ++ tailWord_3479820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479820).length < 2 ^ (prefixWord ++ tailWord_3479820).sum := by decide
  have hdescent : baseEnd_3479820 < baseStart_3479820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479838 : List Nat := [4, 3, 2, 1, 1, 1, 2, 4, 1, 1, 3]
def baseStart_3479838 : Nat := 118140960795 + 3479838 * 2 ^ 59
def prefixEnd_3479838 : Nat := 4983230072969 + 3 ^ 40 * 3479838 * 2
def baseEnd_3479838 : Nat := 1786829493780461351521523

theorem tailTrace_3479838 : CollatzResearch.WordTrace tailWord_3479838 prefixEnd_3479838 1786829493780461351521523 := by
  unfold tailWord_3479838
  simp only [CollatzResearch.WordTrace]
  refine ⟨15865014845893588732519021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84613412511432473240101445 15865014845893588732519021)
  ·
    refine ⟨5949380567210095774694633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15865014845893588732519021 5949380567210095774694633)
    ·
      refine ⟨4462035425407571831020975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5949380567210095774694633 4462035425407571831020975)
      ·
        refine ⟨6693053138111357746531463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4462035425407571831020975 6693053138111357746531463)
        ·
          refine ⟨10039579707167036619797195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6693053138111357746531463 10039579707167036619797195)
          ·
            refine ⟨15059369560750554929695793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10039579707167036619797195 15059369560750554929695793)
            ·
              refine ⟨11294527170562916197271845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15059369560750554929695793 11294527170562916197271845)
              ·
                refine ⟨2117723844480546786988471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11294527170562916197271845 2117723844480546786988471)
                ·
                  refine ⟨3176585766720820180482707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2117723844480546786988471 3176585766720820180482707)
                  ·
                    refine ⟨4764878650081230270724061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3176585766720820180482707 4764878650081230270724061)
                    ·
                      refine ⟨1786829493780461351521523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4764878650081230270724061 1786829493780461351521523)
                      ·
                        rfl

theorem cell23_3479838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_3479838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479838 prefixEnd_3479838 := by exact prefixLift 3479838
  have htrace : WordTrace (prefixWord ++ tailWord_3479838) baseStart_3479838 baseEnd_3479838 := by
    simpa [prefixWord, tailWord_3479838, baseEnd_3479838] using wordTrace_append hprefix tailTrace_3479838
  have hstable : (prefixWord ++ tailWord_3479838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479838).length < 2 ^ (prefixWord ++ tailWord_3479838).sum := by decide
  have hdescent : baseEnd_3479838 < baseStart_3479838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479844 : List Nat := [2, 3, 1, 3, 1, 2, 1, 3, 3, 2, 2]
def baseStart_3479844 : Nat := 118140960795 + 3479844 * 2 ^ 59
def prefixEnd_3479844 : Nat := 4983230072969 + 3 ^ 40 * 3479844 * 2
def baseEnd_3479844 : Nat := 1786832574664388328046495

theorem tailTrace_3479844 : CollatzResearch.WordTrace tailWord_3479844 prefixEnd_3479844 1786832574664388328046495 := by
  unfold tailWord_3479844
  simp only [CollatzResearch.WordTrace]
  refine ⟨63460168802563486442435293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84613558403417981923247057 63460168802563486442435293)
  ·
    refine ⟨23797563300961307415913235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63460168802563486442435293 23797563300961307415913235)
    ·
      refine ⟨35696344951441961123869853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23797563300961307415913235 35696344951441961123869853)
      ·
        refine ⟨13386129356790735421451195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35696344951441961123869853 13386129356790735421451195)
        ·
          refine ⟨20079194035186103132176793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13386129356790735421451195 20079194035186103132176793)
          ·
            refine ⟨15059395526389577349132595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20079194035186103132176793 15059395526389577349132595)
            ·
              refine ⟨22589093289584366023698893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15059395526389577349132595 22589093289584366023698893)
              ·
                refine ⟨8470909983594137258887085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22589093289584366023698893 8470909983594137258887085)
                ·
                  refine ⟨3176591243847801472082657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8470909983594137258887085 3176591243847801472082657)
                  ·
                    refine ⟨2382443432885851104061993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3176591243847801472082657 2382443432885851104061993)
                    ·
                      refine ⟨1786832574664388328046495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2382443432885851104061993 1786832574664388328046495)
                      ·
                        rfl

theorem cell23_3479844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_3479844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479844 prefixEnd_3479844 := by exact prefixLift 3479844
  have htrace : WordTrace (prefixWord ++ tailWord_3479844) baseStart_3479844 baseEnd_3479844 := by
    simpa [prefixWord, tailWord_3479844, baseEnd_3479844] using wordTrace_append hprefix tailTrace_3479844
  have hstable : (prefixWord ++ tailWord_3479844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479844).length < 2 ^ (prefixWord ++ tailWord_3479844).sum := by decide
  have hdescent : baseEnd_3479844 < baseStart_3479844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479863 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 2, 7]
def baseStart_3479863 : Nat := 118140960795 + 3479863 * 2 ^ 59
def prefixEnd_3479863 : Nat := 4983230072969 + 3 ^ 40 * 3479863 * 2
def baseEnd_3479863 : Nat := 595614110265607917902969

theorem tailTrace_3479863 : CollatzResearch.WordTrace tailWord_3479863 prefixEnd_3479863 595614110265607917902969 := by
  unfold tailWord_3479863
  simp only [CollatzResearch.WordTrace]
  refine ⟨126921030592058139129812243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84614020394705426086541495 126921030592058139129812243)
  ·
    refine ⟨190381545888087208694718365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126921030592058139129812243 190381545888087208694718365)
    ·
      refine ⟨71393079708032703260519387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190381545888087208694718365 71393079708032703260519387)
      ·
        refine ⟨107089619562049054890779081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71393079708032703260519387 107089619562049054890779081)
        ·
          refine ⟨80317214671536791168084311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107089619562049054890779081 80317214671536791168084311)
          ·
            refine ⟨120475822007305186752126467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80317214671536791168084311 120475822007305186752126467)
            ·
              refine ⟨180713733010957780128189701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120475822007305186752126467 180713733010957780128189701)
              ·
                refine ⟨33883824939554583774035569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180713733010957780128189701 33883824939554583774035569)
                ·
                  refine ⟨25412868704665937830526677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33883824939554583774035569 25412868704665937830526677)
                  ·
                    refine ⟨595614110265607917902969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25412868704665937830526677 595614110265607917902969)
                    ·
                      rfl

theorem cell23_3479863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 7].length) (baseStart_3479863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479863 prefixEnd_3479863 := by exact prefixLift 3479863
  have htrace : WordTrace (prefixWord ++ tailWord_3479863) baseStart_3479863 baseEnd_3479863 := by
    simpa [prefixWord, tailWord_3479863, baseEnd_3479863] using wordTrace_append hprefix tailTrace_3479863
  have hstable : (prefixWord ++ tailWord_3479863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479863).length < 2 ^ (prefixWord ++ tailWord_3479863).sum := by decide
  have hdescent : baseEnd_3479863 < baseStart_3479863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479911 : List Nat := [1, 1, 5, 1, 3, 1, 4, 1, 2, 1, 3]
def baseStart_3479911 : Nat := 118140960795 + 3479911 * 2 ^ 59
def prefixEnd_3479911 : Nat := 4983230072969 + 3 ^ 40 * 3479911 * 2
def baseEnd_3479911 : Nat := 1786866977868239565908687

theorem tailTrace_3479911 : CollatzResearch.WordTrace tailWord_3479911 prefixEnd_3479911 1786866977868239565908687 := by
  unfold tailWord_3479911
  simp only [CollatzResearch.WordTrace]
  refine ⟨126922781295884243327559587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84615187530589495551706391 126922781295884243327559587)
  ·
    refine ⟨190384171943826364991339381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126922781295884243327559587 190384171943826364991339381)
    ·
      refine ⟨17848516119733721717938067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 190384171943826364991339381 17848516119733721717938067)
      ·
        refine ⟨26772774179600582576907101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17848516119733721717938067 26772774179600582576907101)
        ·
          refine ⟨10039790317350218466340163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26772774179600582576907101 10039790317350218466340163)
          ·
            refine ⟨15059685476025327699510245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10039790317350218466340163 15059685476025327699510245)
            ·
              refine ⟨2823691026754748943658171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15059685476025327699510245 2823691026754748943658171)
              ·
                refine ⟨4235536540132123415487257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2823691026754748943658171 4235536540132123415487257)
                ·
                  refine ⟨3176652405099092561615443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4235536540132123415487257 3176652405099092561615443)
                  ·
                    refine ⟨4764978607648638842423165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3176652405099092561615443 4764978607648638842423165)
                    ·
                      refine ⟨1786866977868239565908687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4764978607648638842423165 1786866977868239565908687)
                      ·
                        rfl

theorem cell23_3479911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_3479911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479911 prefixEnd_3479911 := by exact prefixLift 3479911
  have htrace : WordTrace (prefixWord ++ tailWord_3479911) baseStart_3479911 baseEnd_3479911 := by
    simpa [prefixWord, tailWord_3479911, baseEnd_3479911] using wordTrace_append hprefix tailTrace_3479911
  have hstable : (prefixWord ++ tailWord_3479911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479911).length < 2 ^ (prefixWord ++ tailWord_3479911).sum := by decide
  have hdescent : baseEnd_3479911 < baseStart_3479911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479920 : List Nat := [2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 5]
def baseStart_3479920 : Nat := 118140960795 + 3479920 * 2 ^ 59
def prefixEnd_3479920 : Nat := 4983230072969 + 3 ^ 40 * 3479920 * 2
def baseEnd_3479920 : Nat := 1786871599194130030696145

theorem tailTrace_3479920 : CollatzResearch.WordTrace tailWord_3479920 prefixEnd_3479920 1786871599194130030696145 := by
  unfold tailWord_3479920
  simp only [CollatzResearch.WordTrace]
  refine ⟨63461554776425818932318607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84615406368567758576424809 63461554776425818932318607)
  ·
    refine ⟨95192332164638728398477911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63461554776425818932318607 95192332164638728398477911)
    ·
      refine ⟨142788498246958092597716867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95192332164638728398477911 142788498246958092597716867)
      ·
        refine ⟨214182747370437138896575301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142788498246958092597716867 214182747370437138896575301)
        ·
          refine ⟨40159265131956963543107869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214182747370437138896575301 40159265131956963543107869)
          ·
            refine ⟨15059724424483861328665451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40159265131956963543107869 15059724424483861328665451)
            ·
              refine ⟨22589586636725791992998177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15059724424483861328665451 22589586636725791992998177)
              ·
                refine ⟨16942189977544343994748633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22589586636725791992998177 16942189977544343994748633)
                ·
                  refine ⟨12706642483158257996061475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16942189977544343994748633 12706642483158257996061475)
                  ·
                    refine ⟨19059963724737386994092213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12706642483158257996061475 19059963724737386994092213)
                    ·
                      refine ⟨1786871599194130030696145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19059963724737386994092213 1786871599194130030696145)
                      ·
                        rfl

theorem cell23_3479920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 5].length) (baseStart_3479920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479920 prefixEnd_3479920 := by exact prefixLift 3479920
  have htrace : WordTrace (prefixWord ++ tailWord_3479920) baseStart_3479920 baseEnd_3479920 := by
    simpa [prefixWord, tailWord_3479920, baseEnd_3479920] using wordTrace_append hprefix tailTrace_3479920
  have hstable : (prefixWord ++ tailWord_3479920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479920).length < 2 ^ (prefixWord ++ tailWord_3479920).sum := by decide
  have hdescent : baseEnd_3479920 < baseStart_3479920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479937 : List Nat := [1, 2, 4, 3, 1, 1, 2, 1, 2, 1, 5]
def baseStart_3479937 : Nat := 118140960795 + 3479937 * 2 ^ 59
def prefixEnd_3479937 : Nat := 4983230072969 + 3 ^ 40 * 3479937 * 2
def baseEnd_3479937 : Nat := 1786880328365256464183567

theorem tailTrace_3479937 : CollatzResearch.WordTrace tailWord_3479937 prefixEnd_3479937 1786880328365256464183567 := by
  unfold tailWord_3479937
  simp only [CollatzResearch.WordTrace]
  refine ⟨126923729593790049768006065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84615819729193366512004043 126923729593790049768006065)
  ·
    refine ⟨95192797195342537326004549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126923729593790049768006065 95192797195342537326004549)
    ·
      refine ⟨17848649474126725748625853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95192797195342537326004549 17848649474126725748625853)
      ·
        refine ⟨6693243552797522155734695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17848649474126725748625853 6693243552797522155734695)
        ·
          refine ⟨10039865329196283233602043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6693243552797522155734695 10039865329196283233602043)
          ·
            refine ⟨15059797993794424850403065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10039865329196283233602043 15059797993794424850403065)
            ·
              refine ⟨11294848495345818637802299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15059797993794424850403065 11294848495345818637802299)
              ·
                refine ⟨16942272743018727956703449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11294848495345818637802299 16942272743018727956703449)
                ·
                  refine ⟨12706704557264045967527587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16942272743018727956703449 12706704557264045967527587)
                  ·
                    refine ⟨19060056835896068951291381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12706704557264045967527587 19060056835896068951291381)
                    ·
                      refine ⟨1786880328365256464183567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19060056835896068951291381 1786880328365256464183567)
                      ·
                        rfl

theorem cell23_3479937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_3479937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479937 prefixEnd_3479937 := by exact prefixLift 3479937
  have htrace : WordTrace (prefixWord ++ tailWord_3479937) baseStart_3479937 baseEnd_3479937 := by
    simpa [prefixWord, tailWord_3479937, baseEnd_3479937] using wordTrace_append hprefix tailTrace_3479937
  have hstable : (prefixWord ++ tailWord_3479937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479937).length < 2 ^ (prefixWord ++ tailWord_3479937).sum := by decide
  have hdescent : baseEnd_3479937 < baseStart_3479937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479967 : List Nat := [1, 1, 2, 5, 1, 1, 3, 1, 2, 3, 3]
def baseStart_3479967 : Nat := 118140960795 + 3479967 * 2 ^ 59
def prefixEnd_3479967 : Nat := 4983230072969 + 3 ^ 40 * 3479967 * 2
def baseEnd_3479967 : Nat := 1786895732784891346808429

theorem tailTrace_3479967 : CollatzResearch.WordTrace tailWord_3479967 prefixEnd_3479967 1786895732784891346808429 := by
  unfold tailWord_3479967
  simp only [CollatzResearch.WordTrace]
  refine ⟨126924823783681364891598155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84616549189120909927732103 126924823783681364891598155)
  ·
    refine ⟨190387235675522047337397233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126924823783681364891598155 190387235675522047337397233)
    ·
      refine ⟨142790426756641535503047925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190387235675522047337397233 142790426756641535503047925)
      ·
        refine ⟨13386602508435143953410743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142790426756641535503047925 13386602508435143953410743)
        ·
          refine ⟨20079903762652715930116115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13386602508435143953410743 20079903762652715930116115)
          ·
            refine ⟨30119855643979073895174173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20079903762652715930116115 30119855643979073895174173)
            ·
              refine ⟨11294945866492152710690315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30119855643979073895174173 11294945866492152710690315)
              ·
                refine ⟨16942418799738229066035473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11294945866492152710690315 16942418799738229066035473)
                ·
                  refine ⟨12706814099803671799526605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16942418799738229066035473 12706814099803671799526605)
                  ·
                    refine ⟨4765055287426376924822477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12706814099803671799526605 4765055287426376924822477)
                    ·
                      refine ⟨1786895732784891346808429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4765055287426376924822477 1786895732784891346808429)
                      ·
                        rfl

theorem cell23_3479967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_3479967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3479967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3479967 prefixEnd_3479967 := by exact prefixLift 3479967
  have htrace : WordTrace (prefixWord ++ tailWord_3479967) baseStart_3479967 baseEnd_3479967 := by
    simpa [prefixWord, tailWord_3479967, baseEnd_3479967] using wordTrace_append hprefix tailTrace_3479967
  have hstable : (prefixWord ++ tailWord_3479967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479967).length < 2 ^ (prefixWord ++ tailWord_3479967).sum := by decide
  have hdescent : baseEnd_3479967 < baseStart_3479967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480107 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 6, 4]
def baseStart_3480107 : Nat := 118140960795 + 3480107 * 2 ^ 59
def prefixEnd_3480107 : Nat := 4983230072969 + 3 ^ 40 * 3480107 * 2
def baseEnd_3480107 : Nat := 595655873358840266352595

theorem tailTrace_3480107 : CollatzResearch.WordTrace tailWord_3480107 prefixEnd_3480107 595655873358840266352595 := by
  unfold tailWord_3480107
  simp only [CollatzResearch.WordTrace]
  refine ⟨126929930003174168801694575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84619953335449445867796383 126929930003174168801694575)
  ·
    refine ⟨190394895004761253202541863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126929930003174168801694575 190394895004761253202541863)
    ·
      refine ⟨285592342507141879803812795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190394895004761253202541863 285592342507141879803812795)
      ·
        refine ⟨428388513760712819705719193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285592342507141879803812795 428388513760712819705719193)
        ·
          refine ⟨321291385320534614779289395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428388513760712819705719193 321291385320534614779289395)
          ·
            refine ⟨481937077980801922168934093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321291385320534614779289395 481937077980801922168934093)
            ·
              refine ⟨180726404242800720813350285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 481937077980801922168934093 180726404242800720813350285)
              ·
                refine ⟨67772401591050270305006357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180726404242800720813350285 67772401591050270305006357)
                ·
                  refine ⟨3176831324580481420547173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67772401591050270305006357 3176831324580481420547173)
                  ·
                    refine ⟨595655873358840266352595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3176831324580481420547173 595655873358840266352595)
                    ·
                      rfl

theorem cell23_3480107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 6, 4].length) (baseStart_3480107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480107 prefixEnd_3480107 := by exact prefixLift 3480107
  have htrace : WordTrace (prefixWord ++ tailWord_3480107) baseStart_3480107 baseEnd_3480107 := by
    simpa [prefixWord, tailWord_3480107, baseEnd_3480107] using wordTrace_append hprefix tailTrace_3480107
  have hstable : (prefixWord ++ tailWord_3480107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480107).length < 2 ^ (prefixWord ++ tailWord_3480107).sum := by decide
  have hdescent : baseEnd_3480107 < baseStart_3480107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480114 : List Nat := [3, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4]
def baseStart_3480114 : Nat := 118140960795 + 3480114 * 2 ^ 59
def prefixEnd_3480114 : Nat := 4983230072969 + 3 ^ 40 * 3480114 * 2
def baseEnd_3480114 : Nat := 1786971214441102271670253

theorem tailTrace_3480114 : CollatzResearch.WordTrace tailWord_3480114 prefixEnd_3480114 1786971214441102271670253 := by
  unfold tailWord_3480114
  simp only [CollatzResearch.WordTrace]
  refine ⟨31732546328537202249299849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84620123542765872664799597 31732546328537202249299849)
  ·
    refine ⟨23799409746402901686974887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31732546328537202249299849 23799409746402901686974887)
    ·
      refine ⟨35699114619604352530462331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23799409746402901686974887 35699114619604352530462331)
      ·
        refine ⟨53548671929406528795693497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35699114619604352530462331 53548671929406528795693497)
        ·
          refine ⟨40161503947054896596770123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53548671929406528795693497 40161503947054896596770123)
          ·
            refine ⟨60242255920582344895155185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40161503947054896596770123 60242255920582344895155185)
            ·
              refine ⟨45181691940436758671366389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60242255920582344895155185 45181691940436758671366389)
              ·
                refine ⟨4235783619415946125440599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45181691940436758671366389 4235783619415946125440599)
                ·
                  refine ⟨6353675429123919188160899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4235783619415946125440599 6353675429123919188160899)
                  ·
                    refine ⟨9530513143685878782241349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6353675429123919188160899 9530513143685878782241349)
                    ·
                      refine ⟨1786971214441102271670253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9530513143685878782241349 1786971214441102271670253)
                      ·
                        rfl

theorem cell23_3480114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_3480114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480114 prefixEnd_3480114 := by exact prefixLift 3480114
  have htrace : WordTrace (prefixWord ++ tailWord_3480114) baseStart_3480114 baseEnd_3480114 := by
    simpa [prefixWord, tailWord_3480114, baseEnd_3480114] using wordTrace_append hprefix tailTrace_3480114
  have hstable : (prefixWord ++ tailWord_3480114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480114).length < 2 ^ (prefixWord ++ tailWord_3480114).sum := by decide
  have hdescent : baseEnd_3480114 < baseStart_3480114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480118 : List Nat := [5, 1, 2, 1, 2, 1, 2, 2, 2, 3, 2]
def baseStart_3480118 : Nat := 118140960795 + 3480118 * 2 ^ 59
def prefixEnd_3480118 : Nat := 4983230072969 + 3 ^ 40 * 3480118 * 2
def baseEnd_3480118 : Nat := 1786973268363720256020235

theorem tailTrace_3480118 : CollatzResearch.WordTrace tailWord_3480118 prefixEnd_3480118 1786973268363720256020235 := by
  unfold tailWord_3480118
  simp only [CollatzResearch.WordTrace]
  refine ⟨7933145700383394855021563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84620220804089545120230005 7933145700383394855021563)
  ·
    refine ⟨11899718550575092282532345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7933145700383394855021563 11899718550575092282532345)
    ·
      refine ⟨8924788912931319211899259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11899718550575092282532345 8924788912931319211899259)
      ·
        refine ⟨13387183369396978817848889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8924788912931319211899259 13387183369396978817848889)
        ·
          refine ⟨10040387527047734113386667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13387183369396978817848889 10040387527047734113386667)
          ·
            refine ⟨15060581290571601170080001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10040387527047734113386667 15060581290571601170080001)
            ·
              refine ⟨11295435967928700877560001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15060581290571601170080001 11295435967928700877560001)
              ·
                refine ⟨8471576975946525658170001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11295435967928700877560001 8471576975946525658170001)
                ·
                  refine ⟨6353682731959894243627501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8471576975946525658170001 6353682731959894243627501)
                  ·
                    refine ⟨2382631024484960341360313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6353682731959894243627501 2382631024484960341360313)
                    ·
                      refine ⟨1786973268363720256020235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2382631024484960341360313 1786973268363720256020235)
                      ·
                        rfl

theorem cell23_3480118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_3480118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480118 prefixEnd_3480118 := by exact prefixLift 3480118
  have htrace : WordTrace (prefixWord ++ tailWord_3480118) baseStart_3480118 baseEnd_3480118 := by
    simpa [prefixWord, tailWord_3480118, baseEnd_3480118] using wordTrace_append hprefix tailTrace_3480118
  have hstable : (prefixWord ++ tailWord_3480118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480118).length < 2 ^ (prefixWord ++ tailWord_3480118).sum := by decide
  have hdescent : baseEnd_3480118 < baseStart_3480118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480125 : List Nat := [1, 4, 1, 3, 2, 1, 4, 2, 1, 1, 3]
def baseStart_3480125 : Nat := 118140960795 + 3480125 * 2 ^ 59
def prefixEnd_3480125 : Nat := 4983230072969 + 3 ^ 40 * 3480125 * 2
def baseEnd_3480125 : Nat := 1786976862728301728632703

theorem tailTrace_3480125 : CollatzResearch.WordTrace tailWord_3480125 prefixEnd_3480125 1786976862728301728632703 := by
  unfold tailWord_3480125
  simp only [CollatzResearch.WordTrace]
  refine ⟨126930586517108957875849829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84620391011405971917233219 126930586517108957875849829)
  ·
    refine ⟨23799484971957929601721843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126930586517108957875849829 23799484971957929601721843)
    ·
      refine ⟨35699227457936894402582765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23799484971957929601721843 35699227457936894402582765)
      ·
        refine ⟨13387210296726335400968537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35699227457936894402582765 13387210296726335400968537)
        ·
          refine ⟨10040407722544751550726403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13387210296726335400968537 10040407722544751550726403)
          ·
            refine ⟨15060611583817127326089605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10040407722544751550726403 15060611583817127326089605)
            ·
              refine ⟨2823864671965711373641801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15060611583817127326089605 2823864671965711373641801)
              ·
                refine ⟨2117898503974283530231351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2823864671965711373641801 2117898503974283530231351)
                ·
                  refine ⟨3176847755961425295347027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2117898503974283530231351 3176847755961425295347027)
                  ·
                    refine ⟨4765271633942137943020541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3176847755961425295347027 4765271633942137943020541)
                    ·
                      refine ⟨1786976862728301728632703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4765271633942137943020541 1786976862728301728632703)
                      ·
                        rfl

theorem cell23_3480125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_3480125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480125 prefixEnd_3480125 := by exact prefixLift 3480125
  have htrace : WordTrace (prefixWord ++ tailWord_3480125) baseStart_3480125 baseEnd_3480125 := by
    simpa [prefixWord, tailWord_3480125, baseEnd_3480125] using wordTrace_append hprefix tailTrace_3480125
  have hstable : (prefixWord ++ tailWord_3480125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480125).length < 2 ^ (prefixWord ++ tailWord_3480125).sum := by decide
  have hdescent : baseEnd_3480125 < baseStart_3480125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480127 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 4]
def baseStart_3480127 : Nat := 118140960795 + 3480127 * 2 ^ 59
def prefixEnd_3480127 : Nat := 4983230072969 + 3 ^ 40 * 3480127 * 2
def baseEnd_3480127 : Nat := 1786977889689610720807693

theorem tailTrace_3480127 : CollatzResearch.WordTrace tailWord_3480127 prefixEnd_3480127 1786977889689610720807693 := by
  unfold tailWord_3480127
  simp only [CollatzResearch.WordTrace]
  refine ⟨126930659463101712217422635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84620439642067808144948423 126930659463101712217422635)
  ·
    refine ⟨190395989194652568326133953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126930659463101712217422635 190395989194652568326133953)
    ·
      refine ⟨142796991895989426244600465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190395989194652568326133953 142796991895989426244600465)
      ·
        refine ⟨107097743921992069683450349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142796991895989426244600465 107097743921992069683450349)
        ·
          refine ⟨40161653970747026131293881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107097743921992069683450349 40161653970747026131293881)
          ·
            refine ⟨30121240478060269598470411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40161653970747026131293881 30121240478060269598470411)
            ·
              refine ⟨45181860717090404397705617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30121240478060269598470411 45181860717090404397705617)
              ·
                refine ⟨33886395537817803298279213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45181860717090404397705617 33886395537817803298279213)
                ·
                  refine ⟨12707398326681676236854705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33886395537817803298279213 12707398326681676236854705)
                  ·
                    refine ⟨9530548745011257177641029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12707398326681676236854705 9530548745011257177641029)
                    ·
                      refine ⟨1786977889689610720807693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9530548745011257177641029 1786977889689610720807693)
                      ·
                        rfl

theorem cell23_3480127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_3480127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480127 prefixEnd_3480127 := by exact prefixLift 3480127
  have htrace : WordTrace (prefixWord ++ tailWord_3480127) baseStart_3480127 baseEnd_3480127 := by
    simpa [prefixWord, tailWord_3480127, baseEnd_3480127] using wordTrace_append hprefix tailTrace_3480127
  have hstable : (prefixWord ++ tailWord_3480127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480127).length < 2 ^ (prefixWord ++ tailWord_3480127).sum := by decide
  have hdescent : baseEnd_3480127 < baseStart_3480127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480141 : List Nat := [1, 6, 1, 1, 2, 2, 2, 1, 1, 6]
def baseStart_3480141 : Nat := 118140960795 + 3480141 * 2 ^ 59
def prefixEnd_3480141 : Nat := 4983230072969 + 3 ^ 40 * 3480141 * 2
def baseEnd_3480141 : Nat := 595661692806257888677543

theorem tailTrace_3480141 : CollatzResearch.WordTrace tailWord_3480141 prefixEnd_3480141 595661692806257888677543 := by
  unfold tailWord_3480141
  simp only [CollatzResearch.WordTrace]
  refine ⟨126931170085050992608432277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84620780056700661738954851 126931170085050992608432277)
  ·
    refine ⟨5949898597736765278520263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 126931170085050992608432277 5949898597736765278520263)
    ·
      refine ⟨8924847896605147917780395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5949898597736765278520263 8924847896605147917780395)
      ·
        refine ⟨13387271844907721876670593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8924847896605147917780395 13387271844907721876670593)
        ·
          refine ⟨10040453883680791407502945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13387271844907721876670593 10040453883680791407502945)
          ·
            refine ⟨7530340412760593555627209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10040453883680791407502945 7530340412760593555627209)
            ·
              refine ⟨5647755309570445166720407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7530340412760593555627209 5647755309570445166720407)
              ·
                refine ⟨8471632964355667750080611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5647755309570445166720407 8471632964355667750080611)
                ·
                  refine ⟨12707449446533501625120917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8471632964355667750080611 12707449446533501625120917)
                  ·
                    refine ⟨595661692806257888677543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12707449446533501625120917 595661692806257888677543)
                    ·
                      rfl

theorem cell23_3480141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_3480141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480141 prefixEnd_3480141 := by exact prefixLift 3480141
  have htrace : WordTrace (prefixWord ++ tailWord_3480141) baseStart_3480141 baseEnd_3480141 := by
    simpa [prefixWord, tailWord_3480141, baseEnd_3480141] using wordTrace_append hprefix tailTrace_3480141
  have hstable : (prefixWord ++ tailWord_3480141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480141).length < 2 ^ (prefixWord ++ tailWord_3480141).sum := by decide
  have hdescent : baseEnd_3480141 < baseStart_3480141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480148 : List Nat := [2, 4, 1, 1, 1, 4, 1, 2, 3, 2, 2]
def baseStart_3480148 : Nat := 118140960795 + 3480148 * 2 ^ 59
def prefixEnd_3480148 : Nat := 4983230072969 + 3 ^ 40 * 3480148 * 2
def baseEnd_3480148 : Nat := 1786988672783355138645097

theorem tailTrace_3480148 : CollatzResearch.WordTrace tailWord_3480148 prefixEnd_3480148 1786988672783355138645097 := by
  unfold tailWord_3480148
  simp only [CollatzResearch.WordTrace]
  refine ⟨63465712698012816401968549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84620950264017088535958065 63465712698012816401968549)
  ·
    refine ⟨11899821130877403075369103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63465712698012816401968549 11899821130877403075369103)
    ·
      refine ⟨17849731696316104613053655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11899821130877403075369103 17849731696316104613053655)
      ·
        refine ⟨26774597544474156919580483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17849731696316104613053655 26774597544474156919580483)
        ·
          refine ⟨40161896316711235379370725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26774597544474156919580483 40161896316711235379370725)
          ·
            refine ⟨7530355559383356633632011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40161896316711235379370725 7530355559383356633632011)
            ·
              refine ⟨11295533339075034950448017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7530355559383356633632011 11295533339075034950448017)
              ·
                refine ⟨8471650004306276212836013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11295533339075034950448017 8471650004306276212836013)
                ·
                  refine ⟨3176868751614853579813505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8471650004306276212836013 3176868751614853579813505)
                  ·
                    refine ⟨2382651563711140184860129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3176868751614853579813505 2382651563711140184860129)
                    ·
                      refine ⟨1786988672783355138645097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2382651563711140184860129 1786988672783355138645097)
                      ·
                        rfl

theorem cell23_3480148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_3480148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480148 prefixEnd_3480148 := by exact prefixLift 3480148
  have htrace : WordTrace (prefixWord ++ tailWord_3480148) baseStart_3480148 baseEnd_3480148 := by
    simpa [prefixWord, tailWord_3480148, baseEnd_3480148] using wordTrace_append hprefix tailTrace_3480148
  have hstable : (prefixWord ++ tailWord_3480148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480148).length < 2 ^ (prefixWord ++ tailWord_3480148).sum := by decide
  have hdescent : baseEnd_3480148 < baseStart_3480148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480162 : List Nat := [3, 3, 2, 3, 2, 1, 2, 1, 1, 5]
def baseStart_3480162 : Nat := 118140960795 + 3480162 * 2 ^ 59
def prefixEnd_3480162 : Nat := 4983230072969 + 3 ^ 40 * 3480162 * 2
def baseEnd_3480162 : Nat := 595665287170839361290011

theorem tailTrace_3480162 : CollatzResearch.WordTrace tailWord_3480162 prefixEnd_3480162 595665287170839361290011 := by
  unfold tailWord_3480162
  simp only [CollatzResearch.WordTrace]
  refine ⟨31732984004493728298736685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84621290678649942129964493 31732984004493728298736685)
  ·
    refine ⟨11899869001685148112026257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31732984004493728298736685 11899869001685148112026257)
    ·
      refine ⟨8924901751263861084019693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11899869001685148112026257 8924901751263861084019693)
      ·
        refine ⟨3346838156723947906507385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8924901751263861084019693 3346838156723947906507385)
        ·
          refine ⟨2510128617542960929880539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3346838156723947906507385 2510128617542960929880539)
          ·
            refine ⟨3765192926314441394820809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2510128617542960929880539 3765192926314441394820809)
            ·
              refine ⟨2823894694735831046115607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3765192926314441394820809 2823894694735831046115607)
              ·
                refine ⟨4235842042103746569173411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2823894694735831046115607 4235842042103746569173411)
                ·
                  refine ⟨6353763063155619853760117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4235842042103746569173411 6353763063155619853760117)
                  ·
                    refine ⟨595665287170839361290011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6353763063155619853760117 595665287170839361290011)
                    ·
                      rfl

theorem cell23_3480162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_3480162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480162 prefixEnd_3480162 := by exact prefixLift 3480162
  have htrace : WordTrace (prefixWord ++ tailWord_3480162) baseStart_3480162 baseEnd_3480162 := by
    simpa [prefixWord, tailWord_3480162, baseEnd_3480162] using wordTrace_append hprefix tailTrace_3480162
  have hstable : (prefixWord ++ tailWord_3480162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480162).length < 2 ^ (prefixWord ++ tailWord_3480162).sum := by decide
  have hdescent : baseEnd_3480162 < baseStart_3480162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480164 : List Nat := [2, 3, 1, 1, 2, 2, 1, 4, 1, 3, 3]
def baseStart_3480164 : Nat := 118140960795 + 3480164 * 2 ^ 59
def prefixEnd_3480164 : Nat := 4983230072969 + 3 ^ 40 * 3480164 * 2
def baseEnd_3480164 : Nat := 1786996888473827076045023

theorem tailTrace_3480164 : CollatzResearch.WordTrace tailWord_3480164 prefixEnd_3480164 1786996888473827076045023 := by
  unfold tailWord_3480164
  simp only [CollatzResearch.WordTrace]
  refine ⟨63466004481983833768259773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84621339309311778357679697 63466004481983833768259773)
  ·
    refine ⟨23799751680743937663097415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63466004481983833768259773 23799751680743937663097415)
    ·
      refine ⟨35699627521115906494646123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23799751680743937663097415 35699627521115906494646123)
      ·
        refine ⟨53549441281673859741969185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35699627521115906494646123 53549441281673859741969185)
        ·
          refine ⟨40162080961255394806476889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53549441281673859741969185 40162080961255394806476889)
          ·
            refine ⟨30121560720941546104857667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40162080961255394806476889 30121560720941546104857667)
            ·
              refine ⟨45182341081412319157286501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30121560720941546104857667 45182341081412319157286501)
              ·
                refine ⟨8471688952764809841991219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45182341081412319157286501 8471688952764809841991219)
                ·
                  refine ⟨12707533429147214762986829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8471688952764809841991219 12707533429147214762986829)
                  ·
                    refine ⟨4765325035930205536120061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12707533429147214762986829 4765325035930205536120061)
                    ·
                      refine ⟨1786996888473827076045023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4765325035930205536120061 1786996888473827076045023)
                      ·
                        rfl

theorem cell23_3480164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_3480164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480164 prefixEnd_3480164 := by exact prefixLift 3480164
  have htrace : WordTrace (prefixWord ++ tailWord_3480164) baseStart_3480164 baseEnd_3480164 := by
    simpa [prefixWord, tailWord_3480164, baseEnd_3480164] using wordTrace_append hprefix tailTrace_3480164
  have hstable : (prefixWord ++ tailWord_3480164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480164).length < 2 ^ (prefixWord ++ tailWord_3480164).sum := by decide
  have hdescent : baseEnd_3480164 < baseStart_3480164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480165 : List Nat := [1, 3, 1, 3, 5, 1, 2, 1, 1, 1, 4]
def baseStart_3480165 : Nat := 118140960795 + 3480165 * 2 ^ 59
def prefixEnd_3480165 : Nat := 4983230072969 + 3 ^ 40 * 3480165 * 2
def baseEnd_3480165 : Nat := 1786997401954481572132519

theorem tailTrace_3480165 : CollatzResearch.WordTrace tailWord_3480165 prefixEnd_3480165 1786997401954481572132519 := by
  unfold tailWord_3480165
  simp only [CollatzResearch.WordTrace]
  refine ⟨126932045436964044707305949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84621363624642696471537299 126932045436964044707305949)
  ·
    refine ⟨47599517038861516765239731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126932045436964044707305949 47599517038861516765239731)
    ·
      refine ⟨71399275558292275147859597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47599517038861516765239731 71399275558292275147859597)
      ·
        refine ⟨26774728334359603180447349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71399275558292275147859597 26774728334359603180447349)
        ·
          refine ⟨2510130781346212798166939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26774728334359603180447349 2510130781346212798166939)
          ·
            refine ⟨3765196172019319197250409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2510130781346212798166939 3765196172019319197250409)
            ·
              refine ⟨2823897129014489397937807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3765196172019319197250409 2823897129014489397937807)
              ·
                refine ⟨4235845693521734096906711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2823897129014489397937807 4235845693521734096906711)
                ·
                  refine ⟨6353768540282601145360067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4235845693521734096906711 6353768540282601145360067)
                  ·
                    refine ⟨9530652810423901718040101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6353768540282601145360067 9530652810423901718040101)
                    ·
                      refine ⟨1786997401954481572132519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9530652810423901718040101 1786997401954481572132519)
                      ·
                        rfl

theorem cell23_3480165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_3480165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480165 prefixEnd_3480165 := by exact prefixLift 3480165
  have htrace : WordTrace (prefixWord ++ tailWord_3480165) baseStart_3480165 baseEnd_3480165 := by
    simpa [prefixWord, tailWord_3480165, baseEnd_3480165] using wordTrace_append hprefix tailTrace_3480165
  have hstable : (prefixWord ++ tailWord_3480165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480165).length < 2 ^ (prefixWord ++ tailWord_3480165).sum := by decide
  have hdescent : baseEnd_3480165 < baseStart_3480165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480168 : List Nat := [2, 1, 4, 3, 2, 1, 1, 3, 1, 2, 3]
def baseStart_3480168 : Nat := 118140960795 + 3480168 * 2 ^ 59
def prefixEnd_3480168 : Nat := 4983230072969 + 3 ^ 40 * 3480168 * 2
def baseEnd_3480168 : Nat := 1786998942396445060395005

theorem tailTrace_3480168 : CollatzResearch.WordTrace tailWord_3480168 prefixEnd_3480168 1786998942396445060395005 := by
  unfold tailWord_3480168
  simp only [CollatzResearch.WordTrace]
  refine ⟨63466077427976588109832579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84621436570635450813110105 63466077427976588109832579)
  ·
    refine ⟨95199116141964882164748869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63466077427976588109832579 95199116141964882164748869)
    ·
      refine ⟨17849834276618415405890413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95199116141964882164748869 17849834276618415405890413)
      ·
        refine ⟨6693687853731905777208905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17849834276618415405890413 6693687853731905777208905)
        ·
          refine ⟨5020265890298929332906679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6693687853731905777208905 5020265890298929332906679)
          ·
            refine ⟨7530398835448393999360019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5020265890298929332906679 7530398835448393999360019)
            ·
              refine ⟨11295598253172590999040029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7530398835448393999360019 11295598253172590999040029)
              ·
                refine ⟨4235849344939721624640011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11295598253172590999040029 4235849344939721624640011)
                ·
                  refine ⟨6353774017409582436960017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4235849344939721624640011 6353774017409582436960017)
                  ·
                    refine ⟨4765330513057186827720013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6353774017409582436960017 4765330513057186827720013)
                    ·
                      refine ⟨1786998942396445060395005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4765330513057186827720013 1786998942396445060395005)
                      ·
                        rfl

theorem cell23_3480168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_3480168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480168 prefixEnd_3480168 := by exact prefixLift 3480168
  have htrace : WordTrace (prefixWord ++ tailWord_3480168) baseStart_3480168 baseEnd_3480168 := by
    simpa [prefixWord, tailWord_3480168, baseEnd_3480168] using wordTrace_append hprefix tailTrace_3480168
  have hstable : (prefixWord ++ tailWord_3480168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480168).length < 2 ^ (prefixWord ++ tailWord_3480168).sum := by decide
  have hdescent : baseEnd_3480168 < baseStart_3480168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480187 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 4]
def baseStart_3480187 : Nat := 118140960795 + 3480187 * 2 ^ 59
def prefixEnd_3480187 : Nat := 4983230072969 + 3 ^ 40 * 3480187 * 2
def baseEnd_3480187 : Nat := 1787008698528880486057417

theorem tailTrace_3480187 : CollatzResearch.WordTrace tailWord_3480187 prefixEnd_3480187 1787008698528880486057417 := by
  unfold tailWord_3480187
  simp only [CollatzResearch.WordTrace]
  refine ⟨126932847842884342464606815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84621898561922894976404543 126932847842884342464606815)
  ·
    refine ⟨190399271764326513696910223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126932847842884342464606815 190399271764326513696910223)
    ·
      refine ⟨285598907646489770545365335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190399271764326513696910223 285598907646489770545365335)
      ·
        refine ⟨428398361469734655818048003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285598907646489770545365335 428398361469734655818048003)
        ·
          refine ⟨642597542204601983727072005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428398361469734655818048003 642597542204601983727072005)
          ·
            refine ⟨120487039163362871948826001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 642597542204601983727072005 120487039163362871948826001)
            ·
              refine ⟨90365279372522153961619501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120487039163362871948826001 90365279372522153961619501)
              ·
                refine ⟨33886979764695807735607313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90365279372522153961619501 33886979764695807735607313)
                ·
                  refine ⟨25415234823521855801705485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33886979764695807735607313 25415234823521855801705485)
                  ·
                    refine ⟨9530713058820695925639557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25415234823521855801705485 9530713058820695925639557)
                    ·
                      refine ⟨1787008698528880486057417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9530713058820695925639557 1787008698528880486057417)
                      ·
                        rfl

theorem cell23_3480187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 4].length) (baseStart_3480187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480187 prefixEnd_3480187 := by exact prefixLift 3480187
  have htrace : WordTrace (prefixWord ++ tailWord_3480187) baseStart_3480187 baseEnd_3480187 := by
    simpa [prefixWord, tailWord_3480187, baseEnd_3480187] using wordTrace_append hprefix tailTrace_3480187
  have hstable : (prefixWord ++ tailWord_3480187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480187).length < 2 ^ (prefixWord ++ tailWord_3480187).sum := by decide
  have hdescent : baseEnd_3480187 < baseStart_3480187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480207 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 5]
def baseStart_3480207 : Nat := 118140960795 + 3480207 * 2 ^ 59
def prefixEnd_3480207 : Nat := 4983230072969 + 3 ^ 40 * 3480207 * 2
def baseEnd_3480207 : Nat := 1787018968141970407807325

theorem tailTrace_3480207 : CollatzResearch.WordTrace tailWord_3480207 prefixEnd_3480207 1787018968141970407807325 := by
  unfold tailWord_3480207
  simp only [CollatzResearch.WordTrace]
  refine ⟨126933577302811885880334875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84622384868541257253556583 126933577302811885880334875)
  ·
    refine ⟨190400365954217828820502313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126933577302811885880334875 190400365954217828820502313)
    ·
      refine ⟨142800274465663371615376735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190400365954217828820502313 142800274465663371615376735)
      ·
        refine ⟨214200411698495057423065103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142800274465663371615376735 214200411698495057423065103)
        ·
          refine ⟨321300617547742586134597655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214200411698495057423065103 321300617547742586134597655)
          ·
            refine ⟨481950926321613879201896483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321300617547742586134597655 481950926321613879201896483)
            ·
              refine ⟨722926389482420818802844725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481950926321613879201896483 722926389482420818802844725)
              ·
                refine ⟨67774349013976951762766693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 722926389482420818802844725 67774349013976951762766693)
                ·
                  refine ⟨12707690440120678455518755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67774349013976951762766693 12707690440120678455518755)
                  ·
                    refine ⟨19061535660181017683278133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12707690440120678455518755 19061535660181017683278133)
                    ·
                      refine ⟨1787018968141970407807325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19061535660181017683278133 1787018968141970407807325)
                      ·
                        rfl

theorem cell23_3480207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 5].length) (baseStart_3480207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480207 prefixEnd_3480207 := by exact prefixLift 3480207
  have htrace : WordTrace (prefixWord ++ tailWord_3480207) baseStart_3480207 baseEnd_3480207 := by
    simpa [prefixWord, tailWord_3480207, baseEnd_3480207] using wordTrace_append hprefix tailTrace_3480207
  have hstable : (prefixWord ++ tailWord_3480207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480207).length < 2 ^ (prefixWord ++ tailWord_3480207).sum := by decide
  have hdescent : baseEnd_3480207 < baseStart_3480207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480221 : List Nat := [1, 4, 2, 1, 1, 1, 2, 4, 1, 4, 2]
def baseStart_3480221 : Nat := 118140960795 + 3480221 * 2 ^ 59
def prefixEnd_3480221 : Nat := 4983230072969 + 3 ^ 40 * 3480221 * 2
def baseEnd_3480221 : Nat := 1787026156871133353032261

theorem tailTrace_3480221 : CollatzResearch.WordTrace tailWord_3480221 prefixEnd_3480221 1787026156871133353032261 := by
  unfold tailWord_3480221
  simp only [CollatzResearch.WordTrace]
  refine ⟨126934087924761166271344517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84622725283174110847563011 126934087924761166271344517)
  ·
    refine ⟨23800141485892718675877097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126934087924761166271344517 23800141485892718675877097)
    ·
      refine ⟨17850106114419539006907823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23800141485892718675877097 17850106114419539006907823)
      ·
        refine ⟨26775159171629308510361735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17850106114419539006907823 26775159171629308510361735)
        ·
          refine ⟨40162738757443962765542603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26775159171629308510361735 40162738757443962765542603)
          ·
            refine ⟨60244108136165944148313905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40162738757443962765542603 60244108136165944148313905)
            ·
              refine ⟨45183081102124458111235429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60244108136165944148313905 45183081102124458111235429)
              ·
                refine ⟨8471827706648335895856643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45183081102124458111235429 8471827706648335895856643)
                ·
                  refine ⟨12707741559972503843784965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8471827706648335895856643 12707741559972503843784965)
                  ·
                    refine ⟨2382701542494844470709681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12707741559972503843784965 2382701542494844470709681)
                    ·
                      refine ⟨1787026156871133353032261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2382701542494844470709681 1787026156871133353032261)
                      ·
                        rfl

theorem cell23_3480221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_3480221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480221 prefixEnd_3480221 := by exact prefixLift 3480221
  have htrace : WordTrace (prefixWord ++ tailWord_3480221) baseStart_3480221 baseEnd_3480221 := by
    simpa [prefixWord, tailWord_3480221, baseEnd_3480221] using wordTrace_append hprefix tailTrace_3480221
  have hstable : (prefixWord ++ tailWord_3480221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480221).length < 2 ^ (prefixWord ++ tailWord_3480221).sum := by decide
  have hdescent : baseEnd_3480221 < baseStart_3480221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480255 : List Nat := [1, 1, 2, 2, 2, 4, 4, 1, 2, 2, 2]
def baseStart_3480255 : Nat := 118140960795 + 3480255 * 2 ^ 59
def prefixEnd_3480255 : Nat := 4983230072969 + 3 ^ 40 * 3480255 * 2
def baseEnd_3480255 : Nat := 1787043615213386220007105

theorem tailTrace_3480255 : CollatzResearch.WordTrace tailWord_3480255 prefixEnd_3480255 1787043615213386220007105 := by
  unfold tailWord_3480255
  simp only [CollatzResearch.WordTrace]
  refine ⟨126935328006637990078082219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84623552004425326718721479 126935328006637990078082219)
  ·
    refine ⟨190402992009956985117123329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126935328006637990078082219 190402992009956985117123329)
    ·
      refine ⟨142802244007467738837842497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190402992009956985117123329 142802244007467738837842497)
      ·
        refine ⟨107101683005600804128381873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142802244007467738837842497 107101683005600804128381873)
        ·
          refine ⟨80326262254200603096286405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107101683005600804128381873 80326262254200603096286405)
          ·
            refine ⟨15061174172662613080553701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80326262254200603096286405 15061174172662613080553701)
            ·
              refine ⟨2823970157374239952603819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15061174172662613080553701 2823970157374239952603819)
              ·
                refine ⟨4235955236061359928905729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2823970157374239952603819 4235955236061359928905729)
                ·
                  refine ⟨3176966427046019946679297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4235955236061359928905729 3176966427046019946679297)
                  ·
                    refine ⟨2382724820284514960009473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3176966427046019946679297 2382724820284514960009473)
                    ·
                      refine ⟨1787043615213386220007105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2382724820284514960009473 1787043615213386220007105)
                      ·
                        rfl

theorem cell23_3480255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 2, 2, 2].length) (baseStart_3480255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480255 prefixEnd_3480255 := by exact prefixLift 3480255
  have htrace : WordTrace (prefixWord ++ tailWord_3480255) baseStart_3480255 baseEnd_3480255 := by
    simpa [prefixWord, tailWord_3480255, baseEnd_3480255] using wordTrace_append hprefix tailTrace_3480255
  have hstable : (prefixWord ++ tailWord_3480255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480255).length < 2 ^ (prefixWord ++ tailWord_3480255).sum := by decide
  have hdescent : baseEnd_3480255 < baseStart_3480255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480291 : List Nat := [1, 1, 1, 7, 1, 1, 2, 2, 2, 5]
def baseStart_3480291 : Nat := 118140960795 + 3480291 * 2 ^ 59
def prefixEnd_3480291 : Nat := 4983230072969 + 3 ^ 40 * 3480291 * 2
def baseEnd_3480291 : Nat := 595687366838982693052313

theorem tailTrace_3480291 : CollatzResearch.WordTrace tailWord_3480291 prefixEnd_3480291 595687366838982693052313 := by
  unfold tailWord_3480291
  simp only [CollatzResearch.WordTrace]
  refine ⟨126936641034507568226392727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84624427356338378817595151 126936641034507568226392727)
  ·
    refine ⟨190404961551761352339589091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126936641034507568226392727 190404961551761352339589091)
    ·
      refine ⟨285607442327642028509383637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190404961551761352339589091 285607442327642028509383637)
      ·
        refine ⟨6693924429554110043188679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 285607442327642028509383637 6693924429554110043188679)
        ·
          refine ⟨10040886644331165064783019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6693924429554110043188679 10040886644331165064783019)
          ·
            refine ⟨15061329966496747597174529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10040886644331165064783019 15061329966496747597174529)
            ·
              refine ⟨11295997474872560697880897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15061329966496747597174529 11295997474872560697880897)
              ·
                refine ⟨8471998106154420523410673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11295997474872560697880897 8471998106154420523410673)
                ·
                  refine ⟨6353998579615815392558005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8471998106154420523410673 6353998579615815392558005)
                  ·
                    refine ⟨595687366838982693052313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6353998579615815392558005 595687366838982693052313)
                    ·
                      rfl

theorem cell23_3480291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 5].length) (baseStart_3480291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480291 prefixEnd_3480291 := by exact prefixLift 3480291
  have htrace : WordTrace (prefixWord ++ tailWord_3480291) baseStart_3480291 baseEnd_3480291 := by
    simpa [prefixWord, tailWord_3480291, baseEnd_3480291] using wordTrace_append hprefix tailTrace_3480291
  have hstable : (prefixWord ++ tailWord_3480291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480291).length < 2 ^ (prefixWord ++ tailWord_3480291).sum := by decide
  have hdescent : baseEnd_3480291 < baseStart_3480291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480328 : List Nat := [2, 1, 3, 2, 2, 4, 1, 1, 2, 1, 4]
def baseStart_3480328 : Nat := 118140960795 + 3480328 * 2 ^ 59
def prefixEnd_3480328 : Nat := 4983230072969 + 3 ^ 40 * 3480328 * 2
def baseEnd_3480328 : Nat := 1787081099301164434394269

theorem tailTrace_3480328 : CollatzResearch.WordTrace tailWord_3480328 prefixEnd_3480328 1787081099301164434394269 := by
  unfold tailWord_3480328
  simp only [CollatzResearch.WordTrace]
  refine ⟨63468995267686761772744819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84625327023582349030326425 63468995267686761772744819)
  ·
    refine ⟨95203492901530142659117229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63468995267686761772744819 95203492901530142659117229)
    ·
      refine ⟨35701309838073803497168961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95203492901530142659117229 35701309838073803497168961)
      ·
        refine ⟨26775982378555352622876721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35701309838073803497168961 26775982378555352622876721)
        ·
          refine ⟨20081986783916514467157541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26775982378555352622876721 20081986783916514467157541)
          ·
            refine ⟨3765372521984346462592039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20081986783916514467157541 3765372521984346462592039)
            ·
              refine ⟨5648058782976519693888059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3765372521984346462592039 5648058782976519693888059)
              ·
                refine ⟨8472088174464779540832089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5648058782976519693888059 8472088174464779540832089)
                ·
                  refine ⟨6354066130848584655624067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8472088174464779540832089 6354066130848584655624067)
                  ·
                    refine ⟨9531099196272876983436101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6354066130848584655624067 9531099196272876983436101)
                    ·
                      refine ⟨1787081099301164434394269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9531099196272876983436101 1787081099301164434394269)
                      ·
                        rfl

theorem cell23_3480328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_3480328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480328 prefixEnd_3480328 := by exact prefixLift 3480328
  have htrace : WordTrace (prefixWord ++ tailWord_3480328) baseStart_3480328 baseEnd_3480328 := by
    simpa [prefixWord, tailWord_3480328, baseEnd_3480328] using wordTrace_append hprefix tailTrace_3480328
  have hstable : (prefixWord ++ tailWord_3480328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480328).length < 2 ^ (prefixWord ++ tailWord_3480328).sum := by decide
  have hdescent : baseEnd_3480328 < baseStart_3480328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480334 : List Nat := [4, 1, 1, 2, 1, 1, 1, 4, 8]
def baseStart_3480334 : Nat := 118140960795 + 3480334 * 2 ^ 59
def prefixEnd_3480334 : Nat := 4983230072969 + 3 ^ 40 * 3480334 * 2
def baseEnd_3480334 : Nat := 198564908909454601213249

theorem tailTrace_3480334 : CollatzResearch.WordTrace tailWord_3480334 prefixEnd_3480334 198564908909454601213249 := by
  unfold tailWord_3480334
  simp only [CollatzResearch.WordTrace]
  refine ⟨15867276171668973321276007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84625472915567857713472037 15867276171668973321276007)
  ·
    refine ⟨23800914257503459981914011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15867276171668973321276007 23800914257503459981914011)
    ·
      refine ⟨35701371386255189972871017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23800914257503459981914011 35701371386255189972871017)
      ·
        refine ⟨26776028539691392479653263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35701371386255189972871017 26776028539691392479653263)
        ·
          refine ⟨40164042809537088719479895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26776028539691392479653263 40164042809537088719479895)
          ·
            refine ⟨60246064214305633079219843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40164042809537088719479895 60246064214305633079219843)
            ·
              refine ⟨90369096321458449618829765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60246064214305633079219843 90369096321458449618829765)
              ·
                refine ⟨16944205560273459303530581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90369096321458449618829765 16944205560273459303530581)
                ·
                  refine ⟨198564908909454601213249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16944205560273459303530581 198564908909454601213249)
                  ·
                    rfl

theorem cell23_3480334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 8].length) (baseStart_3480334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480334 prefixEnd_3480334 := by exact prefixLift 3480334
  have htrace : WordTrace (prefixWord ++ tailWord_3480334) baseStart_3480334 baseEnd_3480334 := by
    simpa [prefixWord, tailWord_3480334, baseEnd_3480334] using wordTrace_append hprefix tailTrace_3480334
  have hstable : (prefixWord ++ tailWord_3480334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480334).length < 2 ^ (prefixWord ++ tailWord_3480334).sum := by decide
  have hdescent : baseEnd_3480334 < baseStart_3480334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480351 : List Nat := [1, 1, 2, 4, 2, 2, 3, 2, 6]
def baseStart_3480351 : Nat := 118140960795 + 3480351 * 2 ^ 59
def prefixEnd_3480351 : Nat := 4983230072969 + 3 ^ 40 * 3480351 * 2
def baseEnd_3480351 : Nat := 198565878817357538267407

theorem tailTrace_3480351 : CollatzResearch.WordTrace tailWord_3480351 prefixEnd_3480351 198565878817357538267407 := by
  unfold tailWord_3480351
  simp only [CollatzResearch.WordTrace]
  refine ⟨126938829414290198473576907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84625886276193465649051271 126938829414290198473576907)
  ·
    refine ⟨190408244121435297710365361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126938829414290198473576907 190408244121435297710365361)
    ·
      refine ⟨142806183091076473282774021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190408244121435297710365361 142806183091076473282774021)
      ·
        refine ⟨26776159329576838740520129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142806183091076473282774021 26776159329576838740520129)
        ·
          refine ⟨20082119497182629055390097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26776159329576838740520129 20082119497182629055390097)
          ·
            refine ⟨15061589622886971791542573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20082119497182629055390097 15061589622886971791542573)
            ·
              refine ⟨5648096108582614421828465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15061589622886971791542573 5648096108582614421828465)
              ·
                refine ⟨4236072081436960816371349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5648096108582614421828465 4236072081436960816371349)
                ·
                  refine ⟨198565878817357538267407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4236072081436960816371349 198565878817357538267407)
                  ·
                    rfl

theorem cell23_3480351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 6].length) (baseStart_3480351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480351 prefixEnd_3480351 := by exact prefixLift 3480351
  have htrace : WordTrace (prefixWord ++ tailWord_3480351) baseStart_3480351 baseEnd_3480351 := by
    simpa [prefixWord, tailWord_3480351, baseEnd_3480351] using wordTrace_append hprefix tailTrace_3480351
  have hstable : (prefixWord ++ tailWord_3480351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480351).length < 2 ^ (prefixWord ++ tailWord_3480351).sum := by decide
  have hdescent : baseEnd_3480351 < baseStart_3480351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480361 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 7, 1, 3]
def baseStart_3480361 : Nat := 118140960795 + 3480361 * 2 ^ 59
def prefixEnd_3480361 : Nat := 4983230072969 + 3 ^ 40 * 3480361 * 2
def baseEnd_3480361 : Nat := 1787098044162762805281617

theorem tailTrace_3480361 : CollatzResearch.WordTrace tailWord_3480361 prefixEnd_3480361 1787098044162762805281617 := by
  unfold tailWord_3480361
  simp only [CollatzResearch.WordTrace]
  refine ⟨126939194144253970181440937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84626129429502646787627291 126939194144253970181440937)
  ·
    refine ⟨95204395608190477636080703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126939194144253970181440937 95204395608190477636080703)
    ·
      refine ⟨142806593412285716454121055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95204395608190477636080703 142806593412285716454121055)
      ·
        refine ⟨214209890118428574681181583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142806593412285716454121055 214209890118428574681181583)
        ·
          refine ⟨321314835177642862021772375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214209890118428574681181583 321314835177642862021772375)
          ·
            refine ⟨481972252766464293032658563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321314835177642862021772375 481972252766464293032658563)
            ·
              refine ⟨722958379149696439548987845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481972252766464293032658563 722958379149696439548987845)
              ·
                refine ⟨135554696090568082415435221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 722958379149696439548987845 135554696090568082415435221)
                ·
                  refine ⟨3177063189622689431611763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 135554696090568082415435221 3177063189622689431611763)
                  ·
                    refine ⟨4765594784434034147417645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3177063189622689431611763 4765594784434034147417645)
                    ·
                      refine ⟨1787098044162762805281617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4765594784434034147417645 1787098044162762805281617)
                      ·
                        rfl

theorem cell23_3480361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 7, 1, 3].length) (baseStart_3480361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480361 prefixEnd_3480361 := by exact prefixLift 3480361
  have htrace : WordTrace (prefixWord ++ tailWord_3480361) baseStart_3480361 baseEnd_3480361 := by
    simpa [prefixWord, tailWord_3480361, baseEnd_3480361] using wordTrace_append hprefix tailTrace_3480361
  have hstable : (prefixWord ++ tailWord_3480361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480361).length < 2 ^ (prefixWord ++ tailWord_3480361).sum := by decide
  have hdescent : baseEnd_3480361 < baseStart_3480361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480384 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 4]
def baseStart_3480384 : Nat := 118140960795 + 3480384 * 2 ^ 59
def prefixEnd_3480384 : Nat := 4983230072969 + 3 ^ 40 * 3480384 * 2
def baseEnd_3480384 : Nat := 1787109854217816215294011

theorem tailTrace_3480384 : CollatzResearch.WordTrace tailWord_3480384 prefixEnd_3480384 1787109854217816215294011 := by
  unfold tailWord_3480384
  simp only [CollatzResearch.WordTrace]
  refine ⟨63470016511585322554764103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84626688682113763406352137 63470016511585322554764103)
  ·
    refine ⟨95205024767377983832146155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63470016511585322554764103 95205024767377983832146155)
    ·
      refine ⟨142807537151066975748219233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95205024767377983832146155 142807537151066975748219233)
      ·
        refine ⟨107105652863300231811164425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142807537151066975748219233 107105652863300231811164425)
        ·
          refine ⟨80329239647475173858373319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107105652863300231811164425 80329239647475173858373319)
          ·
            refine ⟨120493859471212760787559979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80329239647475173858373319 120493859471212760787559979)
            ·
              refine ⟨180740789206819141181339969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120493859471212760787559979 180740789206819141181339969)
              ·
                refine ⟨135555591905114355886004977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180740789206819141181339969 135555591905114355886004977)
                ·
                  refine ⟨101666693928835766914503733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135555591905114355886004977 101666693928835766914503733)
                  ·
                    refine ⟨9531252555828353148234725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101666693928835766914503733 9531252555828353148234725)
                    ·
                      refine ⟨1787109854217816215294011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9531252555828353148234725 1787109854217816215294011)
                      ·
                        rfl

theorem cell23_3480384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_3480384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480384 prefixEnd_3480384 := by exact prefixLift 3480384
  have htrace : WordTrace (prefixWord ++ tailWord_3480384) baseStart_3480384 baseEnd_3480384 := by
    simpa [prefixWord, tailWord_3480384, baseEnd_3480384] using wordTrace_append hprefix tailTrace_3480384
  have hstable : (prefixWord ++ tailWord_3480384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480384).length < 2 ^ (prefixWord ++ tailWord_3480384).sum := by decide
  have hdescent : baseEnd_3480384 < baseStart_3480384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480412 : List Nat := [2, 2, 4, 2, 1, 3, 1, 1, 3, 1, 3]
def baseStart_3480412 : Nat := 118140960795 + 3480412 * 2 ^ 59
def prefixEnd_3480412 : Nat := 4983230072969 + 3 ^ 40 * 3480412 * 2
def baseEnd_3480412 : Nat := 1787124231676142105743883

theorem tailTrace_3480412 : CollatzResearch.WordTrace tailWord_3480412 prefixEnd_3480412 1787124231676142105743883 := by
  unfold tailWord_3480412
  simp only [CollatzResearch.WordTrace]
  refine ⟨63470527133534602945773745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84627369511379470594364993 63470527133534602945773745)
  ·
    refine ⟨47602895350150952209330309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63470527133534602945773745 47602895350150952209330309)
    ·
      refine ⟨8925542878153303539249433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47602895350150952209330309 8925542878153303539249433)
      ·
        refine ⟨6694157158614977654437075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8925542878153303539249433 6694157158614977654437075)
        ·
          refine ⟨10041235737922466481655613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6694157158614977654437075 10041235737922466481655613)
          ·
            refine ⟨3765463401720924930620855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10041235737922466481655613 3765463401720924930620855)
            ·
              refine ⟨5648195102581387395931283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3765463401720924930620855 5648195102581387395931283)
              ·
                refine ⟨8472292653872081093896925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5648195102581387395931283 8472292653872081093896925)
                ·
                  refine ⟨3177109745202030410211347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8472292653872081093896925 3177109745202030410211347)
                  ·
                    refine ⟨4765664617803045615317021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3177109745202030410211347 4765664617803045615317021)
                    ·
                      refine ⟨1787124231676142105743883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4765664617803045615317021 1787124231676142105743883)
                      ·
                        rfl

theorem cell23_3480412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_3480412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480412 prefixEnd_3480412 := by exact prefixLift 3480412
  have htrace : WordTrace (prefixWord ++ tailWord_3480412) baseStart_3480412 baseEnd_3480412 := by
    simpa [prefixWord, tailWord_3480412, baseEnd_3480412] using wordTrace_append hprefix tailTrace_3480412
  have hstable : (prefixWord ++ tailWord_3480412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480412).length < 2 ^ (prefixWord ++ tailWord_3480412).sum := by decide
  have hdescent : baseEnd_3480412 < baseStart_3480412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480421 : List Nat := [1, 3, 1, 3, 1, 1, 4, 2, 1, 1, 5]
def baseStart_3480421 : Nat := 118140960795 + 3480421 * 2 ^ 59
def prefixEnd_3480421 : Nat := 4983230072969 + 3 ^ 40 * 3480421 * 2
def baseEnd_3480421 : Nat := 1787128853002032570531341

theorem tailTrace_3480421 : CollatzResearch.WordTrace tailWord_3480421 prefixEnd_3480421 1787128853002032570531341 := by
  unfold tailWord_3480421
  simp only [CollatzResearch.WordTrace]
  refine ⟨126941382524036600428625117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84627588349357733619083411 126941382524036600428625117)
  ·
    refine ⟨47603018446513725160734419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126941382524036600428625117 47603018446513725160734419)
    ·
      refine ⟨71404527669770587741101629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47603018446513725160734419 71404527669770587741101629)
      ·
        refine ⟨26776697876163970402913111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71404527669770587741101629 26776697876163970402913111)
        ·
          refine ⟨40165046814245955604369667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26776697876163970402913111 40165046814245955604369667)
          ·
            refine ⟨60247570221368933406554501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40165046814245955604369667 60247570221368933406554501)
            ·
              refine ⟨11296419416506675013728969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60247570221368933406554501 11296419416506675013728969)
              ·
                refine ⟨8472314562380006260296727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11296419416506675013728969 8472314562380006260296727)
                ·
                  refine ⟨12708471843570009390445091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8472314562380006260296727 12708471843570009390445091)
                  ·
                    refine ⟨19062707765355014085667637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12708471843570009390445091 19062707765355014085667637)
                    ·
                      refine ⟨1787128853002032570531341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19062707765355014085667637 1787128853002032570531341)
                      ·
                        rfl

theorem cell23_3480421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_3480421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480421 prefixEnd_3480421 := by exact prefixLift 3480421
  have htrace : WordTrace (prefixWord ++ tailWord_3480421) baseStart_3480421 baseEnd_3480421 := by
    simpa [prefixWord, tailWord_3480421, baseEnd_3480421] using wordTrace_append hprefix tailTrace_3480421
  have hstable : (prefixWord ++ tailWord_3480421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480421).length < 2 ^ (prefixWord ++ tailWord_3480421).sum := by decide
  have hdescent : baseEnd_3480421 < baseStart_3480421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480428 : List Nat := [2, 2, 1, 1, 4, 1, 3, 3, 2, 4]
def baseStart_3480428 : Nat := 118140960795 + 3480428 * 2 ^ 59
def prefixEnd_3480428 : Nat := 4983230072969 + 3 ^ 40 * 3480428 * 2
def baseEnd_3480428 : Nat := 595710815788871347714603

theorem tailTrace_3480428 : CollatzResearch.WordTrace tailWord_3480428 prefixEnd_3480428 595710815788871347714603 := by
  unfold tailWord_3480428
  simp only [CollatzResearch.WordTrace]
  refine ⟨63470818917505620312064969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84627758556674160416086625 63470818917505620312064969)
  ·
    refine ⟨47603114188129215234048727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63470818917505620312064969 47603114188129215234048727)
    ·
      refine ⟨71404671282193822851073091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47603114188129215234048727 71404671282193822851073091)
      ·
        refine ⟨107107006923290734276609637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71404671282193822851073091 107107006923290734276609637)
        ·
          refine ⟨20082563798117012676864307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107107006923290734276609637 20082563798117012676864307)
          ·
            refine ⟨30123845697175519015296461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20082563798117012676864307 30123845697175519015296461)
            ·
              refine ⟨11296442136440819630736173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30123845697175519015296461 11296442136440819630736173)
              ·
                refine ⟨4236165801165307361526065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11296442136440819630736173 4236165801165307361526065)
                ·
                  refine ⟨3177124350873980521144549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4236165801165307361526065 3177124350873980521144549)
                  ·
                    refine ⟨595710815788871347714603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3177124350873980521144549 595710815788871347714603)
                    ·
                      rfl

theorem cell23_3480428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 4].length) (baseStart_3480428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480428 prefixEnd_3480428 := by exact prefixLift 3480428
  have htrace : WordTrace (prefixWord ++ tailWord_3480428) baseStart_3480428 baseEnd_3480428 := by
    simpa [prefixWord, tailWord_3480428, baseEnd_3480428] using wordTrace_append hprefix tailTrace_3480428
  have hstable : (prefixWord ++ tailWord_3480428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480428).length < 2 ^ (prefixWord ++ tailWord_3480428).sum := by decide
  have hdescent : baseEnd_3480428 < baseStart_3480428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480452 : List Nat := [2, 3, 2, 1, 1, 1, 1, 7, 1, 2, 2]
def baseStart_3480452 : Nat := 118140960795 + 3480452 * 2 ^ 59
def prefixEnd_3480452 : Nat := 4983230072969 + 3 ^ 40 * 3480452 * 2
def baseEnd_3480452 : Nat := 1787144770902321949243699

theorem tailTrace_3480452 : CollatzResearch.WordTrace tailWord_3480452 prefixEnd_3480452 1787144770902321949243699 := by
  unfold tailWord_3480452
  simp only [CollatzResearch.WordTrace]
  refine ⟨63471256593462146361501805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84628342124616195148669073 63471256593462146361501805)
  ·
    refine ⟨23801721222548304885563177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63471256593462146361501805 23801721222548304885563177)
    ·
      refine ⟨17851290916911228664172383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23801721222548304885563177 17851290916911228664172383)
      ·
        refine ⟨26776936375366842996258575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17851290916911228664172383 26776936375366842996258575)
        ·
          refine ⟨40165404563050264494387863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26776936375366842996258575 40165404563050264494387863)
          ·
            refine ⟨60248106844575396741581795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40165404563050264494387863 60248106844575396741581795)
            ·
              refine ⟨90372160266863095112372693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60248106844575396741581795 90372160266863095112372693)
              ·
                refine ⟨2118097506254603791696235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 90372160266863095112372693 2118097506254603791696235)
                ·
                  refine ⟨3177146259381905687544353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2118097506254603791696235 3177146259381905687544353)
                  ·
                    refine ⟨2382859694536429265658265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3177146259381905687544353 2382859694536429265658265)
                    ·
                      refine ⟨1787144770902321949243699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2382859694536429265658265 1787144770902321949243699)
                      ·
                        rfl

theorem cell23_3480452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_3480452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480452 prefixEnd_3480452 := by exact prefixLift 3480452
  have htrace : WordTrace (prefixWord ++ tailWord_3480452) baseStart_3480452 baseEnd_3480452 := by
    simpa [prefixWord, tailWord_3480452, baseEnd_3480452] using wordTrace_append hprefix tailTrace_3480452
  have hstable : (prefixWord ++ tailWord_3480452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480452).length < 2 ^ (prefixWord ++ tailWord_3480452).sum := by decide
  have hdescent : baseEnd_3480452 < baseStart_3480452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480468 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 3, 3, 3]
def baseStart_3480468 : Nat := 118140960795 + 3480468 * 2 ^ 59
def prefixEnd_3480468 : Nat := 4983230072969 + 3 ^ 40 * 3480468 * 2
def baseEnd_3480468 : Nat := 1787152986592793886643625

theorem tailTrace_3480468 : CollatzResearch.WordTrace tailWord_3480468 prefixEnd_3480468 1787152986592793886643625 := by
  unfold tailWord_3480468
  simp only [CollatzResearch.WordTrace]
  refine ⟨63471548377433163727793029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84628731169910884970390705 63471548377433163727793029)
  ·
    refine ⟨11900915320768718198961193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63471548377433163727793029 11900915320768718198961193)
    ·
      refine ⟨8925686490576538649220895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11900915320768718198961193 8925686490576538649220895)
      ·
        refine ⟨13388529735864807973831343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8925686490576538649220895 13388529735864807973831343)
        ·
          refine ⟨20082794603797211960747015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13388529735864807973831343 20082794603797211960747015)
          ·
            refine ⟨30124191905695817941120523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20082794603797211960747015 30124191905695817941120523)
            ·
              refine ⟨45186287858543726911680785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30124191905695817941120523 45186287858543726911680785)
              ·
                refine ⟨33889715893907795183760589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45186287858543726911680785 33889715893907795183760589)
                ·
                  refine ⟨12708643460215423193910221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33889715893907795183760589 12708643460215423193910221)
                  ·
                    refine ⟨4765741297580783697716333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12708643460215423193910221 4765741297580783697716333)
                    ·
                      refine ⟨1787152986592793886643625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4765741297580783697716333 1787152986592793886643625)
                      ·
                        rfl

theorem cell23_3480468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_3480468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480468 prefixEnd_3480468 := by exact prefixLift 3480468
  have htrace : WordTrace (prefixWord ++ tailWord_3480468) baseStart_3480468 baseEnd_3480468 := by
    simpa [prefixWord, tailWord_3480468, baseEnd_3480468] using wordTrace_append hprefix tailTrace_3480468
  have hstable : (prefixWord ++ tailWord_3480468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480468).length < 2 ^ (prefixWord ++ tailWord_3480468).sum := by decide
  have hdescent : baseEnd_3480468 < baseStart_3480468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480469 : List Nat := [1, 3, 2, 1, 1, 4, 4, 2, 1, 2, 2]
def baseStart_3480469 : Nat := 118140960795 + 3480469 * 2 ^ 59
def prefixEnd_3480469 : Nat := 4983230072969 + 3 ^ 40 * 3480469 * 2
def baseEnd_3480469 : Nat := 1787153500073448382731121

theorem tailTrace_3480469 : CollatzResearch.WordTrace tailWord_3480469 prefixEnd_3480469 1787153500073448382731121 := by
  unfold tailWord_3480469
  simp only [CollatzResearch.WordTrace]
  refine ⟨126943133227862704626372461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84628755485241803084248307 126943133227862704626372461)
  ·
    refine ⟨47603674960448514234889673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126943133227862704626372461 47603674960448514234889673)
    ·
      refine ⟨35702756220336385676167255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47603674960448514234889673 35702756220336385676167255)
      ·
        refine ⟨53554134330504578514250883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35702756220336385676167255 53554134330504578514250883)
        ·
          refine ⟨80331201495756867771376325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53554134330504578514250883 80331201495756867771376325)
          ·
            refine ⟨15062100280454412707133061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80331201495756867771376325 15062100280454412707133061)
            ·
              refine ⟨2824143802585202382587449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15062100280454412707133061 2824143802585202382587449)
              ·
                refine ⟨2118107851938901786940587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2824143802585202382587449 2118107851938901786940587)
                ·
                  refine ⟨3177161777908352680410881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2118107851938901786940587 3177161777908352680410881)
                  ·
                    refine ⟨2382871333431264510308161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3177161777908352680410881 2382871333431264510308161)
                    ·
                      refine ⟨1787153500073448382731121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2382871333431264510308161 1787153500073448382731121)
                      ·
                        rfl

theorem cell23_3480469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 2, 1, 2, 2].length) (baseStart_3480469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480469 prefixEnd_3480469 := by exact prefixLift 3480469
  have htrace : WordTrace (prefixWord ++ tailWord_3480469) baseStart_3480469 baseEnd_3480469 := by
    simpa [prefixWord, tailWord_3480469, baseEnd_3480469] using wordTrace_append hprefix tailTrace_3480469
  have hstable : (prefixWord ++ tailWord_3480469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480469).length < 2 ^ (prefixWord ++ tailWord_3480469).sum := by decide
  have hdescent : baseEnd_3480469 < baseStart_3480469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480501 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 1, 8]
def baseStart_3480501 : Nat := 118140960795 + 3480501 * 2 ^ 59
def prefixEnd_3480501 : Nat := 4983230072969 + 3 ^ 40 * 3480501 * 2
def baseEnd_3480501 : Nat := 595723310484797419176991

theorem tailTrace_3480501 : CollatzResearch.WordTrace tailWord_3480501 prefixEnd_3480501 595723310484797419176991 := by
  unfold tailWord_3480501
  simp only [CollatzResearch.WordTrace]
  refine ⟨126944300363746774091537357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84629533575831182727691571 126944300363746774091537357)
  ·
    refine ⟨47604112636405040284326509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126944300363746774091537357 47604112636405040284326509)
    ·
      refine ⟨17851542238651890106622441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47604112636405040284326509 17851542238651890106622441)
      ·
        refine ⟨13388656678988917579966831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17851542238651890106622441 13388656678988917579966831)
        ·
          refine ⟨20082985018483376369950247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13388656678988917579966831 20082985018483376369950247)
          ·
            refine ⟨30124477527725064554925371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20082985018483376369950247 30124477527725064554925371)
            ·
              refine ⟨45186716291587596832388057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30124477527725064554925371 45186716291587596832388057)
              ·
                refine ⟨33890037218690697624291043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45186716291587596832388057 33890037218690697624291043)
                ·
                  refine ⟨50835055828036046436436565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33890037218690697624291043 50835055828036046436436565)
                  ·
                    refine ⟨595723310484797419176991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50835055828036046436436565 595723310484797419176991)
                    ·
                      rfl

theorem cell23_3480501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_3480501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480501 prefixEnd_3480501 := by exact prefixLift 3480501
  have htrace : WordTrace (prefixWord ++ tailWord_3480501) baseStart_3480501 baseEnd_3480501 := by
    simpa [prefixWord, tailWord_3480501, baseEnd_3480501] using wordTrace_append hprefix tailTrace_3480501
  have hstable : (prefixWord ++ tailWord_3480501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480501).length < 2 ^ (prefixWord ++ tailWord_3480501).sum := by decide
  have hdescent : baseEnd_3480501 < baseStart_3480501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480511 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 1, 6, 3]
def baseStart_3480511 : Nat := 118140960795 + 3480511 * 2 ^ 59
def prefixEnd_3480511 : Nat := 4983230072969 + 3 ^ 40 * 3480511 * 2
def baseEnd_3480511 : Nat := 1787175066260937218405927

theorem tailTrace_3480511 : CollatzResearch.WordTrace tailWord_3480511 prefixEnd_3480511 1787175066260937218405927 := by
  unfold tailWord_3480511
  simp only [CollatzResearch.WordTrace]
  refine ⟨126944665093710545799401387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84629776729140363866267591 126944665093710545799401387)
  ·
    refine ⟨190416997640565818699102081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126944665093710545799401387 190416997640565818699102081)
    ·
      refine ⟨142812748230424364024326561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190416997640565818699102081 142812748230424364024326561)
      ·
        refine ⟨107109561172818273018244921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142812748230424364024326561 107109561172818273018244921)
        ·
          refine ⟨80332170879613704763683691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107109561172818273018244921 80332170879613704763683691)
          ·
            refine ⟨120498256319420557145525537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80332170879613704763683691 120498256319420557145525537)
            ·
              refine ⟨90373692239565417859144153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120498256319420557145525537 90373692239565417859144153)
              ·
                refine ⟨67780269179674063394358115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90373692239565417859144153 67780269179674063394358115)
                ·
                  refine ⟨101670403769511095091537173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67780269179674063394358115 101670403769511095091537173)
                  ·
                    refine ⟨4765800176695832582415805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101670403769511095091537173 4765800176695832582415805)
                    ·
                      refine ⟨1787175066260937218405927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4765800176695832582415805 1787175066260937218405927)
                      ·
                        rfl

theorem cell23_3480511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 6, 3].length) (baseStart_3480511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480511 prefixEnd_3480511 := by exact prefixLift 3480511
  have htrace : WordTrace (prefixWord ++ tailWord_3480511) baseStart_3480511 baseEnd_3480511 := by
    simpa [prefixWord, tailWord_3480511, baseEnd_3480511] using wordTrace_append hprefix tailTrace_3480511
  have hstable : (prefixWord ++ tailWord_3480511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480511).length < 2 ^ (prefixWord ++ tailWord_3480511).sum := by decide
  have hdescent : baseEnd_3480511 < baseStart_3480511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480512 : List Nat := [2, 1, 1, 2, 3, 3, 4, 1, 1, 3, 2]
def baseStart_3480512 : Nat := 118140960795 + 3480512 * 2 ^ 59
def prefixEnd_3480512 : Nat := 4983230072969 + 3 ^ 40 * 3480512 * 2
def baseEnd_3480512 : Nat := 1787175579741591714493423

theorem tailTrace_3480512 : CollatzResearch.WordTrace tailWord_3480512 prefixEnd_3480512 1787175579741591714493423 := by
  unfold tailWord_3480512
  simp only [CollatzResearch.WordTrace]
  refine ⟨63472350783353461485093895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84629801044471281980125193 63472350783353461485093895)
  ·
    refine ⟨95208526175030192227640843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63472350783353461485093895 95208526175030192227640843)
    ·
      refine ⟨142812789262545288341461265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95208526175030192227640843 142812789262545288341461265)
      ·
        refine ⟨107109591946908966256095949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142812789262545288341461265 107109591946908966256095949)
        ·
          refine ⟨40166096980090862346035981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107109591946908966256095949 40166096980090862346035981)
          ·
            refine ⟨15062286367534073379763493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40166096980090862346035981 15062286367534073379763493)
            ·
              refine ⟨2824178693912638758705655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15062286367534073379763493 2824178693912638758705655)
              ·
                refine ⟨4236268040868958138058483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2824178693912638758705655 4236268040868958138058483)
                ·
                  refine ⟨6354402061303437207087725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4236268040868958138058483 6354402061303437207087725)
                  ·
                    refine ⟨2382900772988788952657897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6354402061303437207087725 2382900772988788952657897)
                    ·
                      refine ⟨1787175579741591714493423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2382900772988788952657897 1787175579741591714493423)
                      ·
                        rfl

theorem cell23_3480512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 1, 3, 2].length) (baseStart_3480512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480512 prefixEnd_3480512 := by exact prefixLift 3480512
  have htrace : WordTrace (prefixWord ++ tailWord_3480512) baseStart_3480512 baseEnd_3480512 := by
    simpa [prefixWord, tailWord_3480512, baseEnd_3480512] using wordTrace_append hprefix tailTrace_3480512
  have hstable : (prefixWord ++ tailWord_3480512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480512).length < 2 ^ (prefixWord ++ tailWord_3480512).sum := by decide
  have hdescent : baseEnd_3480512 < baseStart_3480512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480538 : List Nat := [3, 1, 1, 2, 4, 1, 2, 1, 2, 2, 4]
def baseStart_3480538 : Nat := 118140960795 + 3480538 * 2 ^ 59
def prefixEnd_3480538 : Nat := 4983230072969 + 3 ^ 40 * 3480538 * 2
def baseEnd_3480538 : Nat := 1787188930238608612768303

theorem tailTrace_3480538 : CollatzResearch.WordTrace tailWord_3480538 prefixEnd_3480538 1787188930238608612768303 := by
  unfold tailWord_3480538
  simp only [CollatzResearch.WordTrace]
  refine ⟨31736412466153182352658567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84630433243075152940422845 31736412466153182352658567)
  ·
    refine ⟨47604618699229773528987851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31736412466153182352658567 47604618699229773528987851)
    ·
      refine ⟨71406928048844660293481777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47604618699229773528987851 71406928048844660293481777)
      ·
        refine ⟨53555196036633495220111333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71406928048844660293481777 53555196036633495220111333)
        ·
          refine ⟨10041599256868780353770875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53555196036633495220111333 10041599256868780353770875)
          ·
            refine ⟨15062398885303170530656313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10041599256868780353770875 15062398885303170530656313)
            ·
              refine ⟨11296799163977377897992235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15062398885303170530656313 11296799163977377897992235)
              ·
                refine ⟨16945198745966066846988353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11296799163977377897992235 16945198745966066846988353)
                ·
                  refine ⟨12708899059474550135241265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16945198745966066846988353 12708899059474550135241265)
                  ·
                    refine ⟨9531674294605912601430949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12708899059474550135241265 9531674294605912601430949)
                    ·
                      refine ⟨1787188930238608612768303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9531674294605912601430949 1787188930238608612768303)
                      ·
                        rfl

theorem cell23_3480538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_3480538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480538 prefixEnd_3480538 := by exact prefixLift 3480538
  have htrace : WordTrace (prefixWord ++ tailWord_3480538) baseStart_3480538 baseEnd_3480538 := by
    simpa [prefixWord, tailWord_3480538, baseEnd_3480538] using wordTrace_append hprefix tailTrace_3480538
  have hstable : (prefixWord ++ tailWord_3480538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480538).length < 2 ^ (prefixWord ++ tailWord_3480538).sum := by decide
  have hdescent : baseEnd_3480538 < baseStart_3480538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480568 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 1, 7, 2]
def baseStart_3480568 : Nat := 118140960795 + 3480568 * 2 ^ 59
def prefixEnd_3480568 : Nat := 4983230072969 + 3 ^ 40 * 3480568 * 2
def baseEnd_3480568 : Nat := 1787204334658243495393165

theorem tailTrace_3480568 : CollatzResearch.WordTrace tailWord_3480568 prefixEnd_3480568 1787204334658243495393165 := by
  unfold tailWord_3480568
  simp only [CollatzResearch.WordTrace]
  refine ⟨63473372027252022267113179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84631162703002696356150905 63473372027252022267113179)
  ·
    refine ⟨95210058040878033400669769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63473372027252022267113179 95210058040878033400669769)
    ·
      refine ⟨71407543530658525050502327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95210058040878033400669769 71407543530658525050502327)
      ·
        refine ⟨107111315295987787575753491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71407543530658525050502327 107111315295987787575753491)
        ·
          refine ⟨160666972943981681363630237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107111315295987787575753491 160666972943981681363630237)
          ·
            refine ⟨60250114853993130511361339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160666972943981681363630237 60250114853993130511361339)
            ·
              refine ⟨90375172280989695767042009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60250114853993130511361339 90375172280989695767042009)
              ·
                refine ⟨67781379210742271825281507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90375172280989695767042009 67781379210742271825281507)
                ·
                  refine ⟨101672068816113407737922261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67781379210742271825281507 101672068816113407737922261)
                  ·
                    refine ⟨2382939112877657993857553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 101672068816113407737922261 2382939112877657993857553)
                    ·
                      refine ⟨1787204334658243495393165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2382939112877657993857553 1787204334658243495393165)
                      ·
                        rfl

theorem cell23_3480568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 7, 2].length) (baseStart_3480568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480568 prefixEnd_3480568 := by exact prefixLift 3480568
  have htrace : WordTrace (prefixWord ++ tailWord_3480568) baseStart_3480568 baseEnd_3480568 := by
    simpa [prefixWord, tailWord_3480568, baseEnd_3480568] using wordTrace_append hprefix tailTrace_3480568
  have hstable : (prefixWord ++ tailWord_3480568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480568).length < 2 ^ (prefixWord ++ tailWord_3480568).sum := by decide
  have hdescent : baseEnd_3480568 < baseStart_3480568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480571 : List Nat := [1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 5]
def baseStart_3480571 : Nat := 118140960795 + 3480571 * 2 ^ 59
def prefixEnd_3480571 : Nat := 4983230072969 + 3 ^ 40 * 3480571 * 2
def baseEnd_3480571 : Nat := 1787205875100206983655651

theorem tailTrace_3480571 : CollatzResearch.WordTrace tailWord_3480571 prefixEnd_3480571 1787205875100206983655651 := by
  unfold tailWord_3480571
  simp only [CollatzResearch.WordTrace]
  refine ⟨126946853473493176046585567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84631235648995450697723711 126946853473493176046585567)
  ·
    refine ⟨190420280210239764069878351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126946853473493176046585567 190420280210239764069878351)
    ·
      refine ⟨285630420315359646104817527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190420280210239764069878351 285630420315359646104817527)
      ·
        refine ⟨428445630473039469157226291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285630420315359646104817527 428445630473039469157226291)
        ·
          refine ⟨642668445709559203735839437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428445630473039469157226291 642668445709559203735839437)
          ·
            refine ⟨241000667141084701400939789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 642668445709559203735839437 241000667141084701400939789)
            ·
              refine ⟨90375250177906763025352421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241000667141084701400939789 90375250177906763025352421)
              ·
                refine ⟨16945359408357518067253579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90375250177906763025352421 16945359408357518067253579)
                ·
                  refine ⟨25418039112536277100880369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16945359408357518067253579 25418039112536277100880369)
                  ·
                    refine ⟨19063529334402207825660277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25418039112536277100880369 19063529334402207825660277)
                    ·
                      refine ⟨1787205875100206983655651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19063529334402207825660277 1787205875100206983655651)
                      ·
                        rfl

theorem cell23_3480571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 5].length) (baseStart_3480571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480571 prefixEnd_3480571 := by exact prefixLift 3480571
  have htrace : WordTrace (prefixWord ++ tailWord_3480571) baseStart_3480571 baseEnd_3480571 := by
    simpa [prefixWord, tailWord_3480571, baseEnd_3480571] using wordTrace_append hprefix tailTrace_3480571
  have hstable : (prefixWord ++ tailWord_3480571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480571).length < 2 ^ (prefixWord ++ tailWord_3480571).sum := by decide
  have hdescent : baseEnd_3480571 < baseStart_3480571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480588 : List Nat := [2, 2, 1, 2, 3, 3, 1, 1, 1, 2, 5]
def baseStart_3480588 : Nat := 118140960795 + 3480588 * 2 ^ 59
def prefixEnd_3480588 : Nat := 4983230072969 + 3 ^ 40 * 3480588 * 2
def baseEnd_3480588 : Nat := 1787214604271333417143073

theorem tailTrace_3480588 : CollatzResearch.WordTrace tailWord_3480588 prefixEnd_3480588 1787214604271333417143073 := by
  unfold tailWord_3480588
  simp only [CollatzResearch.WordTrace]
  refine ⟨63473736757215793974977209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84631649009621058633302945 63473736757215793974977209)
  ·
    refine ⟨47605302567911845481232907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63473736757215793974977209 47605302567911845481232907)
    ·
      refine ⟨71407953851867768221849361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47605302567911845481232907 71407953851867768221849361)
      ·
        refine ⟨53555965388900826166387021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71407953851867768221849361 53555965388900826166387021)
        ·
          refine ⟨20083487020837809812395133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53555965388900826166387021 20083487020837809812395133)
          ·
            refine ⟨7531307632814178679648175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20083487020837809812395133 7531307632814178679648175)
            ·
              refine ⟨11296961449221268019472263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7531307632814178679648175 11296961449221268019472263)
              ·
                refine ⟨16945442173831902029208395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11296961449221268019472263 16945442173831902029208395)
                ·
                  refine ⟨25418163260747853043812593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16945442173831902029208395 25418163260747853043812593)
                  ·
                    refine ⟨19063622445560889782859445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25418163260747853043812593 19063622445560889782859445)
                    ·
                      refine ⟨1787214604271333417143073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19063622445560889782859445 1787214604271333417143073)
                      ·
                        rfl

theorem cell23_3480588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_3480588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480588 prefixEnd_3480588 := by exact prefixLift 3480588
  have htrace : WordTrace (prefixWord ++ tailWord_3480588) baseStart_3480588 baseEnd_3480588 := by
    simpa [prefixWord, tailWord_3480588, baseEnd_3480588] using wordTrace_append hprefix tailTrace_3480588
  have hstable : (prefixWord ++ tailWord_3480588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480588).length < 2 ^ (prefixWord ++ tailWord_3480588).sum := by decide
  have hdescent : baseEnd_3480588 < baseStart_3480588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480651 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 1, 11]
def baseStart_3480651 : Nat := 118140960795 + 3480651 * 2 ^ 59
def prefixEnd_3480651 : Nat := 4983230072969 + 3 ^ 40 * 3480651 * 2
def baseEnd_3480651 : Nat := 595748984517522223551761

theorem tailTrace_3480651 : CollatzResearch.WordTrace tailWord_3480651 prefixEnd_3480651 595748984517522223551761 := by
  unfold tailWord_3480651
  simp only [CollatzResearch.WordTrace]
  refine ⟨126949771313203349709497807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84633180875468899806331871 126949771313203349709497807)
  ·
    refine ⟨190424656969805024564246711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126949771313203349709497807 190424656969805024564246711)
    ·
      refine ⟨285636985454707536846370067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190424656969805024564246711 285636985454707536846370067)
      ·
        refine ⟨428455478182061305269555101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285636985454707536846370067 428455478182061305269555101)
        ·
          refine ⟨160670804318272989476083163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 428455478182061305269555101 160670804318272989476083163)
          ·
            refine ⟨241006206477409484214124745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160670804318272989476083163 241006206477409484214124745)
            ·
              refine ⟨180754654858057113160593559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241006206477409484214124745 180754654858057113160593559)
              ·
                refine ⟨271131982287085669740890339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180754654858057113160593559 271131982287085669740890339)
                ·
                  refine ⟨406697973430628504611335509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271131982287085669740890339 406697973430628504611335509)
                  ·
                    refine ⟨595748984517522223551761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 406697973430628504611335509 595748984517522223551761)
                    ·
                      rfl

theorem cell23_3480651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 11].length) (baseStart_3480651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480651 prefixEnd_3480651 := by exact prefixLift 3480651
  have htrace : WordTrace (prefixWord ++ tailWord_3480651) baseStart_3480651 baseEnd_3480651 := by
    simpa [prefixWord, tailWord_3480651, baseEnd_3480651] using wordTrace_append hprefix tailTrace_3480651
  have hstable : (prefixWord ++ tailWord_3480651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480651).length < 2 ^ (prefixWord ++ tailWord_3480651).sum := by decide
  have hdescent : baseEnd_3480651 < baseStart_3480651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480715 : List Nat := [1, 1, 1, 1, 4, 1, 1, 7, 2, 4]
def baseStart_3480715 : Nat := 118140960795 + 3480715 * 2 ^ 59
def prefixEnd_3480715 : Nat := 4983230072969 + 3 ^ 40 * 3480715 * 2
def baseEnd_3480715 : Nat := 595759938771484806751663

theorem tailTrace_3480715 : CollatzResearch.WordTrace tailWord_3480715 prefixEnd_3480715 595759938771484806751663 := by
  unfold tailWord_3480715
  simp only [CollatzResearch.WordTrace]
  refine ⟨126952105584971488639827599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84634737056647659093218399 126952105584971488639827599)
  ·
    refine ⟨190428158377457232959741399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126952105584971488639827599 190428158377457232959741399)
    ·
      refine ⟨285642237566185849439612099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190428158377457232959741399 285642237566185849439612099)
      ·
        refine ⟨428463356349278774159418149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285642237566185849439612099 428463356349278774159418149)
        ·
          refine ⟨80336879315489770154890903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 428463356349278774159418149 80336879315489770154890903)
          ·
            refine ⟨120505318973234655232336355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80336879315489770154890903 120505318973234655232336355)
            ·
              refine ⟨180757978459851982848504533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120505318973234655232336355 180757978459851982848504533)
              ·
                refine ⟨4236515120152780848011825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 180757978459851982848504533 4236515120152780848011825)
                ·
                  refine ⟨3177386340114585636008869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4236515120152780848011825 3177386340114585636008869)
                  ·
                    refine ⟨595759938771484806751663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3177386340114585636008869 595759938771484806751663)
                    ·
                      rfl

theorem cell23_3480715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 2, 4].length) (baseStart_3480715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480715 prefixEnd_3480715 := by exact prefixLift 3480715
  have htrace : WordTrace (prefixWord ++ tailWord_3480715) baseStart_3480715 baseEnd_3480715 := by
    simpa [prefixWord, tailWord_3480715, baseEnd_3480715] using wordTrace_append hprefix tailTrace_3480715
  have hstable : (prefixWord ++ tailWord_3480715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480715).length < 2 ^ (prefixWord ++ tailWord_3480715).sum := by decide
  have hdescent : baseEnd_3480715 < baseStart_3480715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480722 : List Nat := [3, 2, 3, 1, 1, 2, 1, 4, 1, 1, 4]
def baseStart_3480722 : Nat := 118140960795 + 3480722 * 2 ^ 59
def prefixEnd_3480722 : Nat := 4983230072969 + 3 ^ 40 * 3480722 * 2
def baseEnd_3480722 : Nat := 1787283410679035892867457

theorem tailTrace_3480722 : CollatzResearch.WordTrace tailWord_3480722 prefixEnd_3480722 1787283410679035892867457 := by
  unfold tailWord_3480722
  simp only [CollatzResearch.WordTrace]
  refine ⟨31738090223986532208833105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84634907263964085890221613 31738090223986532208833105)
  ·
    refine ⟨23803567667989899156624829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31738090223986532208833105 23803567667989899156624829)
    ·
      refine ⟨8926337875496212183734311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23803567667989899156624829 8926337875496212183734311)
      ·
        refine ⟨13389506813244318275601467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8926337875496212183734311 13389506813244318275601467)
        ·
          refine ⟨20084260219866477413402201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13389506813244318275601467 20084260219866477413402201)
          ·
            refine ⟨15063195164899858060051651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20084260219866477413402201 15063195164899858060051651)
            ·
              refine ⟨22594792747349787090077477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15063195164899858060051651 22594792747349787090077477)
              ·
                refine ⟨4236523640128085079389527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22594792747349787090077477 4236523640128085079389527)
                ·
                  refine ⟨6354785460192127619084291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4236523640128085079389527 6354785460192127619084291)
                  ·
                    refine ⟨9532178190288191428626437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6354785460192127619084291 9532178190288191428626437)
                    ·
                      refine ⟨1787283410679035892867457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9532178190288191428626437 1787283410679035892867457)
                      ·
                        rfl

theorem cell23_3480722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_3480722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480722 prefixEnd_3480722 := by exact prefixLift 3480722
  have htrace : WordTrace (prefixWord ++ tailWord_3480722) baseStart_3480722 baseEnd_3480722 := by
    simpa [prefixWord, tailWord_3480722, baseEnd_3480722] using wordTrace_append hprefix tailTrace_3480722
  have hstable : (prefixWord ++ tailWord_3480722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480722).length < 2 ^ (prefixWord ++ tailWord_3480722).sum := by decide
  have hdescent : baseEnd_3480722 < baseStart_3480722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480766 : List Nat := [4, 2, 1, 1, 3, 3, 2, 1, 2, 4]
def baseStart_3480766 : Nat := 118140960795 + 3480766 * 2 ^ 59
def prefixEnd_3480766 : Nat := 4983230072969 + 3 ^ 40 * 3480766 * 2
def baseEnd_3480766 : Nat := 595768667942611240239085

theorem tailTrace_3480766 : CollatzResearch.WordTrace tailWord_3480766 prefixEnd_3480766 595768667942611240239085 := by
  unfold tailWord_3480766
  simp only [CollatzResearch.WordTrace]
  refine ⟨15869245713473340543741769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84635977138524482899956101 15869245713473340543741769)
  ·
    refine ⟨11901934285105005407806327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15869245713473340543741769 11901934285105005407806327)
    ·
      refine ⟨17852901427657508111709491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11901934285105005407806327 17852901427657508111709491)
      ·
        refine ⟨26779352141486262167564237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17852901427657508111709491 26779352141486262167564237)
        ·
          refine ⟨10042257053057348312836589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26779352141486262167564237 10042257053057348312836589)
          ·
            refine ⟨3765846394896505617313721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10042257053057348312836589 3765846394896505617313721)
            ·
              refine ⟨2824384796172379212985291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3765846394896505617313721 2824384796172379212985291)
              ·
                refine ⟨4236577194258568819477937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2824384796172379212985291 4236577194258568819477937)
                ·
                  refine ⟨3177432895693926614608453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4236577194258568819477937 3177432895693926614608453)
                  ·
                    refine ⟨595768667942611240239085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3177432895693926614608453 595768667942611240239085)
                    ·
                      rfl

theorem cell23_3480766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_3480766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480766 prefixEnd_3480766 := by exact prefixLift 3480766
  have htrace : WordTrace (prefixWord ++ tailWord_3480766) baseStart_3480766 baseEnd_3480766 := by
    simpa [prefixWord, tailWord_3480766, baseEnd_3480766] using wordTrace_append hprefix tailTrace_3480766
  have hstable : (prefixWord ++ tailWord_3480766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480766).length < 2 ^ (prefixWord ++ tailWord_3480766).sum := by decide
  have hdescent : baseEnd_3480766 < baseStart_3480766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480795 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 2, 8, 2]
def baseStart_3480795 : Nat := 118140960795 + 3480795 * 2 ^ 59
def prefixEnd_3480795 : Nat := 4983230072969 + 3 ^ 40 * 3480795 * 2
def baseEnd_3480795 : Nat := 1787320894766814107254621

theorem tailTrace_3480795 : CollatzResearch.WordTrace tailWord_3480795 prefixEnd_3480795 1787320894766814107254621 := by
  unfold tailWord_3480795
  simp only [CollatzResearch.WordTrace]
  refine ⟨126955023424681662302739839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84636682283121108201826559 126955023424681662302739839)
  ·
    refine ⟨190432535137022493454109759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126955023424681662302739839 190432535137022493454109759)
    ·
      refine ⟨285648802705533740181164639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190432535137022493454109759 285648802705533740181164639)
      ·
        refine ⟨428473204058300610271746959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285648802705533740181164639 428473204058300610271746959)
        ·
          refine ⟨642709806087450915407620439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428473204058300610271746959 642709806087450915407620439)
          ·
            refine ⟨964064709131176373111430659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642709806087450915407620439 964064709131176373111430659)
            ·
              refine ⟨1446097063696764559667145989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 964064709131176373111430659 1446097063696764559667145989)
              ·
                refine ⟨271143199443143354937589873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1446097063696764559667145989 271143199443143354937589873)
                ·
                  refine ⟨203357399582357516203192405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 271143199443143354937589873 203357399582357516203192405)
                  ·
                    refine ⟨2383094526355752143006161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 203357399582357516203192405 2383094526355752143006161)
                    ·
                      refine ⟨1787320894766814107254621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2383094526355752143006161 1787320894766814107254621)
                      ·
                        rfl

theorem cell23_3480795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 8, 2].length) (baseStart_3480795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480795 prefixEnd_3480795 := by exact prefixLift 3480795
  have htrace : WordTrace (prefixWord ++ tailWord_3480795) baseStart_3480795 baseEnd_3480795 := by
    simpa [prefixWord, tailWord_3480795, baseEnd_3480795] using wordTrace_append hprefix tailTrace_3480795
  have hstable : (prefixWord ++ tailWord_3480795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480795).length < 2 ^ (prefixWord ++ tailWord_3480795).sum := by decide
  have hdescent : baseEnd_3480795 < baseStart_3480795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480807 : List Nat := [1, 1, 5, 3, 3, 1, 2, 2, 1, 2, 2]
def baseStart_3480807 : Nat := 118140960795 + 3480807 * 2 ^ 59
def prefixEnd_3480807 : Nat := 4983230072969 + 3 ^ 40 * 3480807 * 2
def baseEnd_3480807 : Nat := 1787327056534668060304567

theorem tailTrace_3480807 : CollatzResearch.WordTrace tailWord_3480807 prefixEnd_3480807 1787327056534668060304567 := by
  unfold tailWord_3480807
  simp only [CollatzResearch.WordTrace]
  refine ⟨126955461100638188352176675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84636974067092125568117783 126955461100638188352176675)
  ·
    refine ⟨190433191650957282528265013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126955461100638188352176675 190433191650957282528265013)
    ·
      refine ⟨17853111717277245237024845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 190433191650957282528265013 17853111717277245237024845)
      ·
        refine ⟨6694916893978966963884317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17853111717277245237024845 6694916893978966963884317)
        ·
          refine ⟨2510593835242112611456619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6694916893978966963884317 2510593835242112611456619)
          ·
            refine ⟨3765890752863168917184929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2510593835242112611456619 3765890752863168917184929)
            ·
              refine ⟨2824418064647376687888697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3765890752863168917184929 2824418064647376687888697)
              ·
                refine ⟨2118313548485532515916523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2824418064647376687888697 2118313548485532515916523)
                ·
                  refine ⟨3177470322728298773874785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2118313548485532515916523 3177470322728298773874785)
                  ·
                    refine ⟨2383102742046224080406089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3177470322728298773874785 2383102742046224080406089)
                    ·
                      refine ⟨1787327056534668060304567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2383102742046224080406089 1787327056534668060304567)
                      ·
                        rfl

theorem cell23_3480807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_3480807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480807 prefixEnd_3480807 := by exact prefixLift 3480807
  have htrace : WordTrace (prefixWord ++ tailWord_3480807) baseStart_3480807 baseEnd_3480807 := by
    simpa [prefixWord, tailWord_3480807, baseEnd_3480807] using wordTrace_append hprefix tailTrace_3480807
  have hstable : (prefixWord ++ tailWord_3480807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480807).length < 2 ^ (prefixWord ++ tailWord_3480807).sum := by decide
  have hdescent : baseEnd_3480807 < baseStart_3480807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480825 : List Nat := [1, 2, 1, 3, 1, 1, 5, 1, 2, 2, 4]
def baseStart_3480825 : Nat := 118140960795 + 3480825 * 2 ^ 59
def prefixEnd_3480825 : Nat := 4983230072969 + 3 ^ 40 * 3480825 * 2
def baseEnd_3480825 : Nat := 1787336299186448989879483

theorem tailTrace_3480825 : CollatzResearch.WordTrace tailWord_3480825 prefixEnd_3480825 1787336299186448989879483 := by
  unfold tailWord_3480825
  simp only [CollatzResearch.WordTrace]
  refine ⟨126956117614572977426331929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84637411743048651617554619 126956117614572977426331929)
  ·
    refine ⟨95217088210929733069748947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126956117614572977426331929 95217088210929733069748947)
    ·
      refine ⟨142825632316394599604623421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95217088210929733069748947 142825632316394599604623421)
      ·
        refine ⟨53559612118647974851733783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142825632316394599604623421 53559612118647974851733783)
        ·
          refine ⟨80339418177971962277600675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53559612118647974851733783 80339418177971962277600675)
          ·
            refine ⟨120509127266957943416401013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80339418177971962277600675 120509127266957943416401013)
            ·
              refine ⟨11297730681277307195287595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120509127266957943416401013 11297730681277307195287595)
              ·
                refine ⟨16946596021915960792931393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11297730681277307195287595 16946596021915960792931393)
                ·
                  refine ⟨12709947016436970594698545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16946596021915960792931393 12709947016436970594698545)
                  ·
                    refine ⟨9532460262327727946023909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12709947016436970594698545 9532460262327727946023909)
                    ·
                      refine ⟨1787336299186448989879483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9532460262327727946023909 1787336299186448989879483)
                      ·
                        rfl

theorem cell23_3480825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_3480825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480825 prefixEnd_3480825 := by exact prefixLift 3480825
  have htrace : WordTrace (prefixWord ++ tailWord_3480825) baseStart_3480825 baseEnd_3480825 := by
    simpa [prefixWord, tailWord_3480825, baseEnd_3480825] using wordTrace_append hprefix tailTrace_3480825
  have hstable : (prefixWord ++ tailWord_3480825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480825).length < 2 ^ (prefixWord ++ tailWord_3480825).sum := by decide
  have hdescent : baseEnd_3480825 < baseStart_3480825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480835 : List Nat := [1, 1, 1, 3, 2, 5, 1, 2, 7]
def baseStart_3480835 : Nat := 118140960795 + 3480835 * 2 ^ 59
def prefixEnd_3480835 : Nat := 4983230072969 + 3 ^ 40 * 3480835 * 2
def baseEnd_3480835 : Nat := 198593492665888216750493

theorem tailTrace_3480835 : CollatzResearch.WordTrace tailWord_3480835 prefixEnd_3480835 198593492665888216750493 := by
  unfold tailWord_3480835
  simp only [CollatzResearch.WordTrace]
  refine ⟨126956482344536749134195959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84637654896357832756130639 126956482344536749134195959)
  ·
    refine ⟨190434723516805123701293939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126956482344536749134195959 190434723516805123701293939)
    ·
      refine ⟨285652085275207685551940909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190434723516805123701293939 285652085275207685551940909)
      ·
        refine ⟨107119531978202882081977841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285652085275207685551940909 107119531978202882081977841)
        ·
          refine ⟨80339648983652161561483381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107119531978202882081977841 80339648983652161561483381)
          ·
            refine ⟨7531842092217390146389067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80339648983652161561483381 7531842092217390146389067)
            ·
              refine ⟨11297763138326085219583601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7531842092217390146389067 11297763138326085219583601)
              ·
                refine ⟨8473322353744563914687701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11297763138326085219583601 8473322353744563914687701)
                ·
                  refine ⟨198593492665888216750493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8473322353744563914687701 198593492665888216750493)
                  ·
                    rfl

theorem cell23_3480835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 7].length) (baseStart_3480835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480835 prefixEnd_3480835 := by exact prefixLift 3480835
  have htrace : WordTrace (prefixWord ++ tailWord_3480835) baseStart_3480835 baseEnd_3480835 := by
    simpa [prefixWord, tailWord_3480835, baseEnd_3480835] using wordTrace_append hprefix tailTrace_3480835
  have hstable : (prefixWord ++ tailWord_3480835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480835).length < 2 ^ (prefixWord ++ tailWord_3480835).sum := by decide
  have hdescent : baseEnd_3480835 < baseStart_3480835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480863 : List Nat := [1, 1, 2, 4, 4, 2, 1, 2, 2, 2, 2]
def baseStart_3480863 : Nat := 118140960795 + 3480863 * 2 ^ 59
def prefixEnd_3480863 : Nat := 4983230072969 + 3 ^ 40 * 3480863 * 2
def baseEnd_3480863 : Nat := 1787355811451319841204309

theorem tailTrace_3480863 : CollatzResearch.WordTrace tailWord_3480863 prefixEnd_3480863 1787355811451319841204309 := by
  unfold tailWord_3480863
  simp only [CollatzResearch.WordTrace]
  refine ⟨126957503588435309916215243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84638335725623539944143495 126957503588435309916215243)
  ·
    refine ⟨190436255382652964874322865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126957503588435309916215243 190436255382652964874322865)
    ·
      refine ⟨142827191536989723655742149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190436255382652964874322865 142827191536989723655742149)
      ·
        refine ⟨26780098413185573185451653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142827191536989723655742149 26780098413185573185451653)
        ·
          refine ⟨5021268452472294972272185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26780098413185573185451653 5021268452472294972272185)
          ·
            refine ⟨3765951339354221229204139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5021268452472294972272185 3765951339354221229204139)
            ·
              refine ⟨5648927009031331843806209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3765951339354221229204139 5648927009031331843806209)
              ·
                refine ⟨4236695256773498882854657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5648927009031331843806209 4236695256773498882854657)
                ·
                  refine ⟨3177521442580124162140993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4236695256773498882854657 3177521442580124162140993)
                  ·
                    refine ⟨2383141081935093121605745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3177521442580124162140993 2383141081935093121605745)
                    ·
                      refine ⟨1787355811451319841204309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2383141081935093121605745 1787355811451319841204309)
                      ·
                        rfl

theorem cell23_3480863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_3480863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480863 prefixEnd_3480863 := by exact prefixLift 3480863
  have htrace : WordTrace (prefixWord ++ tailWord_3480863) baseStart_3480863 baseEnd_3480863 := by
    simpa [prefixWord, tailWord_3480863, baseEnd_3480863] using wordTrace_append hprefix tailTrace_3480863
  have hstable : (prefixWord ++ tailWord_3480863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480863).length < 2 ^ (prefixWord ++ tailWord_3480863).sum := by decide
  have hdescent : baseEnd_3480863 < baseStart_3480863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480865 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 4, 5]
def baseStart_3480865 : Nat := 118140960795 + 3480865 * 2 ^ 59
def prefixEnd_3480865 : Nat := 4983230072969 + 3 ^ 40 * 3480865 * 2
def baseEnd_3480865 : Nat := 595785612804209611126433

theorem tailTrace_3480865 : CollatzResearch.WordTrace tailWord_3480865 prefixEnd_3480865 595785612804209611126433 := by
  unfold tailWord_3480865
  simp only [CollatzResearch.WordTrace]
  refine ⟨126957576534428064257788049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84638384356285376171858699 126957576534428064257788049)
  ·
    refine ⟨95218182400821048193341037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126957576534428064257788049 95218182400821048193341037)
    ·
      refine ⟨35706818400307893072502889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95218182400821048193341037 35706818400307893072502889)
      ·
        refine ⟨26780113800230919804377167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35706818400307893072502889 26780113800230919804377167)
        ·
          refine ⟨40170170700346379706565751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26780113800230919804377167 40170170700346379706565751)
          ·
            refine ⟨60255256050519569559848627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40170170700346379706565751 60255256050519569559848627)
            ·
              refine ⟨90382884075779354339772941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60255256050519569559848627 90382884075779354339772941)
              ·
                refine ⟨33893581528417257877414853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90382884075779354339772941 33893581528417257877414853)
                ·
                  refine ⟨6355046536578235852015285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33893581528417257877414853 6355046536578235852015285)
                  ·
                    refine ⟨595785612804209611126433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6355046536578235852015285 595785612804209611126433)
                    ·
                      rfl

theorem cell23_3480865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_3480865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480865 prefixEnd_3480865 := by exact prefixLift 3480865
  have htrace : WordTrace (prefixWord ++ tailWord_3480865) baseStart_3480865 baseEnd_3480865 := by
    simpa [prefixWord, tailWord_3480865, baseEnd_3480865] using wordTrace_append hprefix tailTrace_3480865
  have hstable : (prefixWord ++ tailWord_3480865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480865).length < 2 ^ (prefixWord ++ tailWord_3480865).sum := by decide
  have hdescent : baseEnd_3480865 < baseStart_3480865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480922 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 4, 2, 3]
def baseStart_3480922 : Nat := 118140960795 + 3480922 * 2 ^ 59
def prefixEnd_3480922 : Nat := 4983230072969 + 3 ^ 40 * 3480922 * 2
def baseEnd_3480922 : Nat := 1787386106809935110366537

theorem tailTrace_3480922 : CollatzResearch.WordTrace tailWord_3480922 prefixEnd_3480922 1787386106809935110366537 := by
  unfold tailWord_3480922
  simp only [CollatzResearch.WordTrace]
  refine ⟨31739913873805390748153255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84639770330147708661742013 31739913873805390748153255)
  ·
    refine ⟨47609870810708086122229883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31739913873805390748153255 47609870810708086122229883)
    ·
      refine ⟨71414806216062129183344825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47609870810708086122229883 71414806216062129183344825)
      ·
        refine ⟨53561104662046596887508619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71414806216062129183344825 53561104662046596887508619)
        ·
          refine ⟨80341656993069895331262929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53561104662046596887508619 80341656993069895331262929)
          ·
            refine ⟨60256242744802421498447197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80341656993069895331262929 60256242744802421498447197)
            ·
              refine ⟨22596091029300908061917699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60256242744802421498447197 22596091029300908061917699)
              ·
                refine ⟨33894136543951362092876549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22596091029300908061917699 33894136543951362092876549)
                ·
                  refine ⟨6355150601990880392414353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33894136543951362092876549 6355150601990880392414353)
                  ·
                    refine ⟨4766362951493160294310765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6355150601990880392414353 4766362951493160294310765)
                    ·
                      refine ⟨1787386106809935110366537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4766362951493160294310765 1787386106809935110366537)
                      ·
                        rfl

theorem cell23_3480922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_3480922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480922 prefixEnd_3480922 := by exact prefixLift 3480922
  have htrace : WordTrace (prefixWord ++ tailWord_3480922) baseStart_3480922 baseEnd_3480922 := by
    simpa [prefixWord, tailWord_3480922, baseEnd_3480922] using wordTrace_append hprefix tailTrace_3480922
  have hstable : (prefixWord ++ tailWord_3480922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480922).length < 2 ^ (prefixWord ++ tailWord_3480922).sum := by decide
  have hdescent : baseEnd_3480922 < baseStart_3480922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480929 : List Nat := [1, 2, 3, 1, 1, 1, 1, 8, 1, 4]
def baseStart_3480929 : Nat := 118140960795 + 3480929 * 2 ^ 59
def prefixEnd_3480929 : Nat := 4983230072969 + 3 ^ 40 * 3480929 * 2
def baseEnd_3480929 : Nat := 595796567058172194326335

theorem tailTrace_3480929 : CollatzResearch.WordTrace tailWord_3480929 prefixEnd_3480929 595796567058172194326335 := by
  unfold tailWord_3480929
  simp only [CollatzResearch.WordTrace]
  refine ⟨126959910806196203188117841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84639940537464135458745227 126959910806196203188117841)
  ·
    refine ⟨95219933104647152391088381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126959910806196203188117841 95219933104647152391088381)
    ·
      refine ⟨35707474914242682146658143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95219933104647152391088381 35707474914242682146658143)
      ·
        refine ⟨53561212371364023219987215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35707474914242682146658143 53561212371364023219987215)
        ·
          refine ⟨80341818557046034829980823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53561212371364023219987215 80341818557046034829980823)
          ·
            refine ⟨120512727835569052244971235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80341818557046034829980823 120512727835569052244971235)
            ·
              refine ⟨180769091753353578367456853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120512727835569052244971235 180769091753353578367456853)
              ·
                refine ⟨2118387793984612246493635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 180769091753353578367456853 2118387793984612246493635)
                ·
                  refine ⟨3177581690976918369740453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2118387793984612246493635 3177581690976918369740453)
                  ·
                    refine ⟨595796567058172194326335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3177581690976918369740453 595796567058172194326335)
                    ·
                      rfl

theorem cell23_3480929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_3480929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480929 prefixEnd_3480929 := by exact prefixLift 3480929
  have htrace : WordTrace (prefixWord ++ tailWord_3480929) baseStart_3480929 baseEnd_3480929 := by
    simpa [prefixWord, tailWord_3480929, baseEnd_3480929] using wordTrace_append hprefix tailTrace_3480929
  have hstable : (prefixWord ++ tailWord_3480929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480929).length < 2 ^ (prefixWord ++ tailWord_3480929).sum := by decide
  have hdescent : baseEnd_3480929 < baseStart_3480929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480945 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 6]
def baseStart_3480945 : Nat := 118140960795 + 3480945 * 2 ^ 59
def prefixEnd_3480945 : Nat := 4983230072969 + 3 ^ 40 * 3480945 * 2
def baseEnd_3480945 : Nat := 1787397916864988520378931

theorem tailTrace_3480945 : CollatzResearch.WordTrace tailWord_3480945 prefixEnd_3480945 1787397916864988520378931 := by
  unfold tailWord_3480945
  simp only [CollatzResearch.WordTrace]
  refine ⟨126960494374138237920700289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84640329582758825280466859 126960494374138237920700289)
  ·
    refine ⟨95220370780603678440525217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126960494374138237920700289 95220370780603678440525217)
    ·
      refine ⟨71415278085452758830393913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95220370780603678440525217 71415278085452758830393913)
      ·
        refine ⟨53561458564089569122795435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71415278085452758830393913 53561458564089569122795435)
        ·
          refine ⟨80342187846134353684193153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53561458564089569122795435 80342187846134353684193153)
          ·
            refine ⟨60256640884600765263144865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80342187846134353684193153 60256640884600765263144865)
            ·
              refine ⟨45192480663450573947358649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60256640884600765263144865 45192480663450573947358649)
              ·
                refine ⟨33894360497587930460518987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45192480663450573947358649 33894360497587930460518987)
                ·
                  refine ⟨50841540746381895690778481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33894360497587930460518987 50841540746381895690778481)
                  ·
                    refine ⟨38131155559786421768083861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50841540746381895690778481 38131155559786421768083861)
                    ·
                      refine ⟨1787397916864988520378931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38131155559786421768083861 1787397916864988520378931)
                      ·
                        rfl

theorem cell23_3480945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_3480945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480945 prefixEnd_3480945 := by exact prefixLift 3480945
  have htrace : WordTrace (prefixWord ++ tailWord_3480945) baseStart_3480945 baseEnd_3480945 := by
    simpa [prefixWord, tailWord_3480945, baseEnd_3480945] using wordTrace_append hprefix tailTrace_3480945
  have hstable : (prefixWord ++ tailWord_3480945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480945).length < 2 ^ (prefixWord ++ tailWord_3480945).sum := by decide
  have hdescent : baseEnd_3480945 < baseStart_3480945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480980 : List Nat := [2, 4, 2, 1, 2, 3, 2, 2, 1, 4]
def baseStart_3480980 : Nat := 118140960795 + 3480980 * 2 ^ 59
def prefixEnd_3480980 : Nat := 4983230072969 + 3 ^ 40 * 3480980 * 2
def baseEnd_3480980 : Nat := 595805296229298627813757

theorem tailTrace_3480980 : CollatzResearch.WordTrace tailWord_3480980 prefixEnd_3480980 595805296229298627813757 := by
  unfold tailWord_3480980
  simp only [CollatzResearch.WordTrace]
  refine ⟨63480885464505719449112197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84641180619340959265482929 63480885464505719449112197)
  ·
    refine ⟨11902666024594822396708537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63480885464505719449112197 11902666024594822396708537)
    ·
      refine ⟨8926999518446116797531403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11902666024594822396708537 8926999518446116797531403)
      ·
        refine ⟨13390499277669175196297105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8926999518446116797531403 13390499277669175196297105)
        ·
          refine ⟨10042874458251881397222829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13390499277669175196297105 10042874458251881397222829)
          ·
            refine ⟨3766077921844455523958561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10042874458251881397222829 3766077921844455523958561)
            ·
              refine ⟨2824558441383341642968921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3766077921844455523958561 2824558441383341642968921)
              ·
                refine ⟨2118418831037506232226691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2824558441383341642968921 2118418831037506232226691)
                ·
                  refine ⟨3177628246556259348340037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2118418831037506232226691 3177628246556259348340037)
                  ·
                    refine ⟨595805296229298627813757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3177628246556259348340037 595805296229298627813757)
                    ·
                      rfl

theorem cell23_3480980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_3480980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480980 prefixEnd_3480980 := by exact prefixLift 3480980
  have htrace : WordTrace (prefixWord ++ tailWord_3480980) baseStart_3480980 baseEnd_3480980 := by
    simpa [prefixWord, tailWord_3480980, baseEnd_3480980] using wordTrace_append hprefix tailTrace_3480980
  have hstable : (prefixWord ++ tailWord_3480980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480980).length < 2 ^ (prefixWord ++ tailWord_3480980).sum := by decide
  have hdescent : baseEnd_3480980 < baseStart_3480980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480992 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 4]
def baseStart_3480992 : Nat := 118140960795 + 3480992 * 2 ^ 59
def prefixEnd_3480992 : Nat := 4983230072969 + 3 ^ 40 * 3480992 * 2
def baseEnd_3480992 : Nat := 1787422050455749836491215

theorem tailTrace_3480992 : CollatzResearch.WordTrace tailWord_3480992 prefixEnd_3480992 1787422050455749836491215 := by
  unfold tailWord_3480992
  simp only [CollatzResearch.WordTrace]
  refine ⟨63481104302483982473830615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84641472403311976631774153 63481104302483982473830615)
  ·
    refine ⟨95221656453725973710745923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63481104302483982473830615 95221656453725973710745923)
    ·
      refine ⟨142832484680588960566118885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95221656453725973710745923 142832484680588960566118885)
      ·
        refine ⟨26781090877610430106147291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142832484680588960566118885 26781090877610430106147291)
        ·
          refine ⟨40171636316415645159220937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26781090877610430106147291 40171636316415645159220937)
          ·
            refine ⟨30128727237311733869415703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40171636316415645159220937 30128727237311733869415703)
            ·
              refine ⟨45193090855967600804123555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30128727237311733869415703 45193090855967600804123555)
              ·
                refine ⟨67789636283951401206185333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45193090855967600804123555 67789636283951401206185333)
                ·
                  refine ⟨6355278401620443863079875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67789636283951401206185333 6355278401620443863079875)
                  ·
                    refine ⟨9532917602430665794619813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6355278401620443863079875 9532917602430665794619813)
                    ·
                      refine ⟨1787422050455749836491215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9532917602430665794619813 1787422050455749836491215)
                      ·
                        rfl

theorem cell23_3480992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_3480992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3480992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3480992 prefixEnd_3480992 := by exact prefixLift 3480992
  have htrace : WordTrace (prefixWord ++ tailWord_3480992) baseStart_3480992 baseEnd_3480992 := by
    simpa [prefixWord, tailWord_3480992, baseEnd_3480992] using wordTrace_append hprefix tailTrace_3480992
  have hstable : (prefixWord ++ tailWord_3480992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480992).length < 2 ^ (prefixWord ++ tailWord_3480992).sum := by decide
  have hdescent : baseEnd_3480992 < baseStart_3480992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481009 : List Nat := [1, 2, 2, 4, 1, 1, 2, 4, 1, 1, 4]
def baseStart_3481009 : Nat := 118140960795 + 3481009 * 2 ^ 59
def prefixEnd_3481009 : Nat := 4983230072969 + 3 ^ 40 * 3481009 * 2
def baseEnd_3481009 : Nat := 1787430779626876269978637

theorem tailTrace_3481009 : CollatzResearch.WordTrace tailWord_3481009 prefixEnd_3481009 1787430779626876269978637 := by
  unfold tailWord_3481009
  simp only [CollatzResearch.WordTrace]
  refine ⟨126962828645906376851030081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84641885763937584567353387 126962828645906376851030081)
  ·
    refine ⟨95222121484429782638272561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126962828645906376851030081 95222121484429782638272561)
    ·
      refine ⟨71416591113322336978704421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95222121484429782638272561 71416591113322336978704421)
      ·
        refine ⟨13390610833747938183507079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71416591113322336978704421 13390610833747938183507079)
        ·
          refine ⟨20085916250621907275260619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13390610833747938183507079 20085916250621907275260619)
          ·
            refine ⟨30128874375932860912890929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20085916250621907275260619 30128874375932860912890929)
            ·
              refine ⟨22596655781949645684668197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30128874375932860912890929 22596655781949645684668197)
              ·
                refine ⟨4236872959115558565875287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22596655781949645684668197 4236872959115558565875287)
                ·
                  refine ⟨6355309438673337848812931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4236872959115558565875287 6355309438673337848812931)
                  ·
                    refine ⟨9532964158010006773219397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6355309438673337848812931 9532964158010006773219397)
                    ·
                      refine ⟨1787430779626876269978637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9532964158010006773219397 1787430779626876269978637)
                      ·
                        rfl

theorem cell23_3481009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_3481009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481009 prefixEnd_3481009 := by exact prefixLift 3481009
  have htrace : WordTrace (prefixWord ++ tailWord_3481009) baseStart_3481009 baseEnd_3481009 := by
    simpa [prefixWord, tailWord_3481009, baseEnd_3481009] using wordTrace_append hprefix tailTrace_3481009
  have hstable : (prefixWord ++ tailWord_3481009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481009).length < 2 ^ (prefixWord ++ tailWord_3481009).sum := by decide
  have hdescent : baseEnd_3481009 < baseStart_3481009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481013 : List Nat := [1, 3, 3, 2, 2, 3, 1, 1, 2, 3, 2]
def baseStart_3481013 : Nat := 118140960795 + 3481013 * 2 ^ 59
def prefixEnd_3481013 : Nat := 4983230072969 + 3 ^ 40 * 3481013 * 2
def baseEnd_3481013 : Nat := 1787432833549494254328619

theorem tailTrace_3481013 : CollatzResearch.WordTrace tailWord_3481013 prefixEnd_3481013 1787432833549494254328619 := by
  unfold tailWord_3481013
  simp only [CollatzResearch.WordTrace]
  refine ⟨126962974537891885534175693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84641983025261257022783795 126962974537891885534175693)
  ·
    refine ⟨47611115451709457075315885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126962974537891885534175693 47611115451709457075315885)
    ·
      refine ⟨17854168294391046403243457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47611115451709457075315885 17854168294391046403243457)
      ·
        refine ⟨13390626220793284802432593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17854168294391046403243457 13390626220793284802432593)
        ·
          refine ⟨10042969665594963601824445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13390626220793284802432593 10042969665594963601824445)
          ·
            refine ⟨3766113624598111350684167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10042969665594963601824445 3766113624598111350684167)
            ·
              refine ⟨5649170436897167026026251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3766113624598111350684167 5649170436897167026026251)
              ·
                refine ⟨8473755655345750539039377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5649170436897167026026251 8473755655345750539039377)
                ·
                  refine ⟨6355316741509312904279533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8473755655345750539039377 6355316741509312904279533)
                  ·
                    refine ⟨2383243778065992339104825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6355316741509312904279533 2383243778065992339104825)
                    ·
                      refine ⟨1787432833549494254328619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2383243778065992339104825 1787432833549494254328619)
                      ·
                        rfl

theorem cell23_3481013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_3481013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481013 prefixEnd_3481013 := by exact prefixLift 3481013
  have htrace : WordTrace (prefixWord ++ tailWord_3481013) baseStart_3481013 baseEnd_3481013 := by
    simpa [prefixWord, tailWord_3481013, baseEnd_3481013] using wordTrace_append hprefix tailTrace_3481013
  have hstable : (prefixWord ++ tailWord_3481013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481013).length < 2 ^ (prefixWord ++ tailWord_3481013).sum := by decide
  have hdescent : baseEnd_3481013 < baseStart_3481013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481020 : List Nat := [2, 2, 2, 4, 2, 1, 2, 3, 1, 1, 3]
def baseStart_3481020 : Nat := 118140960795 + 3481020 * 2 ^ 59
def prefixEnd_3481020 : Nat := 4983230072969 + 3 ^ 40 * 3481020 * 2
def baseEnd_3481020 : Nat := 1787436427914075726941087

theorem tailTrace_3481020 : CollatzResearch.WordTrace tailWord_3481020 prefixEnd_3481020 1787436427914075726941087 := by
  unfold tailWord_3481020
  simp only [CollatzResearch.WordTrace]
  refine ⟨63481614924433262864840257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84642153232577683819787009 63481614924433262864840257)
  ·
    refine ⟨47611211193324947148630193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63481614924433262864840257 47611211193324947148630193)
    ·
      refine ⟨35708408394993710361472645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47611211193324947148630193 35708408394993710361472645)
      ·
        refine ⟨6695326574061320692776121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35708408394993710361472645 6695326574061320692776121)
        ·
          refine ⟨5021494930545990519582091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6695326574061320692776121 5021494930545990519582091)
          ·
            refine ⟨7532242395818985779373137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5021494930545990519582091 7532242395818985779373137)
            ·
              refine ⟨5649181796864239334529853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7532242395818985779373137 5649181796864239334529853)
              ·
                refine ⟨2118443173824089750448695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5649181796864239334529853 2118443173824089750448695)
                ·
                  refine ⟨3177664760736134625673043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2118443173824089750448695 3177664760736134625673043)
                  ·
                    refine ⟨4766497141104201938509565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3177664760736134625673043 4766497141104201938509565)
                    ·
                      refine ⟨1787436427914075726941087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4766497141104201938509565 1787436427914075726941087)
                      ·
                        rfl

theorem cell23_3481020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_3481020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481020 prefixEnd_3481020 := by exact prefixLift 3481020
  have htrace : WordTrace (prefixWord ++ tailWord_3481020) baseStart_3481020 baseEnd_3481020 := by
    simpa [prefixWord, tailWord_3481020, baseEnd_3481020] using wordTrace_append hprefix tailTrace_3481020
  have hstable : (prefixWord ++ tailWord_3481020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481020).length < 2 ^ (prefixWord ++ tailWord_3481020).sum := by decide
  have hdescent : baseEnd_3481020 < baseStart_3481020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481022 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6]
def baseStart_3481022 : Nat := 118140960795 + 3481022 * 2 ^ 59
def prefixEnd_3481022 : Nat := 4983230072969 + 3 ^ 40 * 3481022 * 2
def baseEnd_3481022 : Nat := 1787437454875384719116077

theorem tailTrace_3481022 : CollatzResearch.WordTrace tailWord_3481022 prefixEnd_3481022 1787437454875384719116077 := by
  unfold tailWord_3481022
  simp only [CollatzResearch.WordTrace]
  refine ⟨15870412849357410008906665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84642201863239520047502213 15870412849357410008906665)
  ·
    refine ⟨11902809637018057506679999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15870412849357410008906665 11902809637018057506679999)
    ·
      refine ⟨17854214455527086260019999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11902809637018057506679999 17854214455527086260019999)
      ·
        refine ⟨26781321683290629390029999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17854214455527086260019999 26781321683290629390029999)
        ·
          refine ⟨40171982524935944085044999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26781321683290629390029999 40171982524935944085044999)
          ·
            refine ⟨60257973787403916127567499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40171982524935944085044999 60257973787403916127567499)
            ·
              refine ⟨90386960681105874191351249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60257973787403916127567499 90386960681105874191351249)
              ·
                refine ⟨67790220510829405643513437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90386960681105874191351249 67790220510829405643513437)
                ·
                  refine ⟨25421332691561027116317539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67790220510829405643513437 25421332691561027116317539)
                  ·
                    refine ⟨38131999037341540674476309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25421332691561027116317539 38131999037341540674476309)
                    ·
                      refine ⟨1787437454875384719116077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38131999037341540674476309 1787437454875384719116077)
                      ·
                        rfl

theorem cell23_3481022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_3481022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481022 prefixEnd_3481022 := by exact prefixLift 3481022
  have htrace : WordTrace (prefixWord ++ tailWord_3481022) baseStart_3481022 baseEnd_3481022 := by
    simpa [prefixWord, tailWord_3481022, baseEnd_3481022] using wordTrace_append hprefix tailTrace_3481022
  have hstable : (prefixWord ++ tailWord_3481022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481022).length < 2 ^ (prefixWord ++ tailWord_3481022).sum := by decide
  have hdescent : baseEnd_3481022 < baseStart_3481022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481036 : List Nat := [2, 2, 1, 4, 2, 1, 3, 2, 2, 4]
def baseStart_3481036 : Nat := 118140960795 + 3481036 * 2 ^ 59
def prefixEnd_3481036 : Nat := 4983230072969 + 3 ^ 40 * 3481036 * 2
def baseEnd_3481036 : Nat := 595814881201515888113671

theorem tailTrace_3481036 : CollatzResearch.WordTrace tailWord_3481036 prefixEnd_3481036 595814881201515888113671 := by
  unfold tailWord_3481036
  simp only [CollatzResearch.WordTrace]
  refine ⟨63481906708404280231131481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84642542277872373641508641 63481906708404280231131481)
  ·
    refine ⟨47611430031303210173348611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63481906708404280231131481 47611430031303210173348611)
    ·
      refine ⟨71417145046954815260022917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47611430031303210173348611 71417145046954815260022917)
      ·
        refine ⟨13390714696304027861254297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71417145046954815260022917 13390714696304027861254297)
        ·
          refine ⟨10043036022228020895940723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13390714696304027861254297 10043036022228020895940723)
          ·
            refine ⟨15064554033342031343911085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10043036022228020895940723 15064554033342031343911085)
            ·
              refine ⟨5649207762503261753966657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15064554033342031343911085 5649207762503261753966657)
              ·
                refine ⟨4236905821877446315474993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5649207762503261753966657 4236905821877446315474993)
                ·
                  refine ⟨3177679366408084736606245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4236905821877446315474993 3177679366408084736606245)
                  ·
                    refine ⟨595814881201515888113671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3177679366408084736606245 595814881201515888113671)
                    ·
                      rfl

theorem cell23_3481036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 2, 4].length) (baseStart_3481036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481036 prefixEnd_3481036 := by exact prefixLift 3481036
  have htrace : WordTrace (prefixWord ++ tailWord_3481036) baseStart_3481036 baseEnd_3481036 := by
    simpa [prefixWord, tailWord_3481036, baseEnd_3481036] using wordTrace_append hprefix tailTrace_3481036
  have hstable : (prefixWord ++ tailWord_3481036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481036).length < 2 ^ (prefixWord ++ tailWord_3481036).sum := by decide
  have hdescent : baseEnd_3481036 < baseStart_3481036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481046 : List Nat := [5, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_3481046 : Nat := 118140960795 + 3481046 * 2 ^ 59
def prefixEnd_3481046 : Nat := 4983230072969 + 3 ^ 40 * 3481046 * 2
def baseEnd_3481046 : Nat := 1787449778411092625215967

theorem tailTrace_3481046 : CollatzResearch.WordTrace tailWord_3481046 prefixEnd_3481046 1787449778411092625215967 := by
  unfold tailWord_3481046
  simp only [CollatzResearch.WordTrace]
  refine ⟨7935261134173270760632937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84642785431181554780084661 7935261134173270760632937)
  ·
    refine ⟨5951445850629953070474703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7935261134173270760632937 5951445850629953070474703)
    ·
      refine ⟨8927168775944929605712055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5951445850629953070474703 8927168775944929605712055)
      ·
        refine ⟨13390753163917394408568083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8927168775944929605712055 13390753163917394408568083)
        ·
          refine ⟨20086129745876091612852125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13390753163917394408568083 20086129745876091612852125)
          ·
            refine ⟨7532298654703534354819547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20086129745876091612852125 7532298654703534354819547)
            ·
              refine ⟨11298447982055301532229321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7532298654703534354819547 11298447982055301532229321)
              ·
                refine ⟨8473835986541476149171991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11298447982055301532229321 8473835986541476149171991)
                ·
                  refine ⟨12710753979812214223757987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8473835986541476149171991 12710753979812214223757987)
                  ·
                    refine ⟨19066130969718321335636981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12710753979812214223757987 19066130969718321335636981)
                    ·
                      refine ⟨1787449778411092625215967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19066130969718321335636981 1787449778411092625215967)
                      ·
                        rfl

theorem cell23_3481046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_3481046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481046 prefixEnd_3481046 := by exact prefixLift 3481046
  have htrace : WordTrace (prefixWord ++ tailWord_3481046) baseStart_3481046 baseEnd_3481046 := by
    simpa [prefixWord, tailWord_3481046, baseEnd_3481046] using wordTrace_append hprefix tailTrace_3481046
  have hstable : (prefixWord ++ tailWord_3481046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481046).length < 2 ^ (prefixWord ++ tailWord_3481046).sum := by decide
  have hdescent : baseEnd_3481046 < baseStart_3481046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481053 : List Nat := [1, 4, 3, 1, 1, 3, 3, 1, 2, 4]
def baseStart_3481053 : Nat := 118140960795 + 3481053 * 2 ^ 59
def prefixEnd_3481053 : Nat := 4983230072969 + 3 ^ 40 * 3481053 * 2
def baseEnd_3481053 : Nat := 595817790925224699276145

theorem tailTrace_3481053 : CollatzResearch.WordTrace tailWord_3481053 prefixEnd_3481053 595817790925224699276145 := by
  unfold tailWord_3481053
  simp only [CollatzResearch.WordTrace]
  refine ⟨126964433457746972365631813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84642955638497981577087875 126964433457746972365631813)
  ·
    refine ⟨23805831273327557318555965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126964433457746972365631813 23805831273327557318555965)
    ·
      refine ⟨8927186727497833994458487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23805831273327557318555965 8927186727497833994458487)
      ·
        refine ⟨13390780091246750991687731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8927186727497833994458487 13390780091246750991687731)
        ·
          refine ⟨20086170136870126487531597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13390780091246750991687731 20086170136870126487531597)
          ·
            refine ⟨7532313801326297432824349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20086170136870126487531597 7532313801326297432824349)
            ·
              refine ⟨2824617675497361537309131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7532313801326297432824349 2824617675497361537309131)
              ·
                refine ⟨4236926513246042305963697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2824617675497361537309131 4236926513246042305963697)
                ·
                  refine ⟨3177694884934531729472773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4236926513246042305963697 3177694884934531729472773)
                  ·
                    refine ⟨595817790925224699276145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3177694884934531729472773 595817790925224699276145)
                    ·
                      rfl

theorem cell23_3481053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_3481053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481053 prefixEnd_3481053 := by exact prefixLift 3481053
  have htrace : WordTrace (prefixWord ++ tailWord_3481053) baseStart_3481053 baseEnd_3481053 := by
    simpa [prefixWord, tailWord_3481053, baseEnd_3481053] using wordTrace_append hprefix tailTrace_3481053
  have hstable : (prefixWord ++ tailWord_3481053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481053).length < 2 ^ (prefixWord ++ tailWord_3481053).sum := by decide
  have hdescent : baseEnd_3481053 < baseStart_3481053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481066 : List Nat := [3, 1, 3, 1, 4, 2, 2, 7]
def baseStart_3481066 : Nat := 118140960795 + 3481066 * 2 ^ 59
def prefixEnd_3481066 : Nat := 4983230072969 + 3 ^ 40 * 3481066 * 2
def baseEnd_3481066 : Nat := 66202224000895649887625

theorem tailTrace_3481066 : CollatzResearch.WordTrace tailWord_3481066 prefixEnd_3481066 66202224000895649887625 := by
  unfold tailWord_3481066
  simp only [CollatzResearch.WordTrace]
  refine ⟨31741226901674968896463763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84643271737799917057236701 31741226901674968896463763)
  ·
    refine ⟨47611840352512453344695645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31741226901674968896463763 47611840352512453344695645)
    ·
      refine ⟨17854440132192170004260867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47611840352512453344695645 17854440132192170004260867)
      ·
        refine ⟨26781660198288255006391301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17854440132192170004260867 26781660198288255006391301)
        ·
          refine ⟨5021561287179047813698369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26781660198288255006391301 5021561287179047813698369)
          ·
            refine ⟨3766170965384285860273777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5021561287179047813698369 3766170965384285860273777)
            ·
              refine ⟨2824628224038214395205333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3766170965384285860273777 2824628224038214395205333)
              ·
                refine ⟨66202224000895649887625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2824628224038214395205333 66202224000895649887625)
                ·
                  rfl

theorem cell23_3481066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 7].length) (baseStart_3481066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481066 prefixEnd_3481066 := by exact prefixLift 3481066
  have htrace : WordTrace (prefixWord ++ tailWord_3481066) baseStart_3481066 baseEnd_3481066 := by
    simpa [prefixWord, tailWord_3481066, baseEnd_3481066] using wordTrace_append hprefix tailTrace_3481066
  have hstable : (prefixWord ++ tailWord_3481066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481066).length < 2 ^ (prefixWord ++ tailWord_3481066).sum := by decide
  have hdescent : baseEnd_3481066 < baseStart_3481066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481072 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 5]
def baseStart_3481072 : Nat := 118140960795 + 3481072 * 2 ^ 59
def prefixEnd_3481072 : Nat := 4983230072969 + 3 ^ 40 * 3481072 * 2
def baseEnd_3481072 : Nat := 1787463128908109523490847

theorem tailTrace_3481072 : CollatzResearch.WordTrace tailWord_3481072 prefixEnd_3481072 1787463128908109523490847 := by
  unfold tailWord_3481072
  simp only [CollatzResearch.WordTrace]
  refine ⟨63482563222339069305286735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84643417629785425740382313 63482563222339069305286735)
  ·
    refine ⟨95223844833508603957930103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63482563222339069305286735 95223844833508603957930103)
    ·
      refine ⟨142835767250262905936895155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95223844833508603957930103 142835767250262905936895155)
      ·
        refine ⟨214253650875394358905342733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142835767250262905936895155 214253650875394358905342733)
        ·
          refine ⟨80345119078272884589503525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214253650875394358905342733 80345119078272884589503525)
          ·
            refine ⟨15064709827176165860531911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80345119078272884589503525 15064709827176165860531911)
            ·
              refine ⟨22597064740764248790797867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15064709827176165860531911 22597064740764248790797867)
              ·
                refine ⟨33895597111146373186196801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22597064740764248790797867 33895597111146373186196801)
                ·
                  refine ⟨25421697833359779889647601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33895597111146373186196801 25421697833359779889647601)
                  ·
                    refine ⟨19066273375019834917235701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25421697833359779889647601 19066273375019834917235701)
                    ·
                      refine ⟨1787463128908109523490847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19066273375019834917235701 1787463128908109523490847)
                      ·
                        rfl

theorem cell23_3481072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 5].length) (baseStart_3481072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481072 prefixEnd_3481072 := by exact prefixLift 3481072
  have htrace : WordTrace (prefixWord ++ tailWord_3481072) baseStart_3481072 baseEnd_3481072 := by
    simpa [prefixWord, tailWord_3481072, baseEnd_3481072] using wordTrace_append hprefix tailTrace_3481072
  have hstable : (prefixWord ++ tailWord_3481072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481072).length < 2 ^ (prefixWord ++ tailWord_3481072).sum := by decide
  have hdescent : baseEnd_3481072 < baseStart_3481072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481077 : List Nat := [1, 3, 5, 1, 1, 1, 3, 3, 1, 2, 2]
def baseStart_3481077 : Nat := 118140960795 + 3481077 * 2 ^ 59
def prefixEnd_3481077 : Nat := 4983230072969 + 3 ^ 40 * 3481077 * 2
def baseEnd_3481077 : Nat := 1787465696311382003928325

theorem tailTrace_3481077 : CollatzResearch.WordTrace tailWord_3481077 prefixEnd_3481077 1787465696311382003928325 := by
  unfold tailWord_3481077
  simp only [CollatzResearch.WordTrace]
  refine ⟨126965308809660024464505485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84643539206440016309670323 126965308809660024464505485)
  ·
    refine ⟨47611990803622509174189557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126965308809660024464505485 47611990803622509174189557)
    ·
      refine ⟨4463624137839610235080271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47611990803622509174189557 4463624137839610235080271)
      ·
        refine ⟨6695436206759415352620407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4463624137839610235080271 6695436206759415352620407)
        ·
          refine ⟨10043154310139123028930611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6695436206759415352620407 10043154310139123028930611)
          ·
            refine ⟨15064731465208684543395917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10043154310139123028930611 15064731465208684543395917)
            ·
              refine ⟨5649274299453256703773469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15064731465208684543395917 5649274299453256703773469)
              ·
                refine ⟨2118477862294971263915051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5649274299453256703773469 2118477862294971263915051)
                ·
                  refine ⟨3177716793442456895872577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2118477862294971263915051 3177716793442456895872577)
                  ·
                    refine ⟨2383287595081842671904433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3177716793442456895872577 2383287595081842671904433)
                    ·
                      refine ⟨1787465696311382003928325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2383287595081842671904433 1787465696311382003928325)
                      ·
                        rfl

theorem cell23_3481077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_3481077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481077 prefixEnd_3481077 := by exact prefixLift 3481077
  have htrace : WordTrace (prefixWord ++ tailWord_3481077) baseStart_3481077 baseEnd_3481077 := by
    simpa [prefixWord, tailWord_3481077, baseEnd_3481077] using wordTrace_append hprefix tailTrace_3481077
  have hstable : (prefixWord ++ tailWord_3481077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481077).length < 2 ^ (prefixWord ++ tailWord_3481077).sum := by decide
  have hdescent : baseEnd_3481077 < baseStart_3481077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481116 : List Nat := [2, 2, 3, 1, 2, 1, 2, 3, 1, 4, 2]
def baseStart_3481116 : Nat := 118140960795 + 3481116 * 2 ^ 59
def prefixEnd_3481116 : Nat := 4983230072969 + 3 ^ 40 * 3481116 * 2
def baseEnd_3481116 : Nat := 1787485722056907351340645

theorem tailTrace_3481116 : CollatzResearch.WordTrace tailWord_3481116 prefixEnd_3481116 1787485722056907351340645 := by
  unfold tailWord_3481116
  simp only [CollatzResearch.WordTrace]
  refine ⟨63483365628259367062587601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84644487504345822750116801 63483365628259367062587601)
  ·
    refine ⟨47612524221194525296940701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63483365628259367062587601 47612524221194525296940701)
    ·
      refine ⟨17854696582947946986352763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47612524221194525296940701 17854696582947946986352763)
      ·
        refine ⟨26782044874421920479529145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17854696582947946986352763 26782044874421920479529145)
        ·
          refine ⟨20086533655816440359646859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26782044874421920479529145 20086533655816440359646859)
          ·
            refine ⟨30129800483724660539470289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20086533655816440359646859 30129800483724660539470289)
            ·
              refine ⟨22597350362793495404602717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30129800483724660539470289 22597350362793495404602717)
              ·
                refine ⟨8474006386047560776726019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22597350362793495404602717 8474006386047560776726019)
                ·
                  refine ⟨12711009579071341165089029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8474006386047560776726019 12711009579071341165089029)
                  ·
                    refine ⟨2383314296075876468454193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12711009579071341165089029 2383314296075876468454193)
                    ·
                      refine ⟨1787485722056907351340645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2383314296075876468454193 1787485722056907351340645)
                      ·
                        rfl

theorem cell23_3481116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_3481116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481116 prefixEnd_3481116 := by exact prefixLift 3481116
  have htrace : WordTrace (prefixWord ++ tailWord_3481116) baseStart_3481116 baseEnd_3481116 := by
    simpa [prefixWord, tailWord_3481116, baseEnd_3481116] using wordTrace_append hprefix tailTrace_3481116
  have hstable : (prefixWord ++ tailWord_3481116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481116).length < 2 ^ (prefixWord ++ tailWord_3481116).sum := by decide
  have hdescent : baseEnd_3481116 < baseStart_3481116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481120 : List Nat := [2, 1, 1, 6, 1, 3, 1, 2, 1, 3, 2]
def baseStart_3481120 : Nat := 118140960795 + 3481120 * 2 ^ 59
def prefixEnd_3481120 : Nat := 4983230072969 + 3 ^ 40 * 3481120 * 2
def baseEnd_3481120 : Nat := 1787487775979525335690627

theorem tailTrace_3481120 : CollatzResearch.WordTrace tailWord_3481120 prefixEnd_3481120 1787487775979525335690627 := by
  unfold tailWord_3481120
  simp only [CollatzResearch.WordTrace]
  refine ⟨63483438574252121404160407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84644584765669495205547209 63483438574252121404160407)
  ·
    refine ⟨95225157861378182106240611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63483438574252121404160407 95225157861378182106240611)
    ·
      refine ⟨142837736792067273159360917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95225157861378182106240611 142837736792067273159360917)
      ·
        refine ⟨6695518912128153429345043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 142837736792067273159360917 6695518912128153429345043)
        ·
          refine ⟨10043278368192230144017565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6695518912128153429345043 10043278368192230144017565)
          ·
            refine ⟨3766229388072086304006587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10043278368192230144017565 3766229388072086304006587)
            ·
              refine ⟨5649344082108129456009881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3766229388072086304006587 5649344082108129456009881)
              ·
                refine ⟨4237008061581097092007411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5649344082108129456009881 4237008061581097092007411)
                ·
                  refine ⟨6355512092371645638011117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4237008061581097092007411 6355512092371645638011117)
                  ·
                    refine ⟨2383317034639367114254169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6355512092371645638011117 2383317034639367114254169)
                    ·
                      refine ⟨1787487775979525335690627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2383317034639367114254169 1787487775979525335690627)
                      ·
                        rfl

theorem cell23_3481120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_3481120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481120 prefixEnd_3481120 := by exact prefixLift 3481120
  have htrace : WordTrace (prefixWord ++ tailWord_3481120) baseStart_3481120 baseEnd_3481120 := by
    simpa [prefixWord, tailWord_3481120, baseEnd_3481120] using wordTrace_append hprefix tailTrace_3481120
  have hstable : (prefixWord ++ tailWord_3481120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481120).length < 2 ^ (prefixWord ++ tailWord_3481120).sum := by decide
  have hdescent : baseEnd_3481120 < baseStart_3481120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481152 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 3, 7]
def baseStart_3481152 : Nat := 118140960795 + 3481152 * 2 ^ 59
def prefixEnd_3481152 : Nat := 4983230072969 + 3 ^ 40 * 3481152 * 2
def baseEnd_3481152 : Nat := 595834735786823070163493

theorem tailTrace_3481152 : CollatzResearch.WordTrace tailWord_3481152 prefixEnd_3481152 595834735786823070163493 := by
  unfold tailWord_3481152
  simp only [CollatzResearch.WordTrace]
  refine ⟨63484022142194156136742855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84645362856258874848990473 63484022142194156136742855)
  ·
    refine ⟨95226033213291234205114283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63484022142194156136742855 95226033213291234205114283)
    ·
      refine ⟨142839049819936851307671425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95226033213291234205114283 142839049819936851307671425)
      ·
        refine ⟨107129287364952638480753569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142839049819936851307671425 107129287364952638480753569)
        ·
          refine ⟨80346965523714478860565177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107129287364952638480753569 80346965523714478860565177)
          ·
            refine ⟨60260224142785859145423883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80346965523714478860565177 60260224142785859145423883)
            ·
              refine ⟨90390336214178788718135825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60260224142785859145423883 90390336214178788718135825)
              ·
                refine ⟨67792752160634091538601869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90390336214178788718135825 67792752160634091538601869)
                ·
                  refine ⟨25422282060237784326975701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67792752160634091538601869 25422282060237784326975701)
                  ·
                    refine ⟨595834735786823070163493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25422282060237784326975701 595834735786823070163493)
                    ·
                      rfl

theorem cell23_3481152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 3, 7].length) (baseStart_3481152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481152 prefixEnd_3481152 := by exact prefixLift 3481152
  have htrace : WordTrace (prefixWord ++ tailWord_3481152) baseStart_3481152 baseEnd_3481152 := by
    simpa [prefixWord, tailWord_3481152, baseEnd_3481152] using wordTrace_append hprefix tailTrace_3481152
  have hstable : (prefixWord ++ tailWord_3481152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481152).length < 2 ^ (prefixWord ++ tailWord_3481152).sum := by decide
  have hdescent : baseEnd_3481152 < baseStart_3481152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481199 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 7, 4]
def baseStart_3481199 : Nat := 118140960795 + 3481199 * 2 ^ 59
def prefixEnd_3481199 : Nat := 4983230072969 + 3 ^ 40 * 3481199 * 2
def baseEnd_3481199 : Nat := 595842780317076842200921

theorem tailTrace_3481199 : CollatzResearch.WordTrace tailWord_3481199 prefixEnd_3481199 595842780317076842200921 := by
  unfold tailWord_3481199
  simp only [CollatzResearch.WordTrace]
  refine ⟨126969758515218039300446651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84646505676812026200297767 126969758515218039300446651)
  ·
    refine ⟨190454637772827058950669977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126969758515218039300446651 190454637772827058950669977)
    ·
      refine ⟨142840978329620294213002483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190454637772827058950669977 142840978329620294213002483)
      ·
        refine ⟨214261467494430441319503725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142840978329620294213002483 214261467494430441319503725)
        ·
          refine ⟨80348050310411415494813897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214261467494430441319503725 80348050310411415494813897)
          ·
            refine ⟨60261037732808561621110423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80348050310411415494813897 60261037732808561621110423)
            ·
              refine ⟨90391556599212842431665635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60261037732808561621110423 90391556599212842431665635)
              ·
                refine ⟨135587334898819263647498453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90391556599212842431665635 135587334898819263647498453)
                ·
                  refine ⟨3177828161691076491738245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 135587334898819263647498453 3177828161691076491738245)
                  ·
                    refine ⟨595842780317076842200921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3177828161691076491738245 595842780317076842200921)
                    ·
                      rfl

theorem cell23_3481199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 7, 4].length) (baseStart_3481199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481199 prefixEnd_3481199 := by exact prefixLift 3481199
  have htrace : WordTrace (prefixWord ++ tailWord_3481199) baseStart_3481199 baseEnd_3481199 := by
    simpa [prefixWord, tailWord_3481199, baseEnd_3481199] using wordTrace_append hprefix tailTrace_3481199
  have hstable : (prefixWord ++ tailWord_3481199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481199).length < 2 ^ (prefixWord ++ tailWord_3481199).sum := by decide
  have hdescent : baseEnd_3481199 < baseStart_3481199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481216 : List Nat := [2, 1, 1, 2, 1, 4, 4, 1, 3, 4]
def baseStart_3481216 : Nat := 118140960795 + 3481216 * 2 ^ 59
def prefixEnd_3481216 : Nat := 4983230072969 + 3 ^ 40 * 3481216 * 2
def baseEnd_3481216 : Nat := 595845690040785653363395

theorem tailTrace_3481216 : CollatzResearch.WordTrace tailWord_3481216 prefixEnd_3481216 595845690040785653363395 := by
  unfold tailWord_3481216
  simp only [CollatzResearch.WordTrace]
  refine ⟨63485189278078225601907751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84646919037437634135877001 63485189278078225601907751)
  ·
    refine ⟨95227783917117338402861627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63485189278078225601907751 95227783917117338402861627)
    ·
      refine ⟨142841675875676007604292441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95227783917117338402861627 142841675875676007604292441)
      ·
        refine ⟨107131256906757005703219331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142841675875676007604292441 107131256906757005703219331)
        ·
          refine ⟨160696885360135508554828997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107131256906757005703219331 160696885360135508554828997)
          ·
            refine ⟨30130666005025407854030437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160696885360135508554828997 30130666005025407854030437)
            ·
              refine ⟨5649499875942263972630707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30130666005025407854030437 5649499875942263972630707)
              ·
                refine ⟨8474249813913395958946061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5649499875942263972630707 8474249813913395958946061)
                ·
                  refine ⟨3177843680217523484604773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8474249813913395958946061 3177843680217523484604773)
                  ·
                    refine ⟨595845690040785653363395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3177843680217523484604773 595845690040785653363395)
                    ·
                      rfl

theorem cell23_3481216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 3, 4].length) (baseStart_3481216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481216 prefixEnd_3481216 := by exact prefixLift 3481216
  have htrace : WordTrace (prefixWord ++ tailWord_3481216) baseStart_3481216 baseEnd_3481216 := by
    simpa [prefixWord, tailWord_3481216, baseEnd_3481216] using wordTrace_append hprefix tailTrace_3481216
  have hstable : (prefixWord ++ tailWord_3481216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481216).length < 2 ^ (prefixWord ++ tailWord_3481216).sum := by decide
  have hdescent : baseEnd_3481216 < baseStart_3481216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481226 : List Nat := [3, 1, 2, 3, 2, 1, 1, 2, 1, 4, 3]
def baseStart_3481226 : Nat := 118140960795 + 3481226 * 2 ^ 59
def prefixEnd_3481226 : Nat := 4983230072969 + 3 ^ 40 * 3481226 * 2
def baseEnd_3481226 : Nat := 1787542204928901920965139

theorem tailTrace_3481226 : CollatzResearch.WordTrace tailWord_3481226 prefixEnd_3481226 1787542204928901920965139 := by
  unfold tailWord_3481226
  simp only [CollatzResearch.WordTrace]
  refine ⟨31742685821530055727919883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84647162190746815274453021 31742685821530055727919883)
  ·
    refine ⟨47614028732295083591879825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31742685821530055727919883 47614028732295083591879825)
    ·
      refine ⟨35710521549221312693909869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47614028732295083591879825 35710521549221312693909869)
      ·
        refine ⟨13391445580957992260216201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35710521549221312693909869 13391445580957992260216201)
        ·
          refine ⟨10043584185718494195162151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13391445580957992260216201 10043584185718494195162151)
          ·
            refine ⟨15065376278577741292743227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10043584185718494195162151 15065376278577741292743227)
            ·
              refine ⟨22598064417866611939114841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15065376278577741292743227 22598064417866611939114841)
              ·
                refine ⟨16948548313399958954336131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22598064417866611939114841 16948548313399958954336131)
                ·
                  refine ⟨25422822470099938431504197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16948548313399958954336131 25422822470099938431504197)
                  ·
                    refine ⟨4766779213143738455907037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25422822470099938431504197 4766779213143738455907037)
                    ·
                      refine ⟨1787542204928901920965139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4766779213143738455907037 1787542204928901920965139)
                      ·
                        rfl

theorem cell23_3481226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_3481226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481226 prefixEnd_3481226 := by exact prefixLift 3481226
  have htrace : WordTrace (prefixWord ++ tailWord_3481226) baseStart_3481226 baseEnd_3481226 := by
    simpa [prefixWord, tailWord_3481226, baseEnd_3481226] using wordTrace_append hprefix tailTrace_3481226
  have hstable : (prefixWord ++ tailWord_3481226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481226).length < 2 ^ (prefixWord ++ tailWord_3481226).sum := by decide
  have hdescent : baseEnd_3481226 < baseStart_3481226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481246 : List Nat := [4, 3, 1, 1, 1, 2, 1, 2, 8]
def baseStart_3481246 : Nat := 118140960795 + 3481246 * 2 ^ 59
def prefixEnd_3481246 : Nat := 4983230072969 + 3 ^ 40 * 3481246 * 2
def baseEnd_3481246 : Nat := 198616941615776871412783

theorem tailTrace_3481246 : CollatzResearch.WordTrace tailWord_3481246 prefixEnd_3481246 198616941615776871412783 := by
  unfold tailWord_3481246
  simp only [CollatzResearch.WordTrace]
  refine ⟨15871434093255970790925949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84647648497365177551605061 15871434093255970790925949)
  ·
    refine ⟨5951787784970989046597231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15871434093255970790925949 5951787784970989046597231)
    ·
      refine ⟨8927681677456483569895847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5951787784970989046597231 8927681677456483569895847)
      ·
        refine ⟨13391522516184725354843771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8927681677456483569895847 13391522516184725354843771)
        ·
          refine ⟨20087283774277088032265657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13391522516184725354843771 20087283774277088032265657)
          ·
            refine ⟨15065462830707816024199243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20087283774277088032265657 15065462830707816024199243)
            ·
              refine ⟨22598194246061724036298865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15065462830707816024199243 22598194246061724036298865)
              ·
                refine ⟨16948645684546293027224149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22598194246061724036298865 16948645684546293027224149)
                ·
                  refine ⟨198616941615776871412783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16948645684546293027224149 198616941615776871412783)
                  ·
                    rfl

theorem cell23_3481246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_3481246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481246 prefixEnd_3481246 := by exact prefixLift 3481246
  have htrace : WordTrace (prefixWord ++ tailWord_3481246) baseStart_3481246 baseEnd_3481246 := by
    simpa [prefixWord, tailWord_3481246, baseEnd_3481246] using wordTrace_append hprefix tailTrace_3481246
  have hstable : (prefixWord ++ tailWord_3481246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481246).length < 2 ^ (prefixWord ++ tailWord_3481246).sum := by decide
  have hdescent : baseEnd_3481246 < baseStart_3481246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481273 : List Nat := [1, 2, 1, 4, 1, 1, 5, 1, 3, 1, 3]
def baseStart_3481273 : Nat := 118140960795 + 3481273 * 2 ^ 59
def prefixEnd_3481273 : Nat := 4983230072969 + 3 ^ 40 * 3481273 * 2
def baseEnd_3481273 : Nat := 1787566338519663237077423

theorem tailTrace_3481273 : CollatzResearch.WordTrace tailWord_3481273 prefixEnd_3481273 1787566338519663237077423 := by
  unfold tailWord_3481273
  simp only [CollatzResearch.WordTrace]
  refine ⟨126972457516949949938640473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84648305011299966625760315 126972457516949949938640473)
  ·
    refine ⟨95229343137712462453980355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126972457516949949938640473 95229343137712462453980355)
    ·
      refine ⟨142844014706568693680970533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95229343137712462453980355 142844014706568693680970533)
      ·
        refine ⟨26783252757481630065181975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142844014706568693680970533 26783252757481630065181975)
        ·
          refine ⟨40174879136222445097772963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26783252757481630065181975 40174879136222445097772963)
          ·
            refine ⟨60262318704333667646659445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40174879136222445097772963 60262318704333667646659445)
            ·
              refine ⟨5649592378531281341874323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60262318704333667646659445 5649592378531281341874323)
              ·
                refine ⟨8474388567796922012811485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5649592378531281341874323 8474388567796922012811485)
                ·
                  refine ⟨3177895712923845754804307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8474388567796922012811485 3177895712923845754804307)
                  ·
                    refine ⟨4766843569385768632206461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3177895712923845754804307 4766843569385768632206461)
                    ·
                      refine ⟨1787566338519663237077423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4766843569385768632206461 1787566338519663237077423)
                      ·
                        rfl

theorem cell23_3481273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_3481273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481273 prefixEnd_3481273 := by exact prefixLift 3481273
  have htrace : WordTrace (prefixWord ++ tailWord_3481273) baseStart_3481273 baseEnd_3481273 := by
    simpa [prefixWord, tailWord_3481273, baseEnd_3481273] using wordTrace_append hprefix tailTrace_3481273
  have hstable : (prefixWord ++ tailWord_3481273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481273).length < 2 ^ (prefixWord ++ tailWord_3481273).sum := by decide
  have hdescent : baseEnd_3481273 < baseStart_3481273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481296 : List Nat := [2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 4]
def baseStart_3481296 : Nat := 118140960795 + 3481296 * 2 ^ 59
def prefixEnd_3481296 : Nat := 4983230072969 + 3 ^ 40 * 3481296 * 2
def baseEnd_3481296 : Nat := 1787578148574716647089817

theorem tailTrace_3481296 : CollatzResearch.WordTrace tailWord_3481296 prefixEnd_3481296 1787578148574716647089817 := by
  unfold tailWord_3481296
  simp only [CollatzResearch.WordTrace]
  refine ⟨63486648197933312433363871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84648864263911083244485161 63486648197933312433363871)
  ·
    refine ⟨95229972296899968650045807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63486648197933312433363871 95229972296899968650045807)
    ·
      refine ⟨142844958445349952975068711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95229972296899968650045807 142844958445349952975068711)
      ·
        refine ⟨214267437668024929462603067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142844958445349952975068711 214267437668024929462603067)
        ·
          refine ⟨321401156502037394193904601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214267437668024929462603067 321401156502037394193904601)
          ·
            refine ⟨241050867376528045645428451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321401156502037394193904601 241050867376528045645428451)
            ·
              refine ⟨361576301064792068468142677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241050867376528045645428451 361576301064792068468142677)
              ·
                refine ⟨4237222278103032052361047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 361576301064792068468142677 4237222278103032052361047)
                ·
                  refine ⟨6355833417154548078541571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4237222278103032052361047 6355833417154548078541571)
                  ·
                    refine ⟨9533750125731822117812357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6355833417154548078541571 9533750125731822117812357)
                    ·
                      refine ⟨1787578148574716647089817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9533750125731822117812357 1787578148574716647089817)
                      ·
                        rfl

theorem cell23_3481296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 4].length) (baseStart_3481296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481296 prefixEnd_3481296 := by exact prefixLift 3481296
  have htrace : WordTrace (prefixWord ++ tailWord_3481296) baseStart_3481296 baseEnd_3481296 := by
    simpa [prefixWord, tailWord_3481296, baseEnd_3481296] using wordTrace_append hprefix tailTrace_3481296
  have hstable : (prefixWord ++ tailWord_3481296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481296).length < 2 ^ (prefixWord ++ tailWord_3481296).sum := by decide
  have hdescent : baseEnd_3481296 < baseStart_3481296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481300 : List Nat := [2, 4, 1, 3, 1, 1, 1, 3, 2, 3, 2]
def baseStart_3481300 : Nat := 118140960795 + 3481300 * 2 ^ 59
def prefixEnd_3481300 : Nat := 4983230072969 + 3 ^ 40 * 3481300 * 2
def baseEnd_3481300 : Nat := 1787580202497334631439799

theorem tailTrace_3481300 : CollatzResearch.WordTrace tailWord_3481300 prefixEnd_3481300 1787580202497334631439799 := by
  unfold tailWord_3481300
  simp only [CollatzResearch.WordTrace]
  refine ⟨63486721143926066774936677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84648961525234755699915569 63486721143926066774936677)
  ·
    refine ⟨11903760214486137520300627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63486721143926066774936677 11903760214486137520300627)
    ·
      refine ⟨17855640321729206280450941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11903760214486137520300627 17855640321729206280450941)
      ·
        refine ⟨6695865120648452355169103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17855640321729206280450941 6695865120648452355169103)
        ·
          refine ⟨10043797680972678532753655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6695865120648452355169103 10043797680972678532753655)
          ·
            refine ⟨15065696521459017799130483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10043797680972678532753655 15065696521459017799130483)
            ·
              refine ⟨22598544782188526698695725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15065696521459017799130483 22598544782188526698695725)
              ·
                refine ⟨8474454293320697512010897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22598544782188526698695725 8474454293320697512010897)
                ·
                  refine ⟨6355840719990523134008173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8474454293320697512010897 6355840719990523134008173)
                  ·
                    refine ⟨2383440269996446175253065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6355840719990523134008173 2383440269996446175253065)
                    ·
                      refine ⟨1787580202497334631439799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2383440269996446175253065 1787580202497334631439799)
                      ·
                        rfl

theorem cell23_3481300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_3481300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481300 prefixEnd_3481300 := by exact prefixLift 3481300
  have htrace : WordTrace (prefixWord ++ tailWord_3481300) baseStart_3481300 baseEnd_3481300 := by
    simpa [prefixWord, tailWord_3481300, baseEnd_3481300] using wordTrace_append hprefix tailTrace_3481300
  have hstable : (prefixWord ++ tailWord_3481300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481300).length < 2 ^ (prefixWord ++ tailWord_3481300).sum := by decide
  have hdescent : baseEnd_3481300 < baseStart_3481300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481306 : List Nat := [3, 1, 1, 2, 2, 4, 1, 2, 1, 6]
def baseStart_3481306 : Nat := 118140960795 + 3481306 * 2 ^ 59
def prefixEnd_3481306 : Nat := 4983230072969 + 3 ^ 40 * 3481306 * 2
def baseEnd_3481306 : Nat := 595861094460420535988257

theorem tailTrace_3481306 : CollatzResearch.WordTrace tailWord_3481306 prefixEnd_3481306 595861094460420535988257 := by
  unfold tailWord_3481306
  simp only [CollatzResearch.WordTrace]
  refine ⟨31743415281457599143647943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84649107417220264383061181 31743415281457599143647943)
  ·
    refine ⟨47615122922186398715471915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31743415281457599143647943 47615122922186398715471915)
    ·
      refine ⟨71422684383279598073207873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47615122922186398715471915 71422684383279598073207873)
      ·
        refine ⟨53567013287459698554905905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71422684383279598073207873 53567013287459698554905905)
        ·
          refine ⟨40175259965594773916179429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53567013287459698554905905 40175259965594773916179429)
          ·
            refine ⟨7532861243549020109283643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40175259965594773916179429 7532861243549020109283643)
            ·
              refine ⟨11299291865323530163925465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7532861243549020109283643 11299291865323530163925465)
              ·
                refine ⟨8474468898992647622944099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11299291865323530163925465 8474468898992647622944099)
                ·
                  refine ⟨12711703348488971434416149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8474468898992647622944099 12711703348488971434416149)
                  ·
                    refine ⟨595861094460420535988257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12711703348488971434416149 595861094460420535988257)
                    ·
                      rfl

theorem cell23_3481306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 1, 6].length) (baseStart_3481306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481306 prefixEnd_3481306 := by exact prefixLift 3481306
  have htrace : WordTrace (prefixWord ++ tailWord_3481306) baseStart_3481306 baseEnd_3481306 := by
    simpa [prefixWord, tailWord_3481306, baseEnd_3481306] using wordTrace_append hprefix tailTrace_3481306
  have hstable : (prefixWord ++ tailWord_3481306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481306).length < 2 ^ (prefixWord ++ tailWord_3481306).sum := by decide
  have hdescent : baseEnd_3481306 < baseStart_3481306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481326 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 3, 2, 4]
def baseStart_3481326 : Nat := 118140960795 + 3481326 * 2 ^ 59
def prefixEnd_3481326 : Nat := 4983230072969 + 3 ^ 40 * 3481326 * 2
def baseEnd_3481326 : Nat := 1787593552994351529714679

theorem tailTrace_3481326 : CollatzResearch.WordTrace tailWord_3481326 prefixEnd_3481326 1787593552994351529714679 := by
  unfold tailWord_3481326
  simp only [CollatzResearch.WordTrace]
  refine ⟨15871798823219742498789979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84649593723838626660213221 15871798823219742498789979)
  ·
    refine ⟨23807698234829613748184969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15871798823219742498789979 23807698234829613748184969)
    ·
      refine ⟨17855773676122210311138727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23807698234829613748184969 17855773676122210311138727)
      ·
        refine ⟨26783660514183315466708091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17855773676122210311138727 26783660514183315466708091)
        ·
          refine ⟨40175490771274973200062137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26783660514183315466708091 40175490771274973200062137)
          ·
            refine ⟨30131618078456229900046603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40175490771274973200062137 30131618078456229900046603)
            ·
              refine ⟨45197427117684344850069905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30131618078456229900046603 45197427117684344850069905)
              ·
                refine ⟨33898070338263258637552429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45197427117684344850069905 33898070338263258637552429)
                ·
                  refine ⟨12711776376848721989082161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33898070338263258637552429 12711776376848721989082161)
                  ·
                    refine ⟨9533832282636541491811621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12711776376848721989082161 9533832282636541491811621)
                    ·
                      refine ⟨1787593552994351529714679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9533832282636541491811621 1787593552994351529714679)
                      ·
                        rfl

theorem cell23_3481326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_3481326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481326 prefixEnd_3481326 := by exact prefixLift 3481326
  have htrace : WordTrace (prefixWord ++ tailWord_3481326) baseStart_3481326 baseEnd_3481326 := by
    simpa [prefixWord, tailWord_3481326, baseEnd_3481326] using wordTrace_append hprefix tailTrace_3481326
  have hstable : (prefixWord ++ tailWord_3481326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481326).length < 2 ^ (prefixWord ++ tailWord_3481326).sum := by decide
  have hdescent : baseEnd_3481326 < baseStart_3481326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481330 : List Nat := [3, 2, 1, 3, 1, 1, 2, 3, 3, 2, 2]
def baseStart_3481330 : Nat := 118140960795 + 3481330 * 2 ^ 59
def prefixEnd_3481330 : Nat := 4983230072969 + 3 ^ 40 * 3481330 * 2
def baseEnd_3481330 : Nat := 1787595606916969514064661

theorem tailTrace_3481330 : CollatzResearch.WordTrace tailWord_3481330 prefixEnd_3481330 1787595606916969514064661 := by
  unfold tailWord_3481330
  simp only [CollatzResearch.WordTrace]
  refine ⟨31743634119435862168366361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84649690985162299115643629 31743634119435862168366361)
  ·
    refine ⟨23807725589576896626274771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31743634119435862168366361 23807725589576896626274771)
    ·
      refine ⟨35711588384365344939412157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23807725589576896626274771 35711588384365344939412157)
      ·
        refine ⟨13391845644137004352279559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35711588384365344939412157 13391845644137004352279559)
        ·
          refine ⟨20087768466205506528419339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13391845644137004352279559 20087768466205506528419339)
          ·
            refine ⟨30131652699308259792629009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20087768466205506528419339 30131652699308259792629009)
            ·
              refine ⟨22598739524481194844471757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30131652699308259792629009 22598739524481194844471757)
              ·
                refine ⟨8474527321680448066676909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22598739524481194844471757 8474527321680448066676909)
                ·
                  refine ⟨3177947745630168025003841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8474527321680448066676909 3177947745630168025003841)
                  ·
                    refine ⟨2383460809222626018752881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3177947745630168025003841 2383460809222626018752881)
                    ·
                      refine ⟨1787595606916969514064661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2383460809222626018752881 1787595606916969514064661)
                      ·
                        rfl

theorem cell23_3481330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_3481330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481330 prefixEnd_3481330 := by exact prefixLift 3481330
  have htrace : WordTrace (prefixWord ++ tailWord_3481330) baseStart_3481330 baseEnd_3481330 := by
    simpa [prefixWord, tailWord_3481330, baseEnd_3481330] using wordTrace_append hprefix tailTrace_3481330
  have hstable : (prefixWord ++ tailWord_3481330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481330).length < 2 ^ (prefixWord ++ tailWord_3481330).sum := by decide
  have hdescent : baseEnd_3481330 < baseStart_3481330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481364 : List Nat := [2, 4, 4, 1, 1, 1, 1, 3, 1, 1, 4]
def baseStart_3481364 : Nat := 118140960795 + 3481364 * 2 ^ 59
def prefixEnd_3481364 : Nat := 4983230072969 + 3 ^ 40 * 3481364 * 2
def baseEnd_3481364 : Nat := 1787613065259222381039505

theorem tailTrace_3481364 : CollatzResearch.WordTrace tailWord_3481364 prefixEnd_3481364 1787613065259222381039505 := by
  unfold tailWord_3481364
  simp only [CollatzResearch.WordTrace]
  refine ⟨63487888279810136240101573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84650517706413514986802097 63487888279810136240101573)
  ·
    refine ⟨11903979052464400545019045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63487888279810136240101573 11903979052464400545019045)
    ·
      refine ⟨2231996072337075102191071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11903979052464400545019045 2231996072337075102191071)
      ·
        refine ⟨3347994108505612653286607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2231996072337075102191071 3347994108505612653286607)
        ·
          refine ⟨5021991162758418979929911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3347994108505612653286607 5021991162758418979929911)
          ·
            refine ⟨7532986744137628469894867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5021991162758418979929911 7532986744137628469894867)
            ·
              refine ⟨11299480116206442704842301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7532986744137628469894867 11299480116206442704842301)
              ·
                refine ⟨4237305043577416014315863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11299480116206442704842301 4237305043577416014315863)
                ·
                  refine ⟨6355957565366124021473795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4237305043577416014315863 6355957565366124021473795)
                  ·
                    refine ⟨9533936348049186032210693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6355957565366124021473795 9533936348049186032210693)
                    ·
                      refine ⟨1787613065259222381039505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9533936348049186032210693 1787613065259222381039505)
                      ·
                        rfl

theorem cell23_3481364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_3481364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481364 prefixEnd_3481364 := by exact prefixLift 3481364
  have htrace : WordTrace (prefixWord ++ tailWord_3481364) baseStart_3481364 baseEnd_3481364 := by
    simpa [prefixWord, tailWord_3481364, baseEnd_3481364] using wordTrace_append hprefix tailTrace_3481364
  have hstable : (prefixWord ++ tailWord_3481364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481364).length < 2 ^ (prefixWord ++ tailWord_3481364).sum := by decide
  have hdescent : baseEnd_3481364 < baseStart_3481364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481367 : List Nat := [1, 1, 3, 4, 2, 3, 2, 1, 1, 2, 3]
def baseStart_3481367 : Nat := 118140960795 + 3481367 * 2 ^ 59
def prefixEnd_3481367 : Nat := 4983230072969 + 3 ^ 40 * 3481367 * 2
def baseEnd_3481367 : Nat := 1787614605701185869301991

theorem tailTrace_3481367 : CollatzResearch.WordTrace tailWord_3481367 prefixEnd_3481367 1787614605701185869301991 := by
  unfold tailWord_3481367
  simp only [CollatzResearch.WordTrace]
  refine ⟨126975885978609403992562355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84650590652406269328374903 126975885978609403992562355)
  ·
    refine ⟨190463828967914105988843533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126975885978609403992562355 190463828967914105988843533)
    ·
      refine ⟨71423935862967789745816325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190463828967914105988843533 71423935862967789745816325)
      ·
        refine ⟨13391987974306460577340561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71423935862967789745816325 13391987974306460577340561)
        ·
          refine ⟨10043990980729845433005421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13391987974306460577340561 10043990980729845433005421)
          ·
            refine ⟨3766496617773692037377033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10043990980729845433005421 3766496617773692037377033)
            ·
              refine ⟨2824872463330269028032775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3766496617773692037377033 2824872463330269028032775)
              ·
                refine ⟨4237308694995403542049163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2824872463330269028032775 4237308694995403542049163)
                ·
                  refine ⟨6355963042493105313073745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4237308694995403542049163 6355963042493105313073745)
                  ·
                    refine ⟨4766972281869828984805309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6355963042493105313073745 4766972281869828984805309)
                    ·
                      refine ⟨1787614605701185869301991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4766972281869828984805309 1787614605701185869301991)
                      ·
                        rfl

theorem cell23_3481367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_3481367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481367 prefixEnd_3481367 := by exact prefixLift 3481367
  have htrace : WordTrace (prefixWord ++ tailWord_3481367) baseStart_3481367 baseEnd_3481367 := by
    simpa [prefixWord, tailWord_3481367, baseEnd_3481367] using wordTrace_append hprefix tailTrace_3481367
  have hstable : (prefixWord ++ tailWord_3481367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481367).length < 2 ^ (prefixWord ++ tailWord_3481367).sum := by decide
  have hdescent : baseEnd_3481367 < baseStart_3481367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481380 : List Nat := [2, 3, 1, 3, 2, 2, 1, 1, 4, 1, 3]
def baseStart_3481380 : Nat := 118140960795 + 3481380 * 2 ^ 59
def prefixEnd_3481380 : Nat := 4983230072969 + 3 ^ 40 * 3481380 * 2
def baseEnd_3481380 : Nat := 1787621280949694318439431

theorem tailTrace_3481380 : CollatzResearch.WordTrace tailWord_3481380 prefixEnd_3481380 1787621280949694318439431 := by
  unfold tailWord_3481380
  simp only [CollatzResearch.WordTrace]
  refine ⟨63488180063781153606392797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84650906751708204808523729 63488180063781153606392797)
  ·
    refine ⟨23808067523917932602397299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63488180063781153606392797 23808067523917932602397299)
    ·
      refine ⟨35712101285876898903595949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23808067523917932602397299 35712101285876898903595949)
      ·
        refine ⟨13392037982203837088848481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35712101285876898903595949 13392037982203837088848481)
        ·
          refine ⟨10044028486652877816636361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13392037982203837088848481 10044028486652877816636361)
          ·
            refine ⟨7533021364989658362477271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10044028486652877816636361 7533021364989658362477271)
            ·
              refine ⟨11299532047484487543715907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7533021364989658362477271 11299532047484487543715907)
              ·
                refine ⟨16949298071226731315573861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11299532047484487543715907 16949298071226731315573861)
                ·
                  refine ⟨3177993388355012121670099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16949298071226731315573861 3177993388355012121670099)
                  ·
                    refine ⟨4766990082532518182505149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3177993388355012121670099 4766990082532518182505149)
                    ·
                      refine ⟨1787621280949694318439431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4766990082532518182505149 1787621280949694318439431)
                      ·
                        rfl

theorem cell23_3481380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_3481380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481380 prefixEnd_3481380 := by exact prefixLift 3481380
  have htrace : WordTrace (prefixWord ++ tailWord_3481380) baseStart_3481380 baseEnd_3481380 := by
    simpa [prefixWord, tailWord_3481380, baseEnd_3481380] using wordTrace_append hprefix tailTrace_3481380
  have hstable : (prefixWord ++ tailWord_3481380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481380).length < 2 ^ (prefixWord ++ tailWord_3481380).sum := by decide
  have hdescent : baseEnd_3481380 < baseStart_3481380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481397 : List Nat := [1, 3, 3, 1, 5, 1, 1, 1, 1, 3, 3]
def baseStart_3481397 : Nat := 118140960795 + 3481397 * 2 ^ 59
def prefixEnd_3481397 : Nat := 4983230072969 + 3 ^ 40 * 3481397 * 2
def baseEnd_3481397 : Nat := 1787630010120820751926853

theorem tailTrace_3481397 : CollatzResearch.WordTrace tailWord_3481397 prefixEnd_3481397 1787630010120820751926853 := by
  unfold tailWord_3481397
  simp only [CollatzResearch.WordTrace]
  refine ⟨126976980168500719116154445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84651320112333812744102963 126976980168500719116154445)
  ·
    refine ⟨47616367563187769668557917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126976980168500719116154445 47616367563187769668557917)
    ·
      refine ⟨17856137836195413625709219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47616367563187769668557917 17856137836195413625709219)
      ·
        refine ⟨26784206754293120438563829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17856137836195413625709219 26784206754293120438563829)
        ·
          refine ⟨2511019383214980041115359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26784206754293120438563829 2511019383214980041115359)
          ·
            refine ⟨3766529074822470061673039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2511019383214980041115359 3766529074822470061673039)
            ·
              refine ⟨5649793612233705092509559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3766529074822470061673039 5649793612233705092509559)
              ·
                refine ⟨8474690418350557638764339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5649793612233705092509559 8474690418350557638764339)
                ·
                  refine ⟨12712035627525836458146509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8474690418350557638764339 12712035627525836458146509)
                  ·
                    refine ⟨4767013360322188671804941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12712035627525836458146509 4767013360322188671804941)
                    ·
                      refine ⟨1787630010120820751926853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4767013360322188671804941 1787630010120820751926853)
                      ·
                        rfl

theorem cell23_3481397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_3481397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481397 prefixEnd_3481397 := by exact prefixLift 3481397
  have htrace : WordTrace (prefixWord ++ tailWord_3481397) baseStart_3481397 baseEnd_3481397 := by
    simpa [prefixWord, tailWord_3481397, baseEnd_3481397] using wordTrace_append hprefix tailTrace_3481397
  have hstable : (prefixWord ++ tailWord_3481397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481397).length < 2 ^ (prefixWord ++ tailWord_3481397).sum := by decide
  have hdescent : baseEnd_3481397 < baseStart_3481397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481407 : List Nat := [1, 1, 2, 2, 6, 1, 2, 2, 1, 3, 2]
def baseStart_3481407 : Nat := 118140960795 + 3481407 * 2 ^ 59
def prefixEnd_3481407 : Nat := 4983230072969 + 3 ^ 40 * 3481407 * 2
def baseEnd_3481407 : Nat := 1787635144927365712801807

theorem tailTrace_3481407 : CollatzResearch.WordTrace tailWord_3481407 prefixEnd_3481407 1787635144927365712801807 := by
  unfold tailWord_3481407
  simp only [CollatzResearch.WordTrace]
  refine ⟨126977344898464490824018475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84651563265642993882678983 126977344898464490824018475)
  ·
    refine ⟨190466017347696736236027713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126977344898464490824018475 190466017347696736236027713)
    ·
      refine ⟨142849513010772552177020785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190466017347696736236027713 142849513010772552177020785)
      ·
        refine ⟨107137134758079414132765589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142849513010772552177020785 107137134758079414132765589)
        ·
          refine ⟨5022053191784972537473387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 107137134758079414132765589 5022053191784972537473387)
          ·
            refine ⟨7533079787677458806210081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5022053191784972537473387 7533079787677458806210081)
            ·
              refine ⟨5649809840758094104657561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7533079787677458806210081 5649809840758094104657561)
              ·
                refine ⟨4237357380568570578493171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5649809840758094104657561 4237357380568570578493171)
                ·
                  refine ⟨6356036070852855867739757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4237357380568570578493171 6356036070852855867739757)
                  ·
                    refine ⟨2383513526569820950402409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6356036070852855867739757 2383513526569820950402409)
                    ·
                      refine ⟨1787635144927365712801807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2383513526569820950402409 1787635144927365712801807)
                      ·
                        rfl

theorem cell23_3481407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 3, 2].length) (baseStart_3481407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481407 prefixEnd_3481407 := by exact prefixLift 3481407
  have htrace : WordTrace (prefixWord ++ tailWord_3481407) baseStart_3481407 baseEnd_3481407 := by
    simpa [prefixWord, tailWord_3481407, baseEnd_3481407] using wordTrace_append hprefix tailTrace_3481407
  have hstable : (prefixWord ++ tailWord_3481407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481407).length < 2 ^ (prefixWord ++ tailWord_3481407).sum := by decide
  have hdescent : baseEnd_3481407 < baseStart_3481407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481453 : List Nat := [1, 5, 1, 1, 1, 1, 2, 3, 2, 3, 3]
def baseStart_3481453 : Nat := 118140960795 + 3481453 * 2 ^ 59
def prefixEnd_3481453 : Nat := 4983230072969 + 3 ^ 40 * 3481453 * 2
def baseEnd_3481453 : Nat := 1787658765037472532826595

theorem tailTrace_3481453 : CollatzResearch.WordTrace tailWord_3481453 prefixEnd_3481453 1787658765037472532826595 := by
  unfold tailWord_3481453
  simp only [CollatzResearch.WordTrace]
  refine ⟨126979022656297840680193013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84652681770865227120128675 126979022656297840680193013)
  ·
    refine ⟨11904283374027922563768095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126979022656297840680193013 11904283374027922563768095)
    ·
      refine ⟨17856425061041883845652143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11904283374027922563768095 17856425061041883845652143)
      ·
        refine ⟨26784637591562825768478215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17856425061041883845652143 26784637591562825768478215)
        ·
          refine ⟨40176956387344238652717323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26784637591562825768478215 40176956387344238652717323)
          ·
            refine ⟨60265434581016357979075985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40176956387344238652717323 60265434581016357979075985)
            ·
              refine ⟨45199075935762268484306989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60265434581016357979075985 45199075935762268484306989)
              ·
                refine ⟨16949653475910850681615121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45199075935762268484306989 16949653475910850681615121)
                ·
                  refine ⟨12712240106933138011211341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16949653475910850681615121 12712240106933138011211341)
                  ·
                    refine ⟨4767090040099926754204253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12712240106933138011211341 4767090040099926754204253)
                    ·
                      refine ⟨1787658765037472532826595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4767090040099926754204253 1787658765037472532826595)
                      ·
                        rfl

theorem cell23_3481453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_3481453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481453 prefixEnd_3481453 := by exact prefixLift 3481453
  have htrace : WordTrace (prefixWord ++ tailWord_3481453) baseStart_3481453 baseEnd_3481453 := by
    simpa [prefixWord, tailWord_3481453, baseEnd_3481453] using wordTrace_append hprefix tailTrace_3481453
  have hstable : (prefixWord ++ tailWord_3481453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481453).length < 2 ^ (prefixWord ++ tailWord_3481453).sum := by decide
  have hdescent : baseEnd_3481453 < baseStart_3481453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481454 : List Nat := [4, 1, 2, 3, 1, 2, 1, 3, 2, 2, 2]
def baseStart_3481454 : Nat := 118140960795 + 3481454 * 2 ^ 59
def prefixEnd_3481454 : Nat := 4983230072969 + 3 ^ 40 * 3481454 * 2
def baseEnd_3481454 : Nat := 1787659278518127028914091

theorem tailTrace_3481454 : CollatzResearch.WordTrace tailWord_3481454 prefixEnd_3481454 1787659278518127028914091 := by
  unfold tailWord_3481454
  simp only [CollatzResearch.WordTrace]
  refine ⟨15872382391161777231372427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84652706086196145233986277 15872382391161777231372427)
  ·
    refine ⟨23808573586742665847058641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15872382391161777231372427 23808573586742665847058641)
    ·
      refine ⟨17856430190056999385293981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23808573586742665847058641 17856430190056999385293981)
      ·
        refine ⟨6696161321271374769485243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17856430190056999385293981 6696161321271374769485243)
        ·
          refine ⟨10044241981907062154227865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6696161321271374769485243 10044241981907062154227865)
          ·
            refine ⟨7533181486430296615670899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10044241981907062154227865 7533181486430296615670899)
            ·
              refine ⟨11299772229645444923506349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7533181486430296615670899 11299772229645444923506349)
              ·
                refine ⟨4237414586117041846314881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11299772229645444923506349 4237414586117041846314881)
                ·
                  refine ⟨3178060939587781384736161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4237414586117041846314881 3178060939587781384736161)
                  ·
                    refine ⟨2383545704690836038552121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3178060939587781384736161 2383545704690836038552121)
                    ·
                      refine ⟨1787659278518127028914091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2383545704690836038552121 1787659278518127028914091)
                      ·
                        rfl

theorem cell23_3481454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_3481454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481454 prefixEnd_3481454 := by exact prefixLift 3481454
  have htrace : WordTrace (prefixWord ++ tailWord_3481454) baseStart_3481454 baseEnd_3481454 := by
    simpa [prefixWord, tailWord_3481454, baseEnd_3481454] using wordTrace_append hprefix tailTrace_3481454
  have hstable : (prefixWord ++ tailWord_3481454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481454).length < 2 ^ (prefixWord ++ tailWord_3481454).sum := by decide
  have hdescent : baseEnd_3481454 < baseStart_3481454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481456 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 6, 5]
def baseStart_3481456 : Nat := 118140960795 + 3481456 * 2 ^ 59
def prefixEnd_3481456 : Nat := 4983230072969 + 3 ^ 40 * 3481456 * 2
def baseEnd_3481456 : Nat := 595886768493145340363027

theorem tailTrace_3481456 : CollatzResearch.WordTrace tailWord_3481456 prefixEnd_3481456 595886768493145340363027 := by
  unfold tailWord_3481456
  simp only [CollatzResearch.WordTrace]
  refine ⟨63489566037643486096276111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84652754716857981461701481 63489566037643486096276111)
  ·
    refine ⟨95234349056465229144414167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63489566037643486096276111 95234349056465229144414167)
    ·
      refine ⟨142851523584697843716621251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95234349056465229144414167 142851523584697843716621251)
      ·
        refine ⟨214277285377046765574931877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142851523584697843716621251 214277285377046765574931877)
        ·
          refine ⟨40176991008196268545299727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214277285377046765574931877 40176991008196268545299727)
          ·
            refine ⟨60265486512294402817949591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40176991008196268545299727 60265486512294402817949591)
            ·
              refine ⟨90398229768441604226924387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60265486512294402817949591 90398229768441604226924387)
              ·
                refine ⟨135597344652662406340386581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90398229768441604226924387 135597344652662406340386581)
                ·
                  refine ⟨6356125530593550297205621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135597344652662406340386581 6356125530593550297205621)
                  ·
                    refine ⟨595886768493145340363027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6356125530593550297205621 595886768493145340363027)
                    ·
                      rfl

theorem cell23_3481456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 6, 5].length) (baseStart_3481456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481456 prefixEnd_3481456 := by exact prefixLift 3481456
  have htrace : WordTrace (prefixWord ++ tailWord_3481456) baseStart_3481456 baseEnd_3481456 := by
    simpa [prefixWord, tailWord_3481456, baseEnd_3481456] using wordTrace_append hprefix tailTrace_3481456
  have hstable : (prefixWord ++ tailWord_3481456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481456).length < 2 ^ (prefixWord ++ tailWord_3481456).sum := by decide
  have hdescent : baseEnd_3481456 < baseStart_3481456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481490 : List Nat := [3, 2, 3, 2, 1, 1, 2, 2, 2, 5]
def baseStart_3481490 : Nat := 118140960795 + 3481490 * 2 ^ 59
def prefixEnd_3481490 : Nat := 4983230072969 + 3 ^ 40 * 3481490 * 2
def baseEnd_3481490 : Nat := 595892587940562962687975

theorem tailTrace_3481490 : CollatzResearch.WordTrace tailWord_3481490 prefixEnd_3481490 595892587940562962687975 := by
  unfold tailWord_3481490
  simp only [CollatzResearch.WordTrace]
  refine ⟨31745093039290948999822481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84653581438109197332859949 31745093039290948999822481)
  ·
    refine ⟨23808819779468211749866861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31745093039290948999822481 23808819779468211749866861)
    ·
      refine ⟨8928307417300579406200073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23808819779468211749866861 8928307417300579406200073)
      ·
        refine ⟨6696230562975434554650055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8928307417300579406200073 6696230562975434554650055)
        ·
          refine ⟨10044345844463151831975083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6696230562975434554650055 10044345844463151831975083)
          ·
            refine ⟨15066518766694727747962625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10044345844463151831975083 15066518766694727747962625)
            ·
              refine ⟨11299889075021045810971969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15066518766694727747962625 11299889075021045810971969)
              ·
                refine ⟨8474916806265784358228977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11299889075021045810971969 8474916806265784358228977)
                ·
                  refine ⟨6356187604699338268671733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8474916806265784358228977 6356187604699338268671733)
                  ·
                    refine ⟨595892587940562962687975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6356187604699338268671733 595892587940562962687975)
                    ·
                      rfl

theorem cell23_3481490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_3481490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481490 prefixEnd_3481490 := by exact prefixLift 3481490
  have htrace : WordTrace (prefixWord ++ tailWord_3481490) baseStart_3481490 baseEnd_3481490 := by
    simpa [prefixWord, tailWord_3481490, baseEnd_3481490] using wordTrace_append hprefix tailTrace_3481490
  have hstable : (prefixWord ++ tailWord_3481490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481490).length < 2 ^ (prefixWord ++ tailWord_3481490).sum := by decide
  have hdescent : baseEnd_3481490 < baseStart_3481490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481493 : List Nat := [1, 3, 2, 1, 1, 3, 1, 4, 2, 1, 4]
def baseStart_3481493 : Nat := 118140960795 + 3481493 * 2 ^ 59
def prefixEnd_3481493 : Nat := 4983230072969 + 3 ^ 40 * 3481493 * 2
def baseEnd_3481493 : Nat := 1787679304263652376326411

theorem tailTrace_3481493 : CollatzResearch.WordTrace tailWord_3481493 prefixEnd_3481493 1787679304263652376326411 := by
  unfold tailWord_3481493
  simp only [CollatzResearch.WordTrace]
  refine ⟨126980481576152927511649133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84653654384101951674432755 126980481576152927511649133)
  ·
    refine ⟨47617680591057347816868425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126980481576152927511649133 47617680591057347816868425)
    ·
      refine ⟨35713260443293010862651319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47617680591057347816868425 35713260443293010862651319)
      ·
        refine ⟨53569890664939516293976979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35713260443293010862651319 53569890664939516293976979)
        ·
          refine ⟨80354835997409274440965469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53569890664939516293976979 80354835997409274440965469)
          ·
            refine ⟨30133063499028477915362051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80354835997409274440965469 30133063499028477915362051)
            ·
              refine ⟨45199595248542716873043077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30133063499028477915362051 45199595248542716873043077)
              ·
                refine ⟨8474924109101759413695577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45199595248542716873043077 8474924109101759413695577)
                ·
                  refine ⟨6356193081826319560271683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8474924109101759413695577 6356193081826319560271683)
                  ·
                    refine ⟨9534289622739479340407525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6356193081826319560271683 9534289622739479340407525)
                    ·
                      refine ⟨1787679304263652376326411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9534289622739479340407525 1787679304263652376326411)
                      ·
                        rfl

theorem cell23_3481493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_3481493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481493 prefixEnd_3481493 := by exact prefixLift 3481493
  have htrace : WordTrace (prefixWord ++ tailWord_3481493) baseStart_3481493 baseEnd_3481493 := by
    simpa [prefixWord, tailWord_3481493, baseEnd_3481493] using wordTrace_append hprefix tailTrace_3481493
  have hstable : (prefixWord ++ tailWord_3481493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481493).length < 2 ^ (prefixWord ++ tailWord_3481493).sum := by decide
  have hdescent : baseEnd_3481493 < baseStart_3481493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481524 : List Nat := [2, 5, 2, 1, 2, 2, 1, 1, 2, 5]
def baseStart_3481524 : Nat := 118140960795 + 3481524 * 2 ^ 59
def prefixEnd_3481524 : Nat := 4983230072969 + 3 ^ 40 * 3481524 * 2
def baseEnd_3481524 : Nat := 595898407387980585012923

theorem tailTrace_3481524 : CollatzResearch.WordTrace tailWord_3481524 prefixEnd_3481524 595898407387980585012923 := by
  unfold tailWord_3481524
  simp only [CollatzResearch.WordTrace]
  refine ⟨63490806119520309903013813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84654408159360413204018417 63490806119520309903013813)
  ·
    refine ⟨5952263073705029053407545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63490806119520309903013813 5952263073705029053407545)
    ·
      refine ⟨4464197305278771790055659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5952263073705029053407545 4464197305278771790055659)
      ·
        refine ⟨6696295957918157685083489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4464197305278771790055659 6696295957918157685083489)
        ·
          refine ⟨5022221968438618263812617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6696295957918157685083489 5022221968438618263812617)
          ·
            refine ⟨3766666476328963697859463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5022221968438618263812617 3766666476328963697859463)
            ·
              refine ⟨5649999714493445546789195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3766666476328963697859463 5649999714493445546789195)
              ·
                refine ⟨8474999571740168320183793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5649999714493445546789195 8474999571740168320183793)
                ·
                  refine ⟨6356249678805126240137845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8474999571740168320183793 6356249678805126240137845)
                  ·
                    refine ⟨595898407387980585012923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6356249678805126240137845 595898407387980585012923)
                    ·
                      rfl

theorem cell23_3481524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_3481524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481524 prefixEnd_3481524 := by exact prefixLift 3481524
  have htrace : WordTrace (prefixWord ++ tailWord_3481524) baseStart_3481524 baseEnd_3481524 := by
    simpa [prefixWord, tailWord_3481524, baseEnd_3481524] using wordTrace_append hprefix tailTrace_3481524
  have hstable : (prefixWord ++ tailWord_3481524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481524).length < 2 ^ (prefixWord ++ tailWord_3481524).sum := by decide
  have hdescent : baseEnd_3481524 < baseStart_3481524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481637 : List Nat := [1, 3, 1, 2, 2, 3, 3, 2, 1, 2, 3]
def baseStart_3481637 : Nat := 118140960795 + 3481637 * 2 ^ 59
def prefixEnd_3481637 : Nat := 4983230072969 + 3 ^ 40 * 3481637 * 2
def baseEnd_3481637 : Nat := 1787753245477899812925749

theorem tailTrace_3481637 : CollatzResearch.WordTrace tailWord_3481637 prefixEnd_3481637 1787753245477899812925749 := by
  unfold tailWord_3481637
  simp only [CollatzResearch.WordTrace]
  refine ⟨126985733687631240104891165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84657155791754160069927443 126985733687631240104891165)
  ·
    refine ⟨47619650132861715039334187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126985733687631240104891165 47619650132861715039334187)
    ·
      refine ⟨71429475199292572559001281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47619650132861715039334187 71429475199292572559001281)
      ·
        refine ⟨53572106399469429419250961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71429475199292572559001281 53572106399469429419250961)
        ·
          refine ⟨40179079799602072064438221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53572106399469429419250961 40179079799602072064438221)
          ·
            refine ⟨15067154924850777024164333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40179079799602072064438221 15067154924850777024164333)
            ·
              refine ⟨5650183096819041384061625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15067154924850777024164333 5650183096819041384061625)
              ·
                refine ⟨4237637322614281038046219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5650183096819041384061625 4237637322614281038046219)
                ·
                  refine ⟨6356455983921421557069329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4237637322614281038046219 6356455983921421557069329)
                  ·
                    refine ⟨4767341987941066167801997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6356455983921421557069329 4767341987941066167801997)
                    ·
                      refine ⟨1787753245477899812925749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4767341987941066167801997 1787753245477899812925749)
                      ·
                        rfl

theorem cell23_3481637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_3481637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481637 prefixEnd_3481637 := by exact prefixLift 3481637
  have htrace : WordTrace (prefixWord ++ tailWord_3481637) baseStart_3481637 baseEnd_3481637 := by
    simpa [prefixWord, tailWord_3481637, baseEnd_3481637] using wordTrace_append hprefix tailTrace_3481637
  have hstable : (prefixWord ++ tailWord_3481637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481637).length < 2 ^ (prefixWord ++ tailWord_3481637).sum := by decide
  have hdescent : baseEnd_3481637 < baseStart_3481637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481650 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3]
def baseStart_3481650 : Nat := 118140960795 + 3481650 * 2 ^ 59
def prefixEnd_3481650 : Nat := 4983230072969 + 3 ^ 40 * 3481650 * 2
def baseEnd_3481650 : Nat := 1787759920726408262063189

theorem tailTrace_3481650 : CollatzResearch.WordTrace tailWord_3481650 prefixEnd_3481650 1787759920726408262063189 := by
  unfold tailWord_3481650
  simp only [CollatzResearch.WordTrace]
  refine ⟨31746551959146035831278601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84657471891056095550076269 31746551959146035831278601)
  ·
    refine ⟨23809913969359526873458951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31746551959146035831278601 23809913969359526873458951)
    ·
      refine ⟨35714870954039290310188427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23809913969359526873458951 35714870954039290310188427)
      ·
        refine ⟨53572306431058935465282641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35714870954039290310188427 53572306431058935465282641)
        ·
          refine ⟨40179229823294201598961981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53572306431058935465282641 40179229823294201598961981)
          ·
            refine ⟨15067211183735325599610743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40179229823294201598961981 15067211183735325599610743)
            ·
              refine ⟨22600816775602988399416115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15067211183735325599610743 22600816775602988399416115)
              ·
                refine ⟨33901225163404482599124173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22600816775602988399416115 33901225163404482599124173)
                ·
                  refine ⟨12712959436276680974671565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33901225163404482599124173 12712959436276680974671565)
                  ·
                    refine ⟨4767359788603755365501837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12712959436276680974671565 4767359788603755365501837)
                    ·
                      refine ⟨1787759920726408262063189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4767359788603755365501837 1787759920726408262063189)
                      ·
                        rfl

theorem cell23_3481650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_3481650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481650 prefixEnd_3481650 := by exact prefixLift 3481650
  have htrace : WordTrace (prefixWord ++ tailWord_3481650) baseStart_3481650 baseEnd_3481650 := by
    simpa [prefixWord, tailWord_3481650, baseEnd_3481650] using wordTrace_append hprefix tailTrace_3481650
  have hstable : (prefixWord ++ tailWord_3481650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481650).length < 2 ^ (prefixWord ++ tailWord_3481650).sum := by decide
  have hdescent : baseEnd_3481650 < baseStart_3481650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481663 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 5]
def baseStart_3481663 : Nat := 118140960795 + 3481663 * 2 ^ 59
def prefixEnd_3481663 : Nat := 4983230072969 + 3 ^ 40 * 3481663 * 2
def baseEnd_3481663 : Nat := 1787766595974916711200629

theorem tailTrace_3481663 : CollatzResearch.WordTrace tailWord_3481663 prefixEnd_3481663 1787766595974916711200629 := by
  unfold tailWord_3481663
  simp only [CollatzResearch.WordTrace]
  refine ⟨126986681985537046545337643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84657787990358031030225095 126986681985537046545337643)
  ·
    refine ⟨190480022978305569818006465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126986681985537046545337643 190480022978305569818006465)
    ·
      refine ⟨142860017233729177363504849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190480022978305569818006465 142860017233729177363504849)
      ·
        refine ⟨107145012925296883022628637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142860017233729177363504849 107145012925296883022628637)
        ·
          refine ⟨40179379846986331133485739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107145012925296883022628637 40179379846986331133485739)
          ·
            refine ⟨60269069770479496700228609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40179379846986331133485739 60269069770479496700228609)
            ·
              refine ⟨45201802327859622525171457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60269069770479496700228609 45201802327859622525171457)
              ·
                refine ⟨33901351745894716893878593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45201802327859622525171457 33901351745894716893878593)
                ·
                  refine ⟨25426013809421037670408945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33901351745894716893878593 25426013809421037670408945)
                  ·
                    refine ⟨19069510357065778252806709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25426013809421037670408945 19069510357065778252806709)
                    ·
                      refine ⟨1787766595974916711200629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19069510357065778252806709 1787766595974916711200629)
                      ·
                        rfl

theorem cell23_3481663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_3481663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481663 prefixEnd_3481663 := by exact prefixLift 3481663
  have htrace : WordTrace (prefixWord ++ tailWord_3481663) baseStart_3481663 baseEnd_3481663 := by
    simpa [prefixWord, tailWord_3481663, baseEnd_3481663] using wordTrace_append hprefix tailTrace_3481663
  have hstable : (prefixWord ++ tailWord_3481663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481663).length < 2 ^ (prefixWord ++ tailWord_3481663).sum := by decide
  have hdescent : baseEnd_3481663 < baseStart_3481663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481673 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 1, 5, 4]
def baseStart_3481673 : Nat := 118140960795 + 3481673 * 2 ^ 59
def prefixEnd_3481673 : Nat := 4983230072969 + 3 ^ 40 * 3481673 * 2
def baseEnd_3481673 : Nat := 1787771730781461672075583

theorem tailTrace_3481673 : CollatzResearch.WordTrace tailWord_3481673 prefixEnd_3481673 1787771730781461672075583 := by
  unfold tailWord_3481673
  simp only [CollatzResearch.WordTrace]
  refine ⟨126987046715500818253201673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84658031143667212168801115 126987046715500818253201673)
  ·
    refine ⟨95240285036625613689901255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126987046715500818253201673 95240285036625613689901255)
    ·
      refine ⟨142860427554938420534851883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95240285036625613689901255 142860427554938420534851883)
      ·
        refine ⟨214290641332407630802277825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142860427554938420534851883 214290641332407630802277825)
        ·
          refine ⟨160717980999305723101708369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214290641332407630802277825 160717980999305723101708369)
          ·
            refine ⟨120538485749479292326281277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160717980999305723101708369 120538485749479292326281277)
            ·
              refine ⟨45201932156054734622355479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120538485749479292326281277 45201932156054734622355479)
              ·
                refine ⟨67802898234082101933533219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45201932156054734622355479 67802898234082101933533219)
                ·
                  refine ⟨101704347351123152900299829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67802898234082101933533219 101704347351123152900299829)
                  ·
                    refine ⟨9534782564167795584403109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101704347351123152900299829 9534782564167795584403109)
                    ·
                      refine ⟨1787771730781461672075583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9534782564167795584403109 1787771730781461672075583)
                      ·
                        rfl

theorem cell23_3481673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 5, 4].length) (baseStart_3481673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481673 prefixEnd_3481673 := by exact prefixLift 3481673
  have htrace : WordTrace (prefixWord ++ tailWord_3481673) baseStart_3481673 baseEnd_3481673 := by
    simpa [prefixWord, tailWord_3481673, baseEnd_3481673] using wordTrace_append hprefix tailTrace_3481673
  have hstable : (prefixWord ++ tailWord_3481673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481673).length < 2 ^ (prefixWord ++ tailWord_3481673).sum := by decide
  have hdescent : baseEnd_3481673 < baseStart_3481673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481710 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5]
def baseStart_3481710 : Nat := 118140960795 + 3481710 * 2 ^ 59
def prefixEnd_3481710 : Nat := 4983230072969 + 3 ^ 40 * 3481710 * 2
def baseEnd_3481710 : Nat := 1787790729565678027312913

theorem tailTrace_3481710 : CollatzResearch.WordTrace tailWord_3481710 prefixEnd_3481710 1787790729565678027312913 := by
  unfold tailWord_3481710
  simp only [CollatzResearch.WordTrace]
  refine ⟨15873549527045846696537323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84658930810911182381532389 15873549527045846696537323)
  ·
    refine ⟨23810324290568770044805985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15873549527045846696537323 23810324290568770044805985)
    ·
      refine ⟨17857743217926577533604489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23810324290568770044805985 17857743217926577533604489)
      ·
        refine ⟨13393307413444933150203367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17857743217926577533604489 13393307413444933150203367)
        ·
          refine ⟨20089961120167399725305051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13393307413444933150203367 20089961120167399725305051)
          ·
            refine ⟨30134941680251099587957577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20089961120167399725305051 30134941680251099587957577)
            ·
              refine ⟨22601206260188324690968183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30134941680251099587957577 22601206260188324690968183)
              ·
                refine ⟨33901809390282487036452275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22601206260188324690968183 33901809390282487036452275)
                ·
                  refine ⟨50852714085423730554678413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33901809390282487036452275 50852714085423730554678413)
                  ·
                    refine ⟨19069767782033898958004405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50852714085423730554678413 19069767782033898958004405)
                    ·
                      refine ⟨1787790729565678027312913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19069767782033898958004405 1787790729565678027312913)
                      ·
                        rfl

theorem cell23_3481710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_3481710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481710 prefixEnd_3481710 := by exact prefixLift 3481710
  have htrace : WordTrace (prefixWord ++ tailWord_3481710) baseStart_3481710 baseEnd_3481710 := by
    simpa [prefixWord, tailWord_3481710, baseEnd_3481710] using wordTrace_append hprefix tailTrace_3481710
  have hstable : (prefixWord ++ tailWord_3481710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481710).length < 2 ^ (prefixWord ++ tailWord_3481710).sum := by decide
  have hdescent : baseEnd_3481710 < baseStart_3481710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481711 : List Nat := [1, 1, 2, 1, 3, 6, 2, 1, 1, 3, 2]
def baseStart_3481711 : Nat := 118140960795 + 3481711 * 2 ^ 59
def prefixEnd_3481711 : Nat := 4983230072969 + 3 ^ 40 * 3481711 * 2
def baseEnd_3481711 : Nat := 1787791243046332523400409

theorem tailTrace_3481711 : CollatzResearch.WordTrace tailWord_3481711 prefixEnd_3481711 1787791243046332523400409 := by
  unfold tailWord_3481711
  simp only [CollatzResearch.WordTrace]
  refine ⟨126988432689363150743084987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84658955126242100495389991 126988432689363150743084987)
  ·
    refine ⟨190482649034044726114627481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126988432689363150743084987 190482649034044726114627481)
    ·
      refine ⟨142861986775533544585970611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190482649034044726114627481 142861986775533544585970611)
      ·
        refine ⟨214292980163300316878955917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142861986775533544585970611 214292980163300316878955917)
        ·
          refine ⟨80359867561237618829608469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214292980163300316878955917 80359867561237618829608469)
          ·
            refine ⟨3766868791933013382637897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 80359867561237618829608469 3766868791933013382637897)
            ·
              refine ⟨2825151593949760036978423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3766868791933013382637897 2825151593949760036978423)
              ·
                refine ⟨4237727390924640055467635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2825151593949760036978423 4237727390924640055467635)
                ·
                  refine ⟨6356591086386960083201453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4237727390924640055467635 6356591086386960083201453)
                  ·
                    refine ⟨2383721657395110031200545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6356591086386960083201453 2383721657395110031200545)
                    ·
                      refine ⟨1787791243046332523400409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2383721657395110031200545 1787791243046332523400409)
                      ·
                        rfl

theorem cell23_3481711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 1, 3, 2].length) (baseStart_3481711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481711 prefixEnd_3481711 := by exact prefixLift 3481711
  have htrace : WordTrace (prefixWord ++ tailWord_3481711) baseStart_3481711 baseEnd_3481711 := by
    simpa [prefixWord, tailWord_3481711, baseEnd_3481711] using wordTrace_append hprefix tailTrace_3481711
  have hstable : (prefixWord ++ tailWord_3481711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481711).length < 2 ^ (prefixWord ++ tailWord_3481711).sum := by decide
  have hdescent : baseEnd_3481711 < baseStart_3481711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481713 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 9]
def baseStart_3481713 : Nat := 118140960795 + 3481713 * 2 ^ 59
def prefixEnd_3481713 : Nat := 4983230072969 + 3 ^ 40 * 3481713 * 2
def baseEnd_3481713 : Nat := 198643585556404612841711

theorem tailTrace_3481713 : CollatzResearch.WordTrace tailWord_3481713 prefixEnd_3481713 198643585556404612841711 := by
  unfold tailWord_3481713
  simp only [CollatzResearch.WordTrace]
  refine ⟨126988505635355905084657793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84659003756903936723105195 126988505635355905084657793)
  ·
    refine ⟨95241379226516928813493345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126988505635355905084657793 95241379226516928813493345)
    ·
      refine ⟨71431034419887696610120009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95241379226516928813493345 71431034419887696610120009)
      ·
        refine ⟨53573275814915772457590007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71431034419887696610120009 53573275814915772457590007)
        ·
          refine ⟨80359913722373658686385011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53573275814915772457590007 80359913722373658686385011)
          ·
            refine ⟨120539870583560488029577517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80359913722373658686385011 120539870583560488029577517)
            ·
              refine ⟨45202451468835183011091569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120539870583560488029577517 45202451468835183011091569)
              ·
                refine ⟨33901838601626387258318677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45202451468835183011091569 33901838601626387258318677)
                ·
                  refine ⟨198643585556404612841711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33901838601626387258318677 198643585556404612841711)
                  ·
                    rfl

theorem cell23_3481713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 9].length) (baseStart_3481713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481713 prefixEnd_3481713 := by exact prefixLift 3481713
  have htrace : WordTrace (prefixWord ++ tailWord_3481713) baseStart_3481713 baseEnd_3481713 := by
    simpa [prefixWord, tailWord_3481713, baseEnd_3481713] using wordTrace_append hprefix tailTrace_3481713
  have hstable : (prefixWord ++ tailWord_3481713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481713).length < 2 ^ (prefixWord ++ tailWord_3481713).sum := by decide
  have hdescent : baseEnd_3481713 < baseStart_3481713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481724 : List Nat := [2, 2, 2, 1, 1, 5, 1, 1, 4, 2, 2]
def baseStart_3481724 : Nat := 118140960795 + 3481724 * 2 ^ 59
def prefixEnd_3481724 : Nat := 4983230072969 + 3 ^ 40 * 3481724 * 2
def baseEnd_3481724 : Nat := 1787797918294840972537849

theorem tailTrace_3481724 : CollatzResearch.WordTrace tailWord_3481724 prefixEnd_3481724 1787797918294840972537849 := by
  unfold tailWord_3481724
  simp only [CollatzResearch.WordTrace]
  refine ⟨63494453419158026981654113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84659271225544035975538817 63494453419158026981654113)
  ·
    refine ⟨47620840064368520236240585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63494453419158026981654113 47620840064368520236240585)
    ·
      refine ⟨35715630048276390177180439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47620840064368520236240585 35715630048276390177180439)
      ·
        refine ⟨53573445072414585265770659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35715630048276390177180439 53573445072414585265770659)
        ·
          refine ⟨80360167608621877898655989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53573445072414585265770659 80360167608621877898655989)
          ·
            refine ⟨7533765713308301052998999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80360167608621877898655989 7533765713308301052998999)
            ·
              refine ⟨11300648569962451579498499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7533765713308301052998999 11300648569962451579498499)
              ·
                refine ⟨16950972854943677369247749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11300648569962451579498499 16950972854943677369247749)
                ·
                  refine ⟨3178307410301939506733953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16950972854943677369247749 3178307410301939506733953)
                  ·
                    refine ⟨2383730557726454630050465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3178307410301939506733953 2383730557726454630050465)
                    ·
                      refine ⟨1787797918294840972537849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2383730557726454630050465 1787797918294840972537849)
                      ·
                        rfl

theorem cell23_3481724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 4, 2, 2].length) (baseStart_3481724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481724 prefixEnd_3481724 := by exact prefixLift 3481724
  have htrace : WordTrace (prefixWord ++ tailWord_3481724) baseStart_3481724 baseEnd_3481724 := by
    simpa [prefixWord, tailWord_3481724, baseEnd_3481724] using wordTrace_append hprefix tailTrace_3481724
  have hstable : (prefixWord ++ tailWord_3481724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481724).length < 2 ^ (prefixWord ++ tailWord_3481724).sum := by decide
  have hdescent : baseEnd_3481724 < baseStart_3481724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481760 : List Nat := [2, 1, 1, 4, 2, 2, 2, 1, 1, 7]
def baseStart_3481760 : Nat := 118140960795 + 3481760 * 2 ^ 59
def prefixEnd_3481760 : Nat := 4983230072969 + 3 ^ 40 * 3481760 * 2
def baseEnd_3481760 : Nat := 595938801199467610562561

theorem tailTrace_3481760 : CollatzResearch.WordTrace tailWord_3481760 prefixEnd_3481760 595938801199467610562561 := by
  unfold tailWord_3481760
  simp only [CollatzResearch.WordTrace]
  refine ⟨63495109933092816055809367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84660146577457088074412489 63495109933092816055809367)
  ·
    refine ⟨95242664899639224083714051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63495109933092816055809367 95242664899639224083714051)
    ·
      refine ⟨142863997349458836125571077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95242664899639224083714051 142863997349458836125571077)
      ·
        refine ⟨26786999503023531773544577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142863997349458836125571077 26786999503023531773544577)
        ·
          refine ⟨20090249627267648830158433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26786999503023531773544577 20090249627267648830158433)
          ·
            refine ⟨15067687220450736622618825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20090249627267648830158433 15067687220450736622618825)
            ·
              refine ⟨11300765415338052466964119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15067687220450736622618825 11300765415338052466964119)
              ·
                refine ⟨16951148123007078700446179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11300765415338052466964119 16951148123007078700446179)
                ·
                  refine ⟨25426722184510618050669269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16951148123007078700446179 25426722184510618050669269)
                  ·
                    refine ⟨595938801199467610562561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25426722184510618050669269 595938801199467610562561)
                    ·
                      rfl

theorem cell23_3481760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 1, 7].length) (baseStart_3481760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481760 prefixEnd_3481760 := by exact prefixLift 3481760
  have htrace : WordTrace (prefixWord ++ tailWord_3481760) baseStart_3481760 baseEnd_3481760 := by
    simpa [prefixWord, tailWord_3481760, baseEnd_3481760] using wordTrace_append hprefix tailTrace_3481760
  have hstable : (prefixWord ++ tailWord_3481760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481760).length < 2 ^ (prefixWord ++ tailWord_3481760).sum := by decide
  have hdescent : baseEnd_3481760 < baseStart_3481760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481781 : List Nat := [1, 3, 3, 4, 2, 1, 1, 1, 7]
def baseStart_3481781 : Nat := 118140960795 + 3481781 * 2 ^ 59
def prefixEnd_3481781 : Nat := 4983230072969 + 3 ^ 40 * 3481781 * 2
def baseEnd_3481781 : Nat := 198647465188016361058343

theorem tailTrace_3481781 : CollatzResearch.WordTrace tailWord_3481781 prefixEnd_3481781 198647465188016361058343 := by
  unfold tailWord_3481781
  simp only [CollatzResearch.WordTrace]
  refine ⟨126990985799109552698133197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84660657199406368465422131 126990985799109552698133197)
  ·
    refine ⟨47621619674666082261799949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126990985799109552698133197 47621619674666082261799949)
    ·
      refine ⟨17858107377999780848174981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47621619674666082261799949 17858107377999780848174981)
      ·
        refine ⟨3348395133374958909032809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17858107377999780848174981 3348395133374958909032809)
        ·
          refine ⟨2511296350031219181774607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3348395133374958909032809 2511296350031219181774607)
          ·
            refine ⟨3766944525046828772661911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2511296350031219181774607 3766944525046828772661911)
            ·
              refine ⟨5650416787570243158992867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3766944525046828772661911 5650416787570243158992867)
              ·
                refine ⟨8475625181355364738489301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5650416787570243158992867 8475625181355364738489301)
                ·
                  refine ⟨198647465188016361058343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8475625181355364738489301 198647465188016361058343)
                  ·
                    rfl

theorem cell23_3481781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 7].length) (baseStart_3481781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481781 prefixEnd_3481781 := by exact prefixLift 3481781
  have htrace : WordTrace (prefixWord ++ tailWord_3481781) baseStart_3481781 baseEnd_3481781 := by
    simpa [prefixWord, tailWord_3481781, baseEnd_3481781] using wordTrace_append hprefix tailTrace_3481781
  have hstable : (prefixWord ++ tailWord_3481781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481781).length < 2 ^ (prefixWord ++ tailWord_3481781).sum := by decide
  have hdescent : baseEnd_3481781 < baseStart_3481781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481797 : List Nat := [1, 3, 1, 1, 1, 1, 4, 3, 2, 4, 2]
def baseStart_3481797 : Nat := 118140960795 + 3481797 * 2 ^ 59
def prefixEnd_3481797 : Nat := 4983230072969 + 3 ^ 40 * 3481797 * 2
def baseEnd_3481797 : Nat := 1787835402382619186925013

theorem tailTrace_3481797 : CollatzResearch.WordTrace tailWord_3481797 prefixEnd_3481797 1787835402382619186925013 := by
  unfold tailWord_3481797
  simp only [CollatzResearch.WordTrace]
  refine ⟨126991569367051587430715645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84661046244701058287143763 126991569367051587430715645)
  ·
    refine ⟨47621838512644345286518367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126991569367051587430715645 47621838512644345286518367)
    ·
      refine ⟨71432757768966517929777551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47621838512644345286518367 71432757768966517929777551)
      ·
        refine ⟨107149136653449776894666327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71432757768966517929777551 107149136653449776894666327)
        ·
          refine ⟨160723704980174665341999491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107149136653449776894666327 160723704980174665341999491)
          ·
            refine ⟨241085557470261998012999237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160723704980174665341999491 241085557470261998012999237)
            ·
              refine ⟨45203542025674124627437357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 241085557470261998012999237 45203542025674124627437357)
              ·
                refine ⟨16951328259627796735289009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45203542025674124627437357 16951328259627796735289009)
                ·
                  refine ⟨12713496194720847551466757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16951328259627796735289009 12713496194720847551466757)
                  ·
                    refine ⟨2383780536510158915900017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12713496194720847551466757 2383780536510158915900017)
                    ·
                      refine ⟨1787835402382619186925013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2383780536510158915900017 1787835402382619186925013)
                      ·
                        rfl

theorem cell23_3481797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 4, 2].length) (baseStart_3481797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481797 prefixEnd_3481797 := by exact prefixLift 3481797
  have htrace : WordTrace (prefixWord ++ tailWord_3481797) baseStart_3481797 baseEnd_3481797 := by
    simpa [prefixWord, tailWord_3481797, baseEnd_3481797] using wordTrace_append hprefix tailTrace_3481797
  have hstable : (prefixWord ++ tailWord_3481797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481797).length < 2 ^ (prefixWord ++ tailWord_3481797).sum := by decide
  have hdescent : baseEnd_3481797 < baseStart_3481797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481817 : List Nat := [1, 2, 1, 2, 3, 1, 3, 3, 2, 2, 3]
def baseStart_3481817 : Nat := 118140960795 + 3481817 * 2 ^ 59
def prefixEnd_3481817 : Nat := 4983230072969 + 3 ^ 40 * 3481817 * 2
def baseEnd_3481817 : Nat := 1787845671995709108674921

theorem tailTrace_3481817 : CollatzResearch.WordTrace tailWord_3481817 prefixEnd_3481817 1787845671995709108674921 := by
  unfold tailWord_3481817
  simp only [CollatzResearch.WordTrace]
  refine ⟨126992298826979130846443705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84661532551319420564295803 126992298826979130846443705)
  ·
    refine ⟨95244224120234348134832779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126992298826979130846443705 95244224120234348134832779)
    ·
      refine ⟨142866336180351522202249169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95244224120234348134832779 142866336180351522202249169)
      ·
        refine ⟨107149752135263641651686877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142866336180351522202249169 107149752135263641651686877)
        ·
          refine ⟨40181157050723865619382579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107149752135263641651686877 40181157050723865619382579)
          ·
            refine ⟨60271735576085798429073869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40181157050723865619382579 60271735576085798429073869)
            ·
              refine ⟨22601900841032174410902701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60271735576085798429073869 22601900841032174410902701)
              ·
                refine ⟨8475712815387065404088513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22601900841032174410902701 8475712815387065404088513)
                ·
                  refine ⟨6356784611540299053066385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8475712815387065404088513 6356784611540299053066385)
                  ·
                    refine ⟨4767588458655224289799789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6356784611540299053066385 4767588458655224289799789)
                    ·
                      refine ⟨1787845671995709108674921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4767588458655224289799789 1787845671995709108674921)
                      ·
                        rfl

theorem cell23_3481817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 2, 3].length) (baseStart_3481817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481817 prefixEnd_3481817 := by exact prefixLift 3481817
  have htrace : WordTrace (prefixWord ++ tailWord_3481817) baseStart_3481817 baseEnd_3481817 := by
    simpa [prefixWord, tailWord_3481817, baseEnd_3481817] using wordTrace_append hprefix tailTrace_3481817
  have hstable : (prefixWord ++ tailWord_3481817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481817).length < 2 ^ (prefixWord ++ tailWord_3481817).sum := by decide
  have hdescent : baseEnd_3481817 < baseStart_3481817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481824 : List Nat := [2, 1, 1, 3, 1, 3, 2, 5, 1, 4]
def baseStart_3481824 : Nat := 118140960795 + 3481824 * 2 ^ 59
def prefixEnd_3481824 : Nat := 4983230072969 + 3 ^ 40 * 3481824 * 2
def baseEnd_3481824 : Nat := 595949755453430193762463

theorem tailTrace_3481824 : CollatzResearch.WordTrace tailWord_3481824 prefixEnd_3481824 595949755453430193762463 := by
  unfold tailWord_3481824
  simp only [CollatzResearch.WordTrace]
  refine ⟨63496277068976885520974263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84661702758635847361299017 63496277068976885520974263)
  ·
    refine ⟨95244415603465328281461395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63496277068976885520974263 95244415603465328281461395)
    ·
      refine ⟨142866623405197992422192093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95244415603465328281461395 142866623405197992422192093)
      ·
        refine ⟨53574983776949247158322035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142866623405197992422192093 53574983776949247158322035)
        ·
          refine ⟨80362475665423870737483053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53574983776949247158322035 80362475665423870737483053)
          ·
            refine ⟨30135928374533951526556145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80362475665423870737483053 30135928374533951526556145)
            ·
              refine ⟨22601946280900463644917109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30135928374533951526556145 22601946280900463644917109)
              ·
                refine ⟨2118932463834418466710979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22601946280900463644917109 2118932463834418466710979)
                ·
                  refine ⟨3178398695751627700066469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2118932463834418466710979 3178398695751627700066469)
                  ·
                    refine ⟨595949755453430193762463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3178398695751627700066469 595949755453430193762463)
                    ·
                      rfl

theorem cell23_3481824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 5, 1, 4].length) (baseStart_3481824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481824 prefixEnd_3481824 := by exact prefixLift 3481824
  have htrace : WordTrace (prefixWord ++ tailWord_3481824) baseStart_3481824 baseEnd_3481824 := by
    simpa [prefixWord, tailWord_3481824, baseEnd_3481824] using wordTrace_append hprefix tailTrace_3481824
  have hstable : (prefixWord ++ tailWord_3481824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481824).length < 2 ^ (prefixWord ++ tailWord_3481824).sum := by decide
  have hdescent : baseEnd_3481824 < baseStart_3481824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481841 : List Nat := [1, 2, 2, 2, 2, 1, 6, 2, 1, 4]
def baseStart_3481841 : Nat := 118140960795 + 3481841 * 2 ^ 59
def prefixEnd_3481841 : Nat := 4983230072969 + 3 ^ 40 * 3481841 * 2
def baseEnd_3481841 : Nat := 595952665177139004924937

theorem tailTrace_3481841 : CollatzResearch.WordTrace tailWord_3481841 prefixEnd_3481841 595952665177139004924937 := by
  unfold tailWord_3481841
  simp only [CollatzResearch.WordTrace]
  refine ⟨126993174178892182945317377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84662116119261455296878251 126993174178892182945317377)
  ·
    refine ⟨95244880634169137208988033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126993174178892182945317377 95244880634169137208988033)
    ·
      refine ⟨71433660475626852906741025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95244880634169137208988033 71433660475626852906741025)
      ·
        refine ⟨53575245356720139680055769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71433660475626852906741025 53575245356720139680055769)
        ·
          refine ⟨40181434017540104760041827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53575245356720139680055769 40181434017540104760041827)
          ·
            refine ⟨60272151026310157140062741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40181434017540104760041827 60272151026310157140062741)
            ·
              refine ⟨2825257079358288615940441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60272151026310157140062741 2825257079358288615940441)
              ·
                refine ⟨2118942809518716461955331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2825257079358288615940441 2118942809518716461955331)
                ·
                  refine ⟨3178414214278074692932997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2118942809518716461955331 3178414214278074692932997)
                  ·
                    refine ⟨595952665177139004924937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3178414214278074692932997 595952665177139004924937)
                    ·
                      rfl

theorem cell23_3481841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 2, 1, 4].length) (baseStart_3481841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481841 prefixEnd_3481841 := by exact prefixLift 3481841
  have htrace : WordTrace (prefixWord ++ tailWord_3481841) baseStart_3481841 baseEnd_3481841 := by
    simpa [prefixWord, tailWord_3481841, baseEnd_3481841] using wordTrace_append hprefix tailTrace_3481841
  have hstable : (prefixWord ++ tailWord_3481841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481841).length < 2 ^ (prefixWord ++ tailWord_3481841).sum := by decide
  have hdescent : baseEnd_3481841 < baseStart_3481841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481864 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 5, 1, 3]
def baseStart_3481864 : Nat := 118140960795 + 3481864 * 2 ^ 59
def prefixEnd_3481864 : Nat := 4983230072969 + 3 ^ 40 * 3481864 * 2
def baseEnd_3481864 : Nat := 1787869805586470424787205

theorem tailTrace_3481864 : CollatzResearch.WordTrace tailWord_3481864 prefixEnd_3481864 1787869805586470424787205 := by
  unfold tailWord_3481864
  simp only [CollatzResearch.WordTrace]
  refine ⟨63497006528904428936702323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84662675371872571915603097 63497006528904428936702323)
  ·
    refine ⟨95245509793356643405053485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63497006528904428936702323 95245509793356643405053485)
    ·
      refine ⟨35717066172508741276895057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95245509793356643405053485 35717066172508741276895057)
      ·
        refine ⟨26787799629381555957671293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35717066172508741276895057 26787799629381555957671293)
        ·
          refine ⟨10045424861018083484126735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26787799629381555957671293 10045424861018083484126735)
          ·
            refine ⟨15068137291527125226190103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10045424861018083484126735 15068137291527125226190103)
            ·
              refine ⟨22602205937290687839285155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15068137291527125226190103 22602205937290687839285155)
              ·
                refine ⟨33903308905936031758927733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22602205937290687839285155 33903308905936031758927733)
                ·
                  refine ⟨3178435209931502977399475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33903308905936031758927733 3178435209931502977399475)
                  ·
                    refine ⟨4767652814897254466099213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3178435209931502977399475 4767652814897254466099213)
                    ·
                      refine ⟨1787869805586470424787205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4767652814897254466099213 1787869805586470424787205)
                      ·
                        rfl

theorem cell23_3481864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_3481864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481864 prefixEnd_3481864 := by exact prefixLift 3481864
  have htrace : WordTrace (prefixWord ++ tailWord_3481864) baseStart_3481864 baseEnd_3481864 := by
    simpa [prefixWord, tailWord_3481864, baseEnd_3481864] using wordTrace_append hprefix tailTrace_3481864
  have hstable : (prefixWord ++ tailWord_3481864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481864).length < 2 ^ (prefixWord ++ tailWord_3481864).sum := by decide
  have hdescent : baseEnd_3481864 < baseStart_3481864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481867 : List Nat := [1, 1, 1, 1, 5, 2, 2, 4, 1, 5]
def baseStart_3481867 : Nat := 118140960795 + 3481867 * 2 ^ 59
def prefixEnd_3481867 : Nat := 4983230072969 + 3 ^ 40 * 3481867 * 2
def baseEnd_3481867 : Nat := 595957115342811304349897

theorem tailTrace_3481867 : CollatzResearch.WordTrace tailWord_3481867 prefixEnd_3481867 595957115342811304349897 := by
  unfold tailWord_3481867
  simp only [CollatzResearch.WordTrace]
  refine ⟨126994122476797989385763855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84662748317865326257175903 126994122476797989385763855)
  ·
    refine ⟨190491183715196984078645783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126994122476797989385763855 190491183715196984078645783)
    ·
      refine ⟨285736775572795476117968675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190491183715196984078645783 285736775572795476117968675)
      ·
        refine ⟨428605163359193214176953013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285736775572795476117968675 428605163359193214176953013)
        ·
          refine ⟨40181734064924363829089345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 428605163359193214176953013 40181734064924363829089345)
          ·
            refine ⟨30136300548693272871817009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40181734064924363829089345 30136300548693272871817009)
            ·
              refine ⟨22602225411519954653862757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30136300548693272871817009 22602225411519954653862757)
              ·
                refine ⟨4237917264659991497599267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22602225411519954653862757 4237917264659991497599267)
                ·
                  refine ⟨6356875896989987246398901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4237917264659991497599267 6356875896989987246398901)
                  ·
                    refine ⟨595957115342811304349897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6356875896989987246398901 595957115342811304349897)
                    ·
                      rfl

theorem cell23_3481867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 5].length) (baseStart_3481867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481867 prefixEnd_3481867 := by exact prefixLift 3481867
  have htrace : WordTrace (prefixWord ++ tailWord_3481867) baseStart_3481867 baseEnd_3481867 := by
    simpa [prefixWord, tailWord_3481867, baseEnd_3481867] using wordTrace_append hprefix tailTrace_3481867
  have hstable : (prefixWord ++ tailWord_3481867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481867).length < 2 ^ (prefixWord ++ tailWord_3481867).sum := by decide
  have hdescent : baseEnd_3481867 < baseStart_3481867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481898 : List Nat := [3, 1, 4, 2, 2, 1, 2, 1, 3, 1, 3]
def baseStart_3481898 : Nat := 118140960795 + 3481898 * 2 ^ 59
def prefixEnd_3481898 : Nat := 4983230072969 + 3 ^ 40 * 3481898 * 2
def baseEnd_3481898 : Nat := 1787887263928723291762049

theorem tailTrace_3481898 : CollatzResearch.WordTrace tailWord_3481898 prefixEnd_3481898 1787887263928723291762049 := by
  unfold tailWord_3481898
  simp only [CollatzResearch.WordTrace]
  refine ⟨31748813284921420420035587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84663502093123787786761565 31748813284921420420035587)
  ·
    refine ⟨47623219927382130630053381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31748813284921420420035587 47623219927382130630053381)
    ·
      refine ⟨8929353736384149493135009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47623219927382130630053381 8929353736384149493135009)
      ·
        refine ⟨6697015302288112119851257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8929353736384149493135009 6697015302288112119851257)
        ·
          refine ⟨5022761476716084089888443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6697015302288112119851257 5022761476716084089888443)
          ·
            refine ⟨7534142215074126134832665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5022761476716084089888443 7534142215074126134832665)
            ·
              refine ⟨5650606661305594601124499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7534142215074126134832665 5650606661305594601124499)
              ·
                refine ⟨8475909991958391901686749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5650606661305594601124499 8475909991958391901686749)
                ·
                  refine ⟨3178466246984396963132531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8475909991958391901686749 3178466246984396963132531)
                  ·
                    refine ⟨4767699370476595444698797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3178466246984396963132531 4767699370476595444698797)
                    ·
                      refine ⟨1787887263928723291762049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4767699370476595444698797 1787887263928723291762049)
                      ·
                        rfl

theorem cell23_3481898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_3481898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481898 prefixEnd_3481898 := by exact prefixLift 3481898
  have htrace : WordTrace (prefixWord ++ tailWord_3481898) baseStart_3481898 baseEnd_3481898 := by
    simpa [prefixWord, tailWord_3481898, baseEnd_3481898] using wordTrace_append hprefix tailTrace_3481898
  have hstable : (prefixWord ++ tailWord_3481898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481898).length < 2 ^ (prefixWord ++ tailWord_3481898).sum := by decide
  have hdescent : baseEnd_3481898 < baseStart_3481898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481907 : List Nat := [1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 5]
def baseStart_3481907 : Nat := 118140960795 + 3481907 * 2 ^ 59
def prefixEnd_3481907 : Nat := 4983230072969 + 3 ^ 40 * 3481907 * 2
def baseEnd_3481907 : Nat := 1787891885254613756549507

theorem tailTrace_3481907 : CollatzResearch.WordTrace tailWord_3481907 prefixEnd_3481907 1787891885254613756549507 := by
  unfold tailWord_3481907
  simp only [CollatzResearch.WordTrace]
  refine ⟨126995581396653076217219975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84663720931102050811479983 126995581396653076217219975)
  ·
    refine ⟨190493372094979614325829963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126995581396653076217219975 190493372094979614325829963)
    ·
      refine ⟨285740058142469421488744945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190493372094979614325829963 285740058142469421488744945)
      ·
        refine ⟨214305043606852066116558709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285740058142469421488744945 214305043606852066116558709)
        ·
          refine ⟨20091097838142381198427379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 214305043606852066116558709 20091097838142381198427379)
          ·
            refine ⟨30136646757213571797641069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20091097838142381198427379 30136646757213571797641069)
            ·
              refine ⟨11301242533955089424115401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30136646757213571797641069 11301242533955089424115401)
              ·
                refine ⟨8475931900466317068086551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11301242533955089424115401 8475931900466317068086551)
                ·
                  refine ⟨12713897850699475602129827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8475931900466317068086551 12713897850699475602129827)
                  ·
                    refine ⟨19070846776049213403194741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12713897850699475602129827 19070846776049213403194741)
                    ·
                      refine ⟨1787891885254613756549507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19070846776049213403194741 1787891885254613756549507)
                      ·
                        rfl

theorem cell23_3481907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 5].length) (baseStart_3481907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481907 prefixEnd_3481907 := by exact prefixLift 3481907
  have htrace : WordTrace (prefixWord ++ tailWord_3481907) baseStart_3481907 baseEnd_3481907 := by
    simpa [prefixWord, tailWord_3481907, baseEnd_3481907] using wordTrace_append hprefix tailTrace_3481907
  have hstable : (prefixWord ++ tailWord_3481907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481907).length < 2 ^ (prefixWord ++ tailWord_3481907).sum := by decide
  have hdescent : baseEnd_3481907 < baseStart_3481907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481914 : List Nat := [3, 1, 1, 1, 4, 4, 1, 1, 1, 6]
def baseStart_3481914 : Nat := 118140960795 + 3481914 * 2 ^ 59
def prefixEnd_3481914 : Nat := 4983230072969 + 3 ^ 40 * 3481914 * 2
def baseEnd_3481914 : Nat := 595965159873065076387325

theorem tailTrace_3481914 : CollatzResearch.WordTrace tailWord_3481914 prefixEnd_3481914 595965159873065076387325 := by
  unfold tailWord_3481914
  simp only [CollatzResearch.WordTrace]
  refine ⟨31748959176906929103181199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84663891138418477608483197 31748959176906929103181199)
  ·
    refine ⟨47623438765360393654771799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31748959176906929103181199 47623438765360393654771799)
    ·
      refine ⟨71435158148040590482157699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47623438765360393654771799 71435158148040590482157699)
      ·
        refine ⟨107152737222060885723236549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71435158148040590482157699 107152737222060885723236549)
        ·
          refine ⟨20091138229136416073106853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107152737222060885723236549 20091138229136416073106853)
          ·
            refine ⟨3767088417963078013707535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20091138229136416073106853 3767088417963078013707535)
            ·
              refine ⟨5650632626944617020561303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3767088417963078013707535 5650632626944617020561303)
              ·
                refine ⟨8475948940416925530841955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5650632626944617020561303 8475948940416925530841955)
                ·
                  refine ⟨12713923410625388296262933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8475948940416925530841955 12713923410625388296262933)
                  ·
                    refine ⟨595965159873065076387325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12713923410625388296262933 595965159873065076387325)
                    ·
                      rfl

theorem cell23_3481914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 1, 6].length) (baseStart_3481914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481914 prefixEnd_3481914 := by exact prefixLift 3481914
  have htrace : WordTrace (prefixWord ++ tailWord_3481914) baseStart_3481914 baseEnd_3481914 := by
    simpa [prefixWord, tailWord_3481914, baseEnd_3481914] using wordTrace_append hprefix tailTrace_3481914
  have hstable : (prefixWord ++ tailWord_3481914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481914).length < 2 ^ (prefixWord ++ tailWord_3481914).sum := by decide
  have hdescent : baseEnd_3481914 < baseStart_3481914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481955 : List Nat := [1, 1, 1, 5, 2, 1, 5, 2, 1, 2, 2]
def baseStart_3481955 : Nat := 118140960795 + 3481955 * 2 ^ 59
def prefixEnd_3481955 : Nat := 4983230072969 + 3 ^ 40 * 3481955 * 2
def baseEnd_3481955 : Nat := 1787916532326029568749287

theorem tailTrace_3481955 : CollatzResearch.WordTrace tailWord_3481955 prefixEnd_3481955 1787916532326029568749287 := by
  unfold tailWord_3481955
  simp only [CollatzResearch.WordTrace]
  refine ⟨126997332100479180414967319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84664888066986120276644879 126997332100479180414967319)
  ·
    refine ⟨190495998150718770622450979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126997332100479180414967319 190495998150718770622450979)
    ·
      refine ⟨285743997226078155933676469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190495998150718770622450979 285743997226078155933676469)
      ·
        refine ⟨26788499739944827118782169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 285743997226078155933676469 26788499739944827118782169)
        ·
          refine ⟨20091374804958620339086627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26788499739944827118782169 20091374804958620339086627)
          ·
            refine ⟨30137062207437930508629941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20091374804958620339086627 30137062207437930508629941)
            ·
              refine ⟨2825349581947305985184057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30137062207437930508629941 2825349581947305985184057)
              ·
                refine ⟨2119012186460479488888043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2825349581947305985184057 2119012186460479488888043)
                ·
                  refine ⟨3178518279690719233332065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2119012186460479488888043 3178518279690719233332065)
                  ·
                    refine ⟨2383888709768039424999049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3178518279690719233332065 2383888709768039424999049)
                    ·
                      refine ⟨1787916532326029568749287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2383888709768039424999049 1787916532326029568749287)
                      ·
                        rfl

theorem cell23_3481955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_3481955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481955 prefixEnd_3481955 := by exact prefixLift 3481955
  have htrace : WordTrace (prefixWord ++ tailWord_3481955) baseStart_3481955 baseEnd_3481955 := by
    simpa [prefixWord, tailWord_3481955, baseEnd_3481955] using wordTrace_append hprefix tailTrace_3481955
  have hstable : (prefixWord ++ tailWord_3481955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481955).length < 2 ^ (prefixWord ++ tailWord_3481955).sum := by decide
  have hdescent : baseEnd_3481955 < baseStart_3481955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481981 : List Nat := [1, 4, 1, 1, 2, 4, 1, 1, 3, 3, 2]
def baseStart_3481981 : Nat := 118140960795 + 3481981 * 2 ^ 59
def prefixEnd_3481981 : Nat := 4983230072969 + 3 ^ 40 * 3481981 * 2
def baseEnd_3481981 : Nat := 1787929882823046467024167

theorem tailTrace_3481981 : CollatzResearch.WordTrace tailWord_3481981 prefixEnd_3481981 1787929882823046467024167 := by
  unfold tailWord_3481981
  simp only [CollatzResearch.WordTrace]
  refine ⟨126998280398384986855413797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84665520265589991236942531 126998280398384986855413797)
  ·
    refine ⟨23812177574697185035390087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126998280398384986855413797 23812177574697185035390087)
    ·
      refine ⟨35718266362045777553085131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23812177574697185035390087 35718266362045777553085131)
      ·
        refine ⟨53577399543068666329627697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35718266362045777553085131 53577399543068666329627697)
        ·
          refine ⟨40183049657301499747220773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53577399543068666329627697 40183049657301499747220773)
          ·
            refine ⟨7534321810744031202603895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40183049657301499747220773 7534321810744031202603895)
            ·
              refine ⟨11301482716116046803905843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7534321810744031202603895 11301482716116046803905843)
              ·
                refine ⟨16952224074174070205858765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11301482716116046803905843 16952224074174070205858765)
                ·
                  refine ⟨6357084027815276327197037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16952224074174070205858765 6357084027815276327197037)
                  ·
                    refine ⟨2383906510430728622698889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6357084027815276327197037 2383906510430728622698889)
                    ·
                      refine ⟨1787929882823046467024167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2383906510430728622698889 1787929882823046467024167)
                      ·
                        rfl

theorem cell23_3481981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 3, 2].length) (baseStart_3481981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3481981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3481981 prefixEnd_3481981 := by exact prefixLift 3481981
  have htrace : WordTrace (prefixWord ++ tailWord_3481981) baseStart_3481981 baseEnd_3481981 := by
    simpa [prefixWord, tailWord_3481981, baseEnd_3481981] using wordTrace_append hprefix tailTrace_3481981
  have hstable : (prefixWord ++ tailWord_3481981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481981).length < 2 ^ (prefixWord ++ tailWord_3481981).sum := by decide
  have hdescent : baseEnd_3481981 < baseStart_3481981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482006 : List Nat := [5, 3, 1, 2, 1, 1, 1, 4, 1, 2, 2]
def baseStart_3482006 : Nat := 118140960795 + 3482006 * 2 ^ 59
def prefixEnd_3482006 : Nat := 4983230072969 + 3 ^ 40 * 3482006 * 2
def baseEnd_3482006 : Nat := 1787942719839408869211553

theorem tailTrace_3482006 : CollatzResearch.WordTrace tailWord_3482006 prefixEnd_3482006 1787942719839408869211553 := by
  unfold tailWord_3482006
  simp only [CollatzResearch.WordTrace]
  refine ⟨7937449513955901007817117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84666128148862944083382581 7937449513955901007817117)
  ·
    refine ⟨2976543567733462877931419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7937449513955901007817117 2976543567733462877931419)
    ·
      refine ⟨4464815351600194316897129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2976543567733462877931419 4464815351600194316897129)
      ·
        refine ⟨3348611513700145737672847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4464815351600194316897129 3348611513700145737672847)
        ·
          refine ⟨5022917270550218606509271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3348611513700145737672847 5022917270550218606509271)
          ·
            refine ⟨7534375905825327909763907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5022917270550218606509271 7534375905825327909763907)
            ·
              refine ⟨11301563858737991864645861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7534375905825327909763907 11301563858737991864645861)
              ·
                refine ⟨2119043223513373474621099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11301563858737991864645861 2119043223513373474621099)
                ·
                  refine ⟨3178564835270060211931649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2119043223513373474621099 3178564835270060211931649)
                  ·
                    refine ⟨2383923626452545158948737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3178564835270060211931649 2383923626452545158948737)
                    ·
                      refine ⟨1787942719839408869211553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2383923626452545158948737 1787942719839408869211553)
                      ·
                        rfl

theorem cell23_3482006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_3482006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482006 prefixEnd_3482006 := by exact prefixLift 3482006
  have htrace : WordTrace (prefixWord ++ tailWord_3482006) baseStart_3482006 baseEnd_3482006 := by
    simpa [prefixWord, tailWord_3482006, baseEnd_3482006] using wordTrace_append hprefix tailTrace_3482006
  have hstable : (prefixWord ++ tailWord_3482006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482006).length < 2 ^ (prefixWord ++ tailWord_3482006).sum := by decide
  have hdescent : baseEnd_3482006 < baseStart_3482006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482057 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 3, 2, 5]
def baseStart_3482057 : Nat := 118140960795 + 3482057 * 2 ^ 59
def prefixEnd_3482057 : Nat := 4983230072969 + 3 ^ 40 * 3482057 * 2
def baseEnd_3482057 : Nat := 1787968907352788169673817

theorem tailTrace_3482057 : CollatzResearch.WordTrace tailWord_3482057 prefixEnd_3482057 1787968907352788169673817 := by
  unfold tailWord_3482057
  simp only [CollatzResearch.WordTrace]
  refine ⟨127001052346109651835180425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84667368230739767890120283 127001052346109651835180425)
  ·
    refine ⟨95250789259582238876385319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127001052346109651835180425 95250789259582238876385319)
    ·
      refine ⟨142876183889373358314577979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95250789259582238876385319 142876183889373358314577979)
      ·
        refine ⟨214314275834060037471866969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142876183889373358314577979 214314275834060037471866969)
        ·
          refine ⟨160735706875545028103900227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214314275834060037471866969 160735706875545028103900227)
          ·
            refine ⟨241103560313317542155850341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160735706875545028103900227 241103560313317542155850341)
            ·
              refine ⟨45206917558747039154221939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 241103560313317542155850341 45206917558747039154221939)
              ·
                refine ⟨67810376338120558731332909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45206917558747039154221939 67810376338120558731332909)
                ·
                  refine ⟨25428891126795209524249841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67810376338120558731332909 25428891126795209524249841)
                  ·
                    refine ⟨19071668345096407143187381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25428891126795209524249841 19071668345096407143187381)
                    ·
                      refine ⟨1787968907352788169673817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19071668345096407143187381 1787968907352788169673817)
                      ·
                        rfl

theorem cell23_3482057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 2, 5].length) (baseStart_3482057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482057 prefixEnd_3482057 := by exact prefixLift 3482057
  have htrace : WordTrace (prefixWord ++ tailWord_3482057) baseStart_3482057 baseEnd_3482057 := by
    simpa [prefixWord, tailWord_3482057, baseEnd_3482057] using wordTrace_append hprefix tailTrace_3482057
  have hstable : (prefixWord ++ tailWord_3482057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482057).length < 2 ^ (prefixWord ++ tailWord_3482057).sum := by decide
  have hdescent : baseEnd_3482057 < baseStart_3482057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482104 : List Nat := [2, 1, 2, 1, 1, 4, 1, 3, 1, 4, 3]
def baseStart_3482104 : Nat := 118140960795 + 3482104 * 2 ^ 59
def prefixEnd_3482104 : Nat := 4983230072969 + 3 ^ 40 * 3482104 * 2
def baseEnd_3482104 : Nat := 1787993040943549485786101

theorem tailTrace_3482104 : CollatzResearch.WordTrace tailWord_3482104 prefixEnd_3482104 1787993040943549485786101 := by
  unfold tailWord_3482104
  simp only [CollatzResearch.WordTrace]
  refine ⟨63501383288469689431070683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84668511051292919241427577 63501383288469689431070683)
  ·
    refine ⟨95252074932704534146606025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63501383288469689431070683 95252074932704534146606025)
    ·
      refine ⟨71439056199528400609954519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95252074932704534146606025 71439056199528400609954519)
      ·
        refine ⟨107158584299292600914931779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71439056199528400609954519 107158584299292600914931779)
        ·
          refine ⟨160737876448938901372397669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107158584299292600914931779 160737876448938901372397669)
          ·
            refine ⟨30138351834176044007324563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160737876448938901372397669 30138351834176044007324563)
            ·
              refine ⟨45207527751264066010986845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30138351834176044007324563 45207527751264066010986845)
              ·
                refine ⟨16952822906724024754120067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45207527751264066010986845 16952822906724024754120067)
                ·
                  refine ⟨25429234360086037131180101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16952822906724024754120067 25429234360086037131180101)
                  ·
                    refine ⟨4767981442516131962096269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25429234360086037131180101 4767981442516131962096269)
                    ·
                      refine ⟨1787993040943549485786101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4767981442516131962096269 1787993040943549485786101)
                      ·
                        rfl

theorem cell23_3482104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 1, 4, 3].length) (baseStart_3482104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482104 prefixEnd_3482104 := by exact prefixLift 3482104
  have htrace : WordTrace (prefixWord ++ tailWord_3482104) baseStart_3482104 baseEnd_3482104 := by
    simpa [prefixWord, tailWord_3482104, baseEnd_3482104] using wordTrace_append hprefix tailTrace_3482104
  have hstable : (prefixWord ++ tailWord_3482104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482104).length < 2 ^ (prefixWord ++ tailWord_3482104).sum := by decide
  have hdescent : baseEnd_3482104 < baseStart_3482104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482124 : List Nat := [2, 2, 1, 2, 4, 1, 2, 1, 8]
def baseStart_3482124 : Nat := 118140960795 + 3482124 * 2 ^ 59
def prefixEnd_3482124 : Nat := 4983230072969 + 3 ^ 40 * 3482124 * 2
def baseEnd_3482124 : Nat := 198667034506293267504001

theorem tailTrace_3482124 : CollatzResearch.WordTrace tailWord_3482124 prefixEnd_3482124 198667034506293267504001 := by
  unfold tailWord_3482124
  simp only [CollatzResearch.WordTrace]
  refine ⟨63501748018433461138934713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84668997357911281518579617 63501748018433461138934713)
  ·
    refine ⟨47626311013825095854201035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63501748018433461138934713 47626311013825095854201035)
    ·
      refine ⟨71439466520737643781301553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47626311013825095854201035 71439466520737643781301553)
      ·
        refine ⟨53579599890553232835976165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71439466520737643781301553 53579599890553232835976165)
        ·
          refine ⟨10046174979478731156745531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53579599890553232835976165 10046174979478731156745531)
          ·
            refine ⟨15069262469218096735118297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10046174979478731156745531 15069262469218096735118297)
            ·
              refine ⟨11301946851913572551338723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15069262469218096735118297 11301946851913572551338723)
              ·
                refine ⟨16952920277870358827008085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11301946851913572551338723 16952920277870358827008085)
                ·
                  refine ⟨198667034506293267504001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16952920277870358827008085 198667034506293267504001)
                  ·
                    rfl

theorem cell23_3482124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 8].length) (baseStart_3482124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482124 prefixEnd_3482124 := by exact prefixLift 3482124
  have htrace : WordTrace (prefixWord ++ tailWord_3482124) baseStart_3482124 baseEnd_3482124 := by
    simpa [prefixWord, tailWord_3482124, baseEnd_3482124] using wordTrace_append hprefix tailTrace_3482124
  have hstable : (prefixWord ++ tailWord_3482124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482124).length < 2 ^ (prefixWord ++ tailWord_3482124).sum := by decide
  have hdescent : baseEnd_3482124 < baseStart_3482124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482141 : List Nat := [1, 4, 2, 2, 1, 3, 1, 3, 6]
def baseStart_3482141 : Nat := 118140960795 + 3482141 * 2 ^ 59
def prefixEnd_3482141 : Nat := 4983230072969 + 3 ^ 40 * 3482141 * 2
def baseEnd_3482141 : Nat := 198668004414196204558159

theorem tailTrace_3482141 : CollatzResearch.WordTrace tailWord_3482141 prefixEnd_3482141 198668004414196204558159 := by
  unfold tailWord_3482141
  simp only [CollatzResearch.WordTrace]
  refine ⟨127004116077805334181238277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84669410718536889454158851 127004116077805334181238277)
  ·
    refine ⟨23813271764588500158982177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127004116077805334181238277 23813271764588500158982177)
    ·
      refine ⟨17859953823441375119236633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23813271764588500158982177 17859953823441375119236633)
      ·
        refine ⟨13394965367581031339427475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17859953823441375119236633 13394965367581031339427475)
        ·
          refine ⟨20092448051371547009141213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13394965367581031339427475 20092448051371547009141213)
          ·
            refine ⟨7534668019264330128427955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20092448051371547009141213 7534668019264330128427955)
            ·
              refine ⟨11302002028896495192641933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7534668019264330128427955 11302002028896495192641933)
              ·
                refine ⟨4238250760836185697240725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11302002028896495192641933 4238250760836185697240725)
                ·
                  refine ⟨198668004414196204558159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4238250760836185697240725 198668004414196204558159)
                  ·
                    rfl

theorem cell23_3482141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 6].length) (baseStart_3482141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482141 prefixEnd_3482141 := by exact prefixLift 3482141
  have htrace : WordTrace (prefixWord ++ tailWord_3482141) baseStart_3482141 baseEnd_3482141 := by
    simpa [prefixWord, tailWord_3482141, baseEnd_3482141] using wordTrace_append hprefix tailTrace_3482141
  have hstable : (prefixWord ++ tailWord_3482141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482141).length < 2 ^ (prefixWord ++ tailWord_3482141).sum := by decide
  have hdescent : baseEnd_3482141 < baseStart_3482141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482161 : List Nat := [1, 2, 2, 3, 1, 1, 2, 3, 1, 5, 2]
def baseStart_3482161 : Nat := 118140960795 + 3482161 * 2 ^ 59
def prefixEnd_3482161 : Nat := 4983230072969 + 3 ^ 40 * 3482161 * 2
def baseEnd_3482161 : Nat := 1788022309340855762773339

theorem tailTrace_3482161 : CollatzResearch.WordTrace tailWord_3482161 prefixEnd_3482161 1788022309340855762773339 := by
  unfold tailWord_3482161
  simp only [CollatzResearch.WordTrace]
  refine ⟨127004845537732877596966337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84669897025155251731310891 127004845537732877596966337)
  ·
    refine ⟨95253634153299658197724753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127004845537732877596966337 95253634153299658197724753)
    ·
      refine ⟨71440225614974743648293565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95253634153299658197724753 71440225614974743648293565)
      ·
        refine ⟨26790084605615528868110087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71440225614974743648293565 26790084605615528868110087)
        ·
          refine ⟨40185126908423293302165131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26790084605615528868110087 40185126908423293302165131)
          ·
            refine ⟨60277690362634939953247697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40185126908423293302165131 60277690362634939953247697)
            ·
              refine ⟨45208267771976204964935773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60277690362634939953247697 45208267771976204964935773)
              ·
                refine ⟨16953100414491076861850915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45208267771976204964935773 16953100414491076861850915)
                ·
                  refine ⟨25429650621736615292776373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16953100414491076861850915 25429650621736615292776373)
                  ·
                    refine ⟨2384029745787807683697785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25429650621736615292776373 2384029745787807683697785)
                    ·
                      refine ⟨1788022309340855762773339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2384029745787807683697785 1788022309340855762773339)
                      ·
                        rfl

theorem cell23_3482161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_3482161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482161 prefixEnd_3482161 := by exact prefixLift 3482161
  have htrace : WordTrace (prefixWord ++ tailWord_3482161) baseStart_3482161 baseEnd_3482161 := by
    simpa [prefixWord, tailWord_3482161, baseEnd_3482161] using wordTrace_append hprefix tailTrace_3482161
  have hstable : (prefixWord ++ tailWord_3482161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482161).length < 2 ^ (prefixWord ++ tailWord_3482161).sum := by decide
  have hdescent : baseEnd_3482161 < baseStart_3482161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482206 : List Nat := [4, 4, 1, 2, 2, 1, 1, 1, 2, 2, 3]
def baseStart_3482206 : Nat := 118140960795 + 3482206 * 2 ^ 59
def prefixEnd_3482206 : Nat := 4983230072969 + 3 ^ 40 * 3482206 * 2
def baseEnd_3482206 : Nat := 1788045415970308086710633

theorem tailTrace_3482206 : CollatzResearch.WordTrace tailWord_3482206 prefixEnd_3482206 1788045415970308086710633 := by
  unfold tailWord_3482206
  simp only [CollatzResearch.WordTrace]
  refine ⟨15875810852821231285294309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84670991215046566854902981 15875810852821231285294309)
  ·
    refine ⟨2976714534903980865992683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15875810852821231285294309 2976714534903980865992683)
    ·
      refine ⟨4465071802355971298989025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2976714534903980865992683 4465071802355971298989025)
      ·
        refine ⟨3348803851766978474241769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4465071802355971298989025 3348803851766978474241769)
        ·
          refine ⟨2511602888825233855681327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3348803851766978474241769 2511602888825233855681327)
          ·
            refine ⟨3767404333237850783521991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2511602888825233855681327 3767404333237850783521991)
            ·
              refine ⟨5651106499856776175282987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3767404333237850783521991 5651106499856776175282987)
              ·
                refine ⟨8476659749785164262924481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5651106499856776175282987 8476659749785164262924481)
                ·
                  refine ⟨6357494812338873197193361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8476659749785164262924481 6357494812338873197193361)
                  ·
                    refine ⟨4768121109254154897895021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6357494812338873197193361 4768121109254154897895021)
                    ·
                      refine ⟨1788045415970308086710633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4768121109254154897895021 1788045415970308086710633)
                      ·
                        rfl

theorem cell23_3482206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_3482206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482206 prefixEnd_3482206 := by exact prefixLift 3482206
  have htrace : WordTrace (prefixWord ++ tailWord_3482206) baseStart_3482206 baseEnd_3482206 := by
    simpa [prefixWord, tailWord_3482206, baseEnd_3482206] using wordTrace_append hprefix tailTrace_3482206
  have hstable : (prefixWord ++ tailWord_3482206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482206).length < 2 ^ (prefixWord ++ tailWord_3482206).sum := by decide
  have hdescent : baseEnd_3482206 < baseStart_3482206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482208 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 5, 2, 2]
def baseStart_3482208 : Nat := 118140960795 + 3482208 * 2 ^ 59
def prefixEnd_3482208 : Nat := 4983230072969 + 3 ^ 40 * 3482208 * 2
def baseEnd_3482208 : Nat := 1788046442931617078885623

theorem tailTrace_3482208 : CollatzResearch.WordTrace tailWord_3482208 prefixEnd_3482208 1788046442931617078885623 := by
  unfold tailWord_3482208
  simp only [CollatzResearch.WordTrace]
  refine ⟨63503279884281302311963639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84671039845708403082618185 63503279884281302311963639)
  ·
    refine ⟨95254919826421953467945459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63503279884281302311963639 95254919826421953467945459)
    ·
      refine ⟨142882379739632930201918189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95254919826421953467945459 142882379739632930201918189)
      ·
        refine ⟨53580892402362348825719321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142882379739632930201918189 53580892402362348825719321)
        ·
          refine ⟨40185669301771761619289491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53580892402362348825719321 40185669301771761619289491)
          ·
            refine ⟨60278503952657642428934237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40185669301771761619289491 60278503952657642428934237)
            ·
              refine ⟨22604438982246615910850339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60278503952657642428934237 22604438982246615910850339)
              ·
                refine ⟨33906658473369923866275509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22604438982246615910850339 33906658473369923866275509)
                ·
                  refine ⟨3178749231878430362463329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33906658473369923866275509 3178749231878430362463329)
                  ·
                    refine ⟨2384061923908822771847497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3178749231878430362463329 2384061923908822771847497)
                    ·
                      refine ⟨1788046442931617078885623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2384061923908822771847497 1788046442931617078885623)
                      ·
                        rfl

theorem cell23_3482208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 5, 2, 2].length) (baseStart_3482208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482208 prefixEnd_3482208 := by exact prefixLift 3482208
  have htrace : WordTrace (prefixWord ++ tailWord_3482208) baseStart_3482208 baseEnd_3482208 := by
    simpa [prefixWord, tailWord_3482208, baseEnd_3482208] using wordTrace_append hprefix tailTrace_3482208
  have hstable : (prefixWord ++ tailWord_3482208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482208).length < 2 ^ (prefixWord ++ tailWord_3482208).sum := by decide
  have hdescent : baseEnd_3482208 < baseStart_3482208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482211 : List Nat := [1, 1, 1, 5, 1, 2, 1, 3, 3, 2, 3]
def baseStart_3482211 : Nat := 118140960795 + 3482211 * 2 ^ 59
def prefixEnd_3482211 : Nat := 4983230072969 + 3 ^ 40 * 3482211 * 2
def baseEnd_3482211 : Nat := 1788047983373580567148109

theorem tailTrace_3482211 : CollatzResearch.WordTrace tailWord_3482211 prefixEnd_3482211 1788047983373580567148109 := by
  unfold tailWord_3482211
  simp only [CollatzResearch.WordTrace]
  refine ⟨127006669187551736136286487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84671112791701157424190991 127006669187551736136286487)
  ·
    refine ⟨190510003781327604204429731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127006669187551736136286487 190510003781327604204429731)
    ·
      refine ⟨285765005671991406306644597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190510003781327604204429731 285765005671991406306644597)
      ·
        refine ⟨26790469281749194341247931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 285765005671991406306644597 26790469281749194341247931)
        ·
          refine ⟨40185703922623791511871897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26790469281749194341247931 40185703922623791511871897)
          ·
            refine ⟨30139277941967843633903923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40185703922623791511871897 30139277941967843633903923)
            ·
              refine ⟨45208916912951765450855885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30139277941967843633903923 45208916912951765450855885)
              ·
                refine ⟨16953343842356912044070957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45208916912951765450855885 16953343842356912044070957)
                ·
                  refine ⟨6357503940883842016526609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16953343842356912044070957 6357503940883842016526609)
                  ·
                    refine ⟨4768127955662881512394957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6357503940883842016526609 4768127955662881512394957)
                    ·
                      refine ⟨1788047983373580567148109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4768127955662881512394957 1788047983373580567148109)
                      ·
                        rfl

theorem cell23_3482211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_3482211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482211 prefixEnd_3482211 := by exact prefixLift 3482211
  have htrace : WordTrace (prefixWord ++ tailWord_3482211) baseStart_3482211 baseEnd_3482211 := by
    simpa [prefixWord, tailWord_3482211, baseEnd_3482211] using wordTrace_append hprefix tailTrace_3482211
  have hstable : (prefixWord ++ tailWord_3482211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482211).length < 2 ^ (prefixWord ++ tailWord_3482211).sum := by decide
  have hdescent : baseEnd_3482211 < baseStart_3482211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482251 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 2, 7, 2]
def baseStart_3482251 : Nat := 118140960795 + 3482251 * 2 ^ 59
def prefixEnd_3482251 : Nat := 4983230072969 + 3 ^ 40 * 3482251 * 2
def baseEnd_3482251 : Nat := 1788068522599760410647925

theorem tailTrace_3482251 : CollatzResearch.WordTrace tailWord_3482251 prefixEnd_3482251 1788068522599760410647925 := by
  unfold tailWord_3482251
  simp only [CollatzResearch.WordTrace]
  refine ⟨127008128107406822967742607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84672085404937881978495071 127008128107406822967742607)
  ·
    refine ⟨190512192161110234451613911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127008128107406822967742607 190512192161110234451613911)
    ·
      refine ⟨285768288241665351677420867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190512192161110234451613911 285768288241665351677420867)
      ·
        refine ⟨428652432362498027516131301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285768288241665351677420867 428652432362498027516131301)
        ·
          refine ⟨80372331067968380159274619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 428652432362498027516131301 80372331067968380159274619)
          ·
            refine ⟨120558496601952570238911929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80372331067968380159274619 120558496601952570238911929)
            ·
              refine ⟨90418872451464427679183947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120558496601952570238911929 90418872451464427679183947)
              ·
                refine ⟨135628308677196641518775921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90418872451464427679183947 135628308677196641518775921)
                ·
                  refine ⟨101721231507897481139081941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135628308677196641518775921 101721231507897481139081941)
                  ·
                    refine ⟨2384091363466347214197233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 101721231507897481139081941 2384091363466347214197233)
                    ·
                      refine ⟨1788068522599760410647925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2384091363466347214197233 1788068522599760410647925)
                      ·
                        rfl

theorem cell23_3482251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 7, 2].length) (baseStart_3482251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482251 prefixEnd_3482251 := by exact prefixLift 3482251
  have htrace : WordTrace (prefixWord ++ tailWord_3482251) baseStart_3482251 baseEnd_3482251 := by
    simpa [prefixWord, tailWord_3482251, baseEnd_3482251] using wordTrace_append hprefix tailTrace_3482251
  have hstable : (prefixWord ++ tailWord_3482251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482251).length < 2 ^ (prefixWord ++ tailWord_3482251).sum := by decide
  have hdescent : baseEnd_3482251 < baseStart_3482251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482332 : List Nat := [2, 2, 5, 1, 1, 2, 1, 2, 1, 4, 2]
def baseStart_3482332 : Nat := 118140960795 + 3482332 * 2 ^ 59
def prefixEnd_3482332 : Nat := 4983230072969 + 3 ^ 40 * 3482332 * 2
def baseEnd_3482332 : Nat := 1788110114532774593735053

theorem tailTrace_3482332 : CollatzResearch.WordTrace tailWord_3482332 prefixEnd_3482332 1788110114532774593735053 := by
  unfold tailWord_3482332
  simp only [CollatzResearch.WordTrace]
  refine ⟨63505541210056686900720625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84674054946742249200960833 63505541210056686900720625)
  ·
    refine ⟨47629155907542515175540469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63505541210056686900720625 47629155907542515175540469)
    ·
      refine ⟨4465233366332110797706919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47629155907542515175540469 4465233366332110797706919)
      ·
        refine ⟨6697850049498166196560379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4465233366332110797706919 6697850049498166196560379)
        ·
          refine ⟨10046775074247249294840569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6697850049498166196560379 10046775074247249294840569)
          ·
            refine ⟨7535081305685436971130427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10046775074247249294840569 7535081305685436971130427)
            ·
              refine ⟨11302621958528155456695641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7535081305685436971130427 11302621958528155456695641)
              ·
                refine ⟨8476966468896116592521731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11302621958528155456695641 8476966468896116592521731)
                ·
                  refine ⟨12715449703344174888782597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8476966468896116592521731 12715449703344174888782597)
                  ·
                    refine ⟨2384146819377032791646737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12715449703344174888782597 2384146819377032791646737)
                    ·
                      refine ⟨1788110114532774593735053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2384146819377032791646737 1788110114532774593735053)
                      ·
                        rfl

theorem cell23_3482332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_3482332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482332 prefixEnd_3482332 := by exact prefixLift 3482332
  have htrace : WordTrace (prefixWord ++ tailWord_3482332) baseStart_3482332 baseEnd_3482332 := by
    simpa [prefixWord, tailWord_3482332, baseEnd_3482332] using wordTrace_append hprefix tailTrace_3482332
  have hstable : (prefixWord ++ tailWord_3482332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482332).length < 2 ^ (prefixWord ++ tailWord_3482332).sum := by decide
  have hdescent : baseEnd_3482332 < baseStart_3482332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482371 : List Nat := [1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 4]
def baseStart_3482371 : Nat := 118140960795 + 3482371 * 2 ^ 59
def prefixEnd_3482371 : Nat := 4983230072969 + 3 ^ 40 * 3482371 * 2
def baseEnd_3482371 : Nat := 1788130140278299941147373

theorem tailTrace_3482371 : CollatzResearch.WordTrace tailWord_3482371 prefixEnd_3482371 1788130140278299941147373 := by
  unfold tailWord_3482371
  simp only [CollatzResearch.WordTrace]
  refine ⟨127012504866972083462110967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84675003244648055641407311 127012504866972083462110967)
  ·
    refine ⟨190518757300458125193166451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127012504866972083462110967 190518757300458125193166451)
    ·
      refine ⟨285778135950687187789749677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190518757300458125193166451 285778135950687187789749677)
      ·
        refine ⟨107166800981507695421156129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285778135950687187789749677 107166800981507695421156129)
        ·
          refine ⟨80375100736130771565867097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107166800981507695421156129 80375100736130771565867097)
          ·
            refine ⟨60281325552098078674400323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80375100736130771565867097 60281325552098078674400323)
            ·
              refine ⟨90421988328147118011600485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60281325552098078674400323 90421988328147118011600485)
              ·
                refine ⟨16954122811527584627175091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90421988328147118011600485 16954122811527584627175091)
                ·
                  refine ⟨25431184217291376940762637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16954122811527584627175091 25431184217291376940762637)
                  ·
                    refine ⟨9536694081484266352785989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25431184217291376940762637 9536694081484266352785989)
                    ·
                      refine ⟨1788130140278299941147373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9536694081484266352785989 1788130140278299941147373)
                      ·
                        rfl

theorem cell23_3482371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_3482371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482371 prefixEnd_3482371 := by exact prefixLift 3482371
  have htrace : WordTrace (prefixWord ++ tailWord_3482371) baseStart_3482371 baseEnd_3482371 := by
    simpa [prefixWord, tailWord_3482371, baseEnd_3482371] using wordTrace_append hprefix tailTrace_3482371
  have hstable : (prefixWord ++ tailWord_3482371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482371).length < 2 ^ (prefixWord ++ tailWord_3482371).sum := by decide
  have hdescent : baseEnd_3482371 < baseStart_3482371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482401 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 1, 3, 6]
def baseStart_3482401 : Nat := 118140960795 + 3482401 * 2 ^ 59
def prefixEnd_3482401 : Nat := 4983230072969 + 3 ^ 40 * 3482401 * 2
def baseEnd_3482401 : Nat := 1788145544697934823772235

theorem tailTrace_3482401 : CollatzResearch.WordTrace tailWord_3482401 prefixEnd_3482401 1788145544697934823772235 := by
  unfold tailWord_3482401
  simp only [CollatzResearch.WordTrace]
  refine ⟨127013599056863398585703057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84675732704575599057135371 127013599056863398585703057)
  ·
    refine ⟨95260199292647548939277293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127013599056863398585703057 95260199292647548939277293)
    ·
      refine ⟨35722574734742830852228985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95260199292647548939277293 35722574734742830852228985)
      ·
        refine ⟨26791931051057123139171739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35722574734742830852228985 26791931051057123139171739)
        ·
          refine ⟨40187896576585684708757609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26791931051057123139171739 40187896576585684708757609)
          ·
            refine ⟨30140922432439263531568207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40187896576585684708757609 30140922432439263531568207)
            ·
              refine ⟨45211383648658895297352311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30140922432439263531568207 45211383648658895297352311)
              ·
                refine ⟨67817075472988342946028467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45211383648658895297352311 67817075472988342946028467)
                ·
                  refine ⟨101725613209482514419042701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67817075472988342946028467 101725613209482514419042701)
                  ·
                    refine ⟨38147104953555942907141013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101725613209482514419042701 38147104953555942907141013)
                    ·
                      refine ⟨1788145544697934823772235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38147104953555942907141013 1788145544697934823772235)
                      ·
                        rfl

theorem cell23_3482401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_3482401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482401 prefixEnd_3482401 := by exact prefixLift 3482401
  have htrace : WordTrace (prefixWord ++ tailWord_3482401) baseStart_3482401 baseEnd_3482401 := by
    simpa [prefixWord, tailWord_3482401, baseEnd_3482401] using wordTrace_append hprefix tailTrace_3482401
  have hstable : (prefixWord ++ tailWord_3482401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482401).length < 2 ^ (prefixWord ++ tailWord_3482401).sum := by decide
  have hdescent : baseEnd_3482401 < baseStart_3482401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482449 : List Nat := [1, 2, 2, 1, 6, 2, 1, 3, 1, 4]
def baseStart_3482449 : Nat := 118140960795 + 3482449 * 2 ^ 59
def prefixEnd_3482449 : Nat := 4983230072969 + 3 ^ 40 * 3482449 * 2
def baseEnd_3482449 : Nat := 596056730589783545324005

theorem tailTrace_3482449 : CollatzResearch.WordTrace tailWord_3482449 prefixEnd_3482449 596056730589783545324005 := by
  unfold tailWord_3482449
  simp only [CollatzResearch.WordTrace]
  refine ⟨127015349760689502783450401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84676899840459668522300267 127015349760689502783450401)
  ·
    refine ⟨95261512320517127087587801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127015349760689502783450401 95261512320517127087587801)
    ·
      refine ⟨71446134240387845315690851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95261512320517127087587801 71446134240387845315690851)
      ·
        refine ⟨107169201360581767973536277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71446134240387845315690851 107169201360581767973536277)
        ·
          refine ⟨5023556313777270373759513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 107169201360581767973536277 5023556313777270373759513)
          ·
            refine ⟨3767667235332952780319635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5023556313777270373759513 3767667235332952780319635)
            ·
              refine ⟨5651500852999429170479453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3767667235332952780319635 5651500852999429170479453)
              ·
                refine ⟨2119312819874785938929795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5651500852999429170479453 2119312819874785938929795)
                ·
                  refine ⟨3178969229812178908394693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2119312819874785938929795 3178969229812178908394693)
                  ·
                    refine ⟨596056730589783545324005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3178969229812178908394693 596056730589783545324005)
                    ·
                      rfl

theorem cell23_3482449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 3, 1, 4].length) (baseStart_3482449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482449 prefixEnd_3482449 := by exact prefixLift 3482449
  have htrace : WordTrace (prefixWord ++ tailWord_3482449) baseStart_3482449 baseEnd_3482449 := by
    simpa [prefixWord, tailWord_3482449, baseEnd_3482449] using wordTrace_append hprefix tailTrace_3482449
  have hstable : (prefixWord ++ tailWord_3482449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482449).length < 2 ^ (prefixWord ++ tailWord_3482449).sum := by decide
  have hdescent : baseEnd_3482449 < baseStart_3482449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482466 : List Nat := [3, 3, 2, 1, 3, 1, 3, 2, 1, 4]
def baseStart_3482466 : Nat := 118140960795 + 3482466 * 2 ^ 59
def prefixEnd_3482466 : Nat := 4983230072969 + 3 ^ 40 * 3482466 * 2
def baseEnd_3482466 : Nat := 596059640313492356486479

theorem tailTrace_3482466 : CollatzResearch.WordTrace tailWord_3482466 prefixEnd_3482466 596059640313492356486479 := by
  unfold tailWord_3482466
  simp only [CollatzResearch.WordTrace]
  refine ⟨31753992450406978671704813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84677313201085276457879501 31753992450406978671704813)
  ·
    refine ⟨11907747168902617001889305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31753992450406978671704813 11907747168902617001889305)
    ·
      refine ⟨8930810376676962751416979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11907747168902617001889305 8930810376676962751416979)
      ·
        refine ⟨13396215565015444127125469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8930810376676962751416979 13396215565015444127125469)
        ·
          refine ⟨5023580836880791547672051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13396215565015444127125469 5023580836880791547672051)
          ·
            refine ⟨7535371255321187321508077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5023580836880791547672051 7535371255321187321508077)
            ·
              refine ⟨2825764220745445245565529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7535371255321187321508077 2825764220745445245565529)
              ·
                refine ⟨2119323165559083934174147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2825764220745445245565529 2119323165559083934174147)
                ·
                  refine ⟨3178984748338625901261221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2119323165559083934174147 3178984748338625901261221)
                  ·
                    refine ⟨596059640313492356486479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3178984748338625901261221 596059640313492356486479)
                    ·
                      rfl

theorem cell23_3482466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_3482466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482466 prefixEnd_3482466 := by exact prefixLift 3482466
  have htrace : WordTrace (prefixWord ++ tailWord_3482466) baseStart_3482466 baseEnd_3482466 := by
    simpa [prefixWord, tailWord_3482466, baseEnd_3482466] using wordTrace_append hprefix tailTrace_3482466
  have hstable : (prefixWord ++ tailWord_3482466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482466).length < 2 ^ (prefixWord ++ tailWord_3482466).sum := by decide
  have hdescent : baseEnd_3482466 < baseStart_3482466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482472 : List Nat := [2, 1, 4, 2, 1, 2, 3, 1, 3, 1, 3]
def baseStart_3482472 : Nat := 118140960795 + 3482472 * 2 ^ 59
def prefixEnd_3482472 : Nat := 4983230072969 + 3 ^ 40 * 3482472 * 2
def baseEnd_3482472 : Nat := 1788182001824404045984409

theorem tailTrace_3482472 : CollatzResearch.WordTrace tailWord_3482472 prefixEnd_3482472 1788182001824404045984409 := by
  unfold tailWord_3482472
  simp only [CollatzResearch.WordTrace]
  refine ⟨63508094319803088855768835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84677459093070785141025113 63508094319803088855768835)
  ·
    refine ⟨95262141479704633283653253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63508094319803088855768835 95262141479704633283653253)
    ·
      refine ⟨17861651527444618740684985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95262141479704633283653253 17861651527444618740684985)
      ·
        refine ⟨13396238645583464055513739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17861651527444618740684985 13396238645583464055513739)
        ·
          refine ⟨20094357968375196083270609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13396238645583464055513739 20094357968375196083270609)
          ·
            refine ⟨15070768476281397062452957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20094357968375196083270609 15070768476281397062452957)
            ·
              refine ⟨5651538178605523898419859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15070768476281397062452957 5651538178605523898419859)
              ·
                refine ⟨8477307267908285847629789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5651538178605523898419859 8477307267908285847629789)
                ·
                  refine ⟨3178990225465607192861171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8477307267908285847629789 3178990225465607192861171)
                  ·
                    refine ⟨4768485338198410789291757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3178990225465607192861171 4768485338198410789291757)
                    ·
                      refine ⟨1788182001824404045984409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4768485338198410789291757 1788182001824404045984409)
                      ·
                        rfl

theorem cell23_3482472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_3482472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482472 prefixEnd_3482472 := by exact prefixLift 3482472
  have htrace : WordTrace (prefixWord ++ tailWord_3482472) baseStart_3482472 baseEnd_3482472 := by
    simpa [prefixWord, tailWord_3482472, baseEnd_3482472] using wordTrace_append hprefix tailTrace_3482472
  have hstable : (prefixWord ++ tailWord_3482472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482472).length < 2 ^ (prefixWord ++ tailWord_3482472).sum := by decide
  have hdescent : baseEnd_3482472 < baseStart_3482472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482488 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 6, 4]
def baseStart_3482488 : Nat := 118140960795 + 3482488 * 2 ^ 59
def prefixEnd_3482488 : Nat := 4983230072969 + 3 ^ 40 * 3482488 * 2
def baseEnd_3482488 : Nat := 596063405838291994461445

theorem tailTrace_3482488 : CollatzResearch.WordTrace tailWord_3482488 prefixEnd_3482488 596063405838291994461445 := by
  unfold tailWord_3482488
  simp only [CollatzResearch.WordTrace]
  refine ⟨63508386103774106222060059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84677848138365474962746745 63508386103774106222060059)
  ·
    refine ⟨95262579155661159333090089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63508386103774106222060059 95262579155661159333090089)
    ·
      refine ⟨71446934366745869499817567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95262579155661159333090089 71446934366745869499817567)
      ·
        refine ⟨107170401550118804249726351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71446934366745869499817567 107170401550118804249726351)
        ·
          refine ⟨160755602325178206374589527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107170401550118804249726351 160755602325178206374589527)
          ·
            refine ⟨241133403487767309561884291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160755602325178206374589527 241133403487767309561884291)
            ·
              refine ⟨361700105231650964342826437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241133403487767309561884291 361700105231650964342826437)
              ·
                refine ⟨67818769730934555814279957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 361700105231650964342826437 67818769730934555814279957)
                ·
                  refine ⟨3179004831137557303794373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67818769730934555814279957 3179004831137557303794373)
                  ·
                    refine ⟨596063405838291994461445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3179004831137557303794373 596063405838291994461445)
                    ·
                      rfl

theorem cell23_3482488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 6, 4].length) (baseStart_3482488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482488 prefixEnd_3482488 := by exact prefixLift 3482488
  have htrace : WordTrace (prefixWord ++ tailWord_3482488) baseStart_3482488 baseEnd_3482488 := by
    simpa [prefixWord, tailWord_3482488, baseEnd_3482488] using wordTrace_append hprefix tailTrace_3482488
  have hstable : (prefixWord ++ tailWord_3482488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482488).length < 2 ^ (prefixWord ++ tailWord_3482488).sum := by decide
  have hdescent : baseEnd_3482488 < baseStart_3482488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482495 : List Nat := [1, 1, 2, 2, 1, 1, 7, 2, 1, 1, 4]
def baseStart_3482495 : Nat := 118140960795 + 3482495 * 2 ^ 59
def prefixEnd_3482495 : Nat := 4983230072969 + 3 ^ 40 * 3482495 * 2
def baseEnd_3482495 : Nat := 1788193811879457455996803

theorem tailTrace_3482495 : CollatzResearch.WordTrace tailWord_3482495 prefixEnd_3482495 1788193811879457455996803 := by
  unfold tailWord_3482495
  simp only [CollatzResearch.WordTrace]
  refine ⟨127017027518522852639624939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84678018345681901759749959 127017027518522852639624939)
  ·
    refine ⟨190525541277784278959437409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127017027518522852639624939 190525541277784278959437409)
    ·
      refine ⟨142894155958338209219578057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190525541277784278959437409 142894155958338209219578057)
      ·
        refine ⟨107170616968753656914683543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142894155958338209219578057 107170616968753656914683543)
        ·
          refine ⟨160755925453130485372025315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107170616968753656914683543 160755925453130485372025315)
          ·
            refine ⟨241133888179695728058037973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160755925453130485372025315 241133888179695728058037973)
            ·
              refine ⟨5651575504211618626360265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 241133888179695728058037973 5651575504211618626360265)
              ·
                refine ⟨4238681628158713969770199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5651575504211618626360265 4238681628158713969770199)
                ·
                  refine ⟨6358022442238070954655299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4238681628158713969770199 6358022442238070954655299)
                  ·
                    refine ⟨9537033663357106431982949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6358022442238070954655299 9537033663357106431982949)
                    ·
                      refine ⟨1788193811879457455996803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9537033663357106431982949 1788193811879457455996803)
                      ·
                        rfl

theorem cell23_3482495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 1, 4].length) (baseStart_3482495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482495 prefixEnd_3482495 := by exact prefixLift 3482495
  have htrace : WordTrace (prefixWord ++ tailWord_3482495) baseStart_3482495 baseEnd_3482495 := by
    simpa [prefixWord, tailWord_3482495, baseEnd_3482495] using wordTrace_append hprefix tailTrace_3482495
  have hstable : (prefixWord ++ tailWord_3482495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482495).length < 2 ^ (prefixWord ++ tailWord_3482495).sum := by decide
  have hdescent : baseEnd_3482495 < baseStart_3482495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482508 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 3, 2, 4]
def baseStart_3482508 : Nat := 118140960795 + 3482508 * 2 ^ 59
def prefixEnd_3482508 : Nat := 4983230072969 + 3 ^ 40 * 3482508 * 2
def baseEnd_3482508 : Nat := 1788200487127965905134243

theorem tailTrace_3482508 : CollatzResearch.WordTrace tailWord_3482508 prefixEnd_3482508 1788200487127965905134243 := by
  unfold tailWord_3482508
  simp only [CollatzResearch.WordTrace]
  refine ⟨63508750833737877929924089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84678334444983837239898785 63508750833737877929924089)
  ·
    refine ⟨47631563125303408447443067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63508750833737877929924089 47631563125303408447443067)
    ·
      refine ⟨71447344687955112671164601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47631563125303408447443067 71447344687955112671164601)
      ·
        refine ⟨53585508515966334503373451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71447344687955112671164601 53585508515966334503373451)
        ·
          refine ⟨80378262773949501755060177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53585508515966334503373451 80378262773949501755060177)
          ·
            refine ⟨60283697080462126316295133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80378262773949501755060177 60283697080462126316295133)
            ·
              refine ⟨22606386405173297368610675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60283697080462126316295133 22606386405173297368610675)
              ·
                refine ⟨33909579607759946052916013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22606386405173297368610675 33909579607759946052916013)
                ·
                  refine ⟨12716092352909979769843505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33909579607759946052916013 12716092352909979769843505)
                  ·
                    refine ⟨9537069264682484827382629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12716092352909979769843505 9537069264682484827382629)
                    ·
                      refine ⟨1788200487127965905134243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9537069264682484827382629 1788200487127965905134243)
                      ·
                        rfl

theorem cell23_3482508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_3482508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482508 prefixEnd_3482508 := by exact prefixLift 3482508
  have htrace : WordTrace (prefixWord ++ tailWord_3482508) baseStart_3482508 baseEnd_3482508 := by
    simpa [prefixWord, tailWord_3482508, baseEnd_3482508] using wordTrace_append hprefix tailTrace_3482508
  have hstable : (prefixWord ++ tailWord_3482508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482508).length < 2 ^ (prefixWord ++ tailWord_3482508).sum := by decide
  have hdescent : baseEnd_3482508 < baseStart_3482508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482550 : List Nat := [5, 1, 4, 1, 1, 2, 1, 1, 2, 3, 2]
def baseStart_3482550 : Nat := 118140960795 + 3482550 * 2 ^ 59
def prefixEnd_3482550 : Nat := 4983230072969 + 3 ^ 40 * 3482550 * 2
def baseEnd_3482550 : Nat := 1788222053315454740809051

theorem tailTrace_3482550 : CollatzResearch.WordTrace tailWord_3482550 prefixEnd_3482550 1788222053315454740809051 := by
  unfold tailWord_3482550
  simp only [CollatzResearch.WordTrace]
  refine ⟨7938689595832724814554819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84679355688882398021918069 7938689595832724814554819)
  ·
    refine ⟨11908034393749087221832229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7938689595832724814554819 11908034393749087221832229)
    ·
      refine ⟨2232756448827953854093543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11908034393749087221832229 2232756448827953854093543)
      ·
        refine ⟨3349134673241930781140315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2232756448827953854093543 3349134673241930781140315)
        ·
          refine ⟨5023702009862896171710473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3349134673241930781140315 5023702009862896171710473)
          ·
            refine ⟨3767776507397172128782855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5023702009862896171710473 3767776507397172128782855)
            ·
              refine ⟨5651664761095758193174283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3767776507397172128782855 5651664761095758193174283)
              ·
                refine ⟨8477497141643637289761425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5651664761095758193174283 8477497141643637289761425)
                ·
                  refine ⟨6358122856232727967321069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8477497141643637289761425 6358122856232727967321069)
                  ·
                    refine ⟨2384296071087272987745401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6358122856232727967321069 2384296071087272987745401)
                    ·
                      refine ⟨1788222053315454740809051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2384296071087272987745401 1788222053315454740809051)
                      ·
                        rfl

theorem cell23_3482550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_3482550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482550 prefixEnd_3482550 := by exact prefixLift 3482550
  have htrace : WordTrace (prefixWord ++ tailWord_3482550) baseStart_3482550 baseEnd_3482550 := by
    simpa [prefixWord, tailWord_3482550, baseEnd_3482550] using wordTrace_append hprefix tailTrace_3482550
  have hstable : (prefixWord ++ tailWord_3482550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482550).length < 2 ^ (prefixWord ++ tailWord_3482550).sum := by decide
  have hdescent : baseEnd_3482550 < baseStart_3482550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482555 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 7, 3, 2]
def baseStart_3482555 : Nat := 118140960795 + 3482555 * 2 ^ 59
def prefixEnd_3482555 : Nat := 4983230072969 + 3 ^ 40 * 3482555 * 2
def baseEnd_3482555 : Nat := 1788224620718727221246527

theorem tailTrace_3482555 : CollatzResearch.WordTrace tailWord_3482555 prefixEnd_3482555 1788224620718727221246527 := by
  unfold tailWord_3482555
  simp only [CollatzResearch.WordTrace]
  refine ⟨127019215898305482886809119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84679477265536988591206079 127019215898305482886809119)
  ·
    refine ⟨190528823847458224330213679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127019215898305482886809119 190528823847458224330213679)
    ·
      refine ⟨285793235771187336495320519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190528823847458224330213679 285793235771187336495320519)
      ·
        refine ⟨428689853656781004742980779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285793235771187336495320519 428689853656781004742980779)
        ·
          refine ⟨643034780485171507114471169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428689853656781004742980779 643034780485171507114471169)
          ·
            refine ⟨482276085363878630335853377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 643034780485171507114471169 482276085363878630335853377)
            ·
              refine ⟨361707064022908972751890033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 482276085363878630335853377 361707064022908972751890033)
              ·
                refine ⟨271280298017181729563917525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361707064022908972751890033 271280298017181729563917525)
                ·
                  refine ⟨6358131984777696786654317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 271280298017181729563917525 6358131984777696786654317)
                  ·
                    refine ⟨2384299494291636294995369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6358131984777696786654317 2384299494291636294995369)
                    ·
                      refine ⟨1788224620718727221246527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2384299494291636294995369 1788224620718727221246527)
                      ·
                        rfl

theorem cell23_3482555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 3, 2].length) (baseStart_3482555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482555 prefixEnd_3482555 := by exact prefixLift 3482555
  have htrace : WordTrace (prefixWord ++ tailWord_3482555) baseStart_3482555 baseEnd_3482555 := by
    simpa [prefixWord, tailWord_3482555, baseEnd_3482555] using wordTrace_append hprefix tailTrace_3482555
  have hstable : (prefixWord ++ tailWord_3482555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482555).length < 2 ^ (prefixWord ++ tailWord_3482555).sum := by decide
  have hdescent : baseEnd_3482555 < baseStart_3482555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482606 : List Nat := [4, 1, 2, 1, 4, 1, 2, 2, 1, 3, 2]
def baseStart_3482606 : Nat := 118140960795 + 3482606 * 2 ^ 59
def prefixEnd_3482606 : Nat := 4983230072969 + 3 ^ 40 * 3482606 * 2
def baseEnd_3482606 : Nat := 1788250808232106521708793

theorem tailTrace_3482606 : CollatzResearch.WordTrace tailWord_3482606 prefixEnd_3482606 1788250808232106521708793 := by
  unfold tailWord_3482606
  simp only [CollatzResearch.WordTrace]
  refine ⟨15877634502640089824614459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84680717347413812397943781 15877634502640089824614459)
  ·
    refine ⟨23816451753960134736921689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15877634502640089824614459 23816451753960134736921689)
    ·
      refine ⟨17862338815470101052691267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23816451753960134736921689 17862338815470101052691267)
      ·
        refine ⟨26793508223205151579036901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17862338815470101052691267 26793508223205151579036901)
        ·
          refine ⟨5023782791850965921069419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26793508223205151579036901 5023782791850965921069419)
          ·
            refine ⟨7535674187776448881604129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5023782791850965921069419 7535674187776448881604129)
            ·
              refine ⟨5651755640832336661203097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7535674187776448881604129 5651755640832336661203097)
              ·
                refine ⟨4238816730624252495902323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5651755640832336661203097 4238816730624252495902323)
                ·
                  refine ⟨6358225095936378743853485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4238816730624252495902323 6358225095936378743853485)
                  ·
                    refine ⟨2384334410976142028945057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6358225095936378743853485 2384334410976142028945057)
                    ·
                      refine ⟨1788250808232106521708793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2384334410976142028945057 1788250808232106521708793)
                      ·
                        rfl

theorem cell23_3482606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_3482606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482606 prefixEnd_3482606 := by exact prefixLift 3482606
  have htrace : WordTrace (prefixWord ++ tailWord_3482606) baseStart_3482606 baseEnd_3482606 := by
    simpa [prefixWord, tailWord_3482606, baseEnd_3482606] using wordTrace_append hprefix tailTrace_3482606
  have hstable : (prefixWord ++ tailWord_3482606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482606).length < 2 ^ (prefixWord ++ tailWord_3482606).sum := by decide
  have hdescent : baseEnd_3482606 < baseStart_3482606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482702 : List Nat := [4, 1, 1, 1, 1, 3, 2, 3, 3, 4]
def baseStart_3482702 : Nat := 118140960795 + 3482702 * 2 ^ 59
def prefixEnd_3482702 : Nat := 4983230072969 + 3 ^ 40 * 3482702 * 2
def baseEnd_3482702 : Nat := 596100034124979382036117

theorem tailTrace_3482702 : CollatzResearch.WordTrace tailWord_3482702 prefixEnd_3482702 596100034124979382036117 := by
  unfold tailWord_3482702
  simp only [CollatzResearch.WordTrace]
  refine ⟨15878072178596615874051295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84683051619181951328273573 15878072178596615874051295)
  ·
    refine ⟨23817108267894923811076943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15878072178596615874051295 23817108267894923811076943)
    ·
      refine ⟨35725662401842385716615415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23817108267894923811076943 35725662401842385716615415)
      ·
        refine ⟨53588493602763578574923123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35725662401842385716615415 53588493602763578574923123)
        ·
          refine ⟨80382740404145367862384685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53588493602763578574923123 80382740404145367862384685)
          ·
            refine ⟨30143527651554512948394257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80382740404145367862384685 30143527651554512948394257)
            ·
              refine ⟨22607645738665884711295693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30143527651554512948394257 22607645738665884711295693)
              ·
                refine ⟨8477867151999706766735885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22607645738665884711295693 8477867151999706766735885)
                ·
                  refine ⟨3179200181999890037525957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8477867151999706766735885 3179200181999890037525957)
                  ·
                    refine ⟨596100034124979382036117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3179200181999890037525957 596100034124979382036117)
                    ·
                      rfl

theorem cell23_3482702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_3482702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482702 prefixEnd_3482702 := by exact prefixLift 3482702
  have htrace : WordTrace (prefixWord ++ tailWord_3482702) baseStart_3482702 baseEnd_3482702 := by
    simpa [prefixWord, tailWord_3482702, baseEnd_3482702] using wordTrace_append hprefix tailTrace_3482702
  have hstable : (prefixWord ++ tailWord_3482702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482702).length < 2 ^ (prefixWord ++ tailWord_3482702).sum := by decide
  have hdescent : baseEnd_3482702 < baseStart_3482702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482729 : List Nat := [1, 2, 1, 1, 1, 8, 1, 1, 2, 2, 3]
def baseStart_3482729 : Nat := 118140960795 + 3482729 * 2 ^ 59
def prefixEnd_3482729 : Nat := 4983230072969 + 3 ^ 40 * 3482729 * 2
def baseEnd_3482729 : Nat := 1788313966352609540470727

theorem tailTrace_3482729 : CollatzResearch.WordTrace tailWord_3482729 prefixEnd_3482729 1788313966352609540470727 := by
  unfold tailWord_3482729
  simp only [CollatzResearch.WordTrace]
  refine ⟨127025562199675110603643241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84683708133116740402428827 127025562199675110603643241)
  ·
    refine ⟨95269171649756332952732431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127025562199675110603643241 95269171649756332952732431)
    ·
      refine ⟨142903757474634499429098647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95269171649756332952732431 142903757474634499429098647)
      ·
        refine ⟨214355636211951749143647971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142903757474634499429098647 214355636211951749143647971)
        ·
          refine ⟨321533454317927623715471957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214355636211951749143647971 321533454317927623715471957)
          ·
            refine ⟨3767970167788214340415687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 321533454317927623715471957 3767970167788214340415687)
            ·
              refine ⟨5651955251682321510623531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3767970167788214340415687 5651955251682321510623531)
              ·
                refine ⟨8477932877523482265935297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5651955251682321510623531 8477932877523482265935297)
                ·
                  refine ⟨6358449658142611699451473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8477932877523482265935297 6358449658142611699451473)
                  ·
                    refine ⟨4768837243606958774588605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6358449658142611699451473 4768837243606958774588605)
                    ·
                      refine ⟨1788313966352609540470727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4768837243606958774588605 1788313966352609540470727)
                      ·
                        rfl

theorem cell23_3482729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 2, 3].length) (baseStart_3482729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482729 prefixEnd_3482729 := by exact prefixLift 3482729
  have htrace : WordTrace (prefixWord ++ tailWord_3482729) baseStart_3482729 baseEnd_3482729 := by
    simpa [prefixWord, tailWord_3482729, baseEnd_3482729] using wordTrace_append hprefix tailTrace_3482729
  have hstable : (prefixWord ++ tailWord_3482729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482729).length < 2 ^ (prefixWord ++ tailWord_3482729).sum := by decide
  have hdescent : baseEnd_3482729 < baseStart_3482729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482799 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 5, 2, 2]
def baseStart_3482799 : Nat := 118140960795 + 3482799 * 2 ^ 59
def prefixEnd_3482799 : Nat := 4983230072969 + 3 ^ 40 * 3482799 * 2
def baseEnd_3482799 : Nat := 1788349909998424266595405

theorem tailTrace_3482799 : CollatzResearch.WordTrace tailWord_3482799 prefixEnd_3482799 1788349909998424266595405 := by
  unfold tailWord_3482799
  simp only [CollatzResearch.WordTrace]
  refine ⟨127028115309421512558691451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84685410206281008372460967 127028115309421512558691451)
  ·
    refine ⟨190542172964132268838037177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127028115309421512558691451 190542172964132268838037177)
    ·
      refine ⟨142906629723099201628527883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190542172964132268838037177 142906629723099201628527883)
      ·
        refine ⟨214359944584648802442791825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142906629723099201628527883 214359944584648802442791825)
        ·
          refine ⟨160769958438486601832093869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214359944584648802442791825 160769958438486601832093869)
          ·
            refine ⟨60288734414432475687035201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160769958438486601832093869 60288734414432475687035201)
            ·
              refine ⟨45216550810824356765276401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60288734414432475687035201 45216550810824356765276401)
              ·
                refine ⟨33912413108118267573957301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45216550810824356765276401 33912413108118267573957301)
                ·
                  refine ⟨3179288728886087585058497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33912413108118267573957301 3179288728886087585058497)
                  ·
                    refine ⟨2384466546664565688793873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3179288728886087585058497 2384466546664565688793873)
                    ·
                      refine ⟨1788349909998424266595405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2384466546664565688793873 1788349909998424266595405)
                      ·
                        rfl

theorem cell23_3482799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 5, 2, 2].length) (baseStart_3482799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482799 prefixEnd_3482799 := by exact prefixLift 3482799
  have htrace : WordTrace (prefixWord ++ tailWord_3482799) baseStart_3482799 baseEnd_3482799 := by
    simpa [prefixWord, tailWord_3482799, baseEnd_3482799] using wordTrace_append hprefix tailTrace_3482799
  have hstable : (prefixWord ++ tailWord_3482799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482799).length < 2 ^ (prefixWord ++ tailWord_3482799).sum := by decide
  have hdescent : baseEnd_3482799 < baseStart_3482799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482802 : List Nat := [3, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5]
def baseStart_3482802 : Nat := 118140960795 + 3482802 * 2 ^ 59
def prefixEnd_3482802 : Nat := 4983230072969 + 3 ^ 40 * 3482802 * 2
def baseEnd_3482802 : Nat := 1788351450440387754857891

theorem tailTrace_3482802 : CollatzResearch.WordTrace tailWord_3482802 prefixEnd_3482802 1788351450440387754857891 := by
  unfold tailWord_3482802
  simp only [CollatzResearch.WordTrace]
  refine ⟨31757056182102661017762665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84685483152273762714033773 31757056182102661017762665)
  ·
    refine ⟨23817792136576995763321999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31757056182102661017762665 23817792136576995763321999)
    ·
      refine ⟨35726688204865493644982999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23817792136576995763321999 35726688204865493644982999)
      ·
        refine ⟨53590032307298240467474499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35726688204865493644982999 53590032307298240467474499)
        ·
          refine ⟨80385048460947360701211749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53590032307298240467474499 80385048460947360701211749)
          ·
            refine ⟨15072196586427630131477203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80385048460947360701211749 15072196586427630131477203)
            ·
              refine ⟨22608294879641445197215805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15072196586427630131477203 22608294879641445197215805)
              ·
                refine ⟨8478110579865541948955927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22608294879641445197215805 8478110579865541948955927)
                ·
                  refine ⟨12717165869798312923433891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8478110579865541948955927 12717165869798312923433891)
                  ·
                    refine ⟨19075748804697469385150837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12717165869798312923433891 19075748804697469385150837)
                    ·
                      refine ⟨1788351450440387754857891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19075748804697469385150837 1788351450440387754857891)
                      ·
                        rfl

theorem cell23_3482802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_3482802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482802 prefixEnd_3482802 := by exact prefixLift 3482802
  have htrace : WordTrace (prefixWord ++ tailWord_3482802) baseStart_3482802 baseEnd_3482802 := by
    simpa [prefixWord, tailWord_3482802, baseEnd_3482802] using wordTrace_append hprefix tailTrace_3482802
  have hstable : (prefixWord ++ tailWord_3482802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482802).length < 2 ^ (prefixWord ++ tailWord_3482802).sum := by decide
  have hdescent : baseEnd_3482802 < baseStart_3482802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482812 : List Nat := [2, 2, 2, 3, 2, 1, 1, 2, 1, 1, 6]
def baseStart_3482812 : Nat := 118140960795 + 3482812 * 2 ^ 59
def prefixEnd_3482812 : Nat := 4983230072969 + 3 ^ 40 * 3482812 * 2
def baseEnd_3482812 : Nat := 1788356585246932715732845

theorem tailTrace_3482812 : CollatzResearch.WordTrace tailWord_3482812 prefixEnd_3482812 1788356585246932715732845 := by
  unfold tailWord_3482812
  simp only [CollatzResearch.WordTrace]
  refine ⟨63514294729187207889457345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84685726305582943852609793 63514294729187207889457345)
  ·
    refine ⟨47635721046890405917093009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63514294729187207889457345 47635721046890405917093009)
    ·
      refine ⟨35726790785167804437819757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47635721046890405917093009 35726790785167804437819757)
      ·
        refine ⟨13397546544437926664182409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35726790785167804437819757 13397546544437926664182409)
        ·
          refine ⟨10048159908328444998136807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13397546544437926664182409 10048159908328444998136807)
          ·
            refine ⟨15072239862492667497205211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10048159908328444998136807 15072239862492667497205211)
            ·
              refine ⟨22608359793739001245807817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15072239862492667497205211 22608359793739001245807817)
              ·
                refine ⟨16956269845304250934355863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22608359793739001245807817 16956269845304250934355863)
                ·
                  refine ⟨25434404767956376401533795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16956269845304250934355863 25434404767956376401533795)
                  ·
                    refine ⟨38151607151934564602300693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25434404767956376401533795 38151607151934564602300693)
                    ·
                      refine ⟨1788356585246932715732845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38151607151934564602300693 1788356585246932715732845)
                      ·
                        rfl

theorem cell23_3482812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_3482812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482812 prefixEnd_3482812 := by exact prefixLift 3482812
  have htrace : WordTrace (prefixWord ++ tailWord_3482812) baseStart_3482812 baseEnd_3482812 := by
    simpa [prefixWord, tailWord_3482812, baseEnd_3482812] using wordTrace_append hprefix tailTrace_3482812
  have hstable : (prefixWord ++ tailWord_3482812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482812).length < 2 ^ (prefixWord ++ tailWord_3482812).sum := by decide
  have hdescent : baseEnd_3482812 < baseStart_3482812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482826 : List Nat := [3, 1, 2, 1, 3, 2, 4, 1, 2, 4]
def baseStart_3482826 : Nat := 118140960795 + 3482826 * 2 ^ 59
def prefixEnd_3482826 : Nat := 4983230072969 + 3 ^ 40 * 3482826 * 2
def baseEnd_3482826 : Nat := 596121257992031886985927

theorem tailTrace_3482826 : CollatzResearch.WordTrace tailWord_3482826 prefixEnd_3482826 596121257992031886985927 := by
  unfold tailWord_3482826
  simp only [CollatzResearch.WordTrace]
  refine ⟨31757275020080924042481083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84686066720215797446616221 31757275020080924042481083)
  ·
    refine ⟨47635912530121386063721625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31757275020080924042481083 47635912530121386063721625)
    ·
      refine ⟨35726934397591039547791219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47635912530121386063721625 35726934397591039547791219)
      ·
        refine ⟨53590401596386559321686829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35726934397591039547791219 53590401596386559321686829)
        ·
          refine ⟨20096400598644959745632561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53590401596386559321686829 20096400598644959745632561)
          ·
            refine ⟨15072300448983719809224421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20096400598644959745632561 15072300448983719809224421)
            ·
              refine ⟨2826056334184447464229579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15072300448983719809224421 2826056334184447464229579)
              ·
                refine ⟨4239084501276671196344369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2826056334184447464229579 4239084501276671196344369)
                ·
                  refine ⟨3179313375957503397258277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4239084501276671196344369 3179313375957503397258277)
                  ·
                    refine ⟨596121257992031886985927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3179313375957503397258277 596121257992031886985927)
                    ·
                      rfl

theorem cell23_3482826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_3482826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482826 prefixEnd_3482826 := by exact prefixLift 3482826
  have htrace : WordTrace (prefixWord ++ tailWord_3482826) baseStart_3482826 baseEnd_3482826 := by
    simpa [prefixWord, tailWord_3482826, baseEnd_3482826] using wordTrace_append hprefix tailTrace_3482826
  have hstable : (prefixWord ++ tailWord_3482826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482826).length < 2 ^ (prefixWord ++ tailWord_3482826).sum := by decide
  have hdescent : baseEnd_3482826 < baseStart_3482826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482835 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 2, 7]
def baseStart_3482835 : Nat := 118140960795 + 3482835 * 2 ^ 59
def prefixEnd_3482835 : Nat := 4983230072969 + 3 ^ 40 * 3482835 * 2
def baseEnd_3482835 : Nat := 596122798433995375248413

theorem tailTrace_3482835 : CollatzResearch.WordTrace tailWord_3482835 prefixEnd_3482835 596122798433995375248413 := by
  unfold tailWord_3482835
  simp only [CollatzResearch.WordTrace]
  refine ⟨127029428337291090707001959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84686285558194060471334639 127029428337291090707001959)
  ·
    refine ⟨190544142505936636060502939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127029428337291090707001959 190544142505936636060502939)
    ·
      refine ⟨285816213758904954090754409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190544142505936636060502939 285816213758904954090754409)
      ·
        refine ⟨214362160319178715568065807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285816213758904954090754409 214362160319178715568065807)
        ·
          refine ⟨321543240478768073352098711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214362160319178715568065807 321543240478768073352098711)
          ·
            refine ⟨482314860718152110028148067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321543240478768073352098711 482314860718152110028148067)
            ·
              refine ⟨723472291077228165042222101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482314860718152110028148067 723472291077228165042222101)
              ·
                refine ⟨33912763644245070236354161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 723472291077228165042222101 33912763644245070236354161)
                ·
                  refine ⟨25434572733183802677265621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33912763644245070236354161 25434572733183802677265621)
                  ·
                    refine ⟨596122798433995375248413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25434572733183802677265621 596122798433995375248413)
                    ·
                      rfl

theorem cell23_3482835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 7].length) (baseStart_3482835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482835 prefixEnd_3482835 := by exact prefixLift 3482835
  have htrace : WordTrace (prefixWord ++ tailWord_3482835) baseStart_3482835 baseEnd_3482835 := by
    simpa [prefixWord, tailWord_3482835, baseEnd_3482835] using wordTrace_append hprefix tailTrace_3482835
  have hstable : (prefixWord ++ tailWord_3482835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482835).length < 2 ^ (prefixWord ++ tailWord_3482835).sum := by decide
  have hdescent : baseEnd_3482835 < baseStart_3482835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482849 : List Nat := [1, 2, 3, 1, 3, 3, 1, 2, 1, 3, 3]
def baseStart_3482849 : Nat := 118140960795 + 3482849 * 2 ^ 59
def prefixEnd_3482849 : Nat := 4983230072969 + 3 ^ 40 * 3482849 * 2
def baseEnd_3482849 : Nat := 1788375584031149070970175

theorem tailTrace_3482849 : CollatzResearch.WordTrace tailWord_3482849 prefixEnd_3482849 1788375584031149070970175 := by
  unfold tailWord_3482849
  simp only [CollatzResearch.WordTrace]
  refine ⟨127029938959240371098011601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84686625972826914065341067 127029938959240371098011601)
  ·
    refine ⟨95272454219430278323508701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127029938959240371098011601 95272454219430278323508701)
    ·
      refine ⟨35727170332286354371315763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95272454219430278323508701 35727170332286354371315763)
      ·
        refine ⟨53590755498429531556973645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35727170332286354371315763 53590755498429531556973645)
        ·
          refine ⟨20096533311911074333865117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53590755498429531556973645 20096533311911074333865117)
          ·
            refine ⟨7536199991966652875199419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20096533311911074333865117 7536199991966652875199419)
            ·
              refine ⟨11304299987949979312799129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7536199991966652875199419 11304299987949979312799129)
              ·
                refine ⟨8478224990962484484599347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11304299987949979312799129 8478224990962484484599347)
                ·
                  refine ⟨12717337486443726726899021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8478224990962484484599347 12717337486443726726899021)
                  ·
                    refine ⟨4769001557416397522587133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12717337486443726726899021 4769001557416397522587133)
                    ·
                      refine ⟨1788375584031149070970175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4769001557416397522587133 1788375584031149070970175)
                      ·
                        rfl

theorem cell23_3482849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_3482849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482849 prefixEnd_3482849 := by exact prefixLift 3482849
  have htrace : WordTrace (prefixWord ++ tailWord_3482849) baseStart_3482849 baseEnd_3482849 := by
    simpa [prefixWord, tailWord_3482849, baseEnd_3482849] using wordTrace_append hprefix tailTrace_3482849
  have hstable : (prefixWord ++ tailWord_3482849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482849).length < 2 ^ (prefixWord ++ tailWord_3482849).sum := by decide
  have hdescent : baseEnd_3482849 < baseStart_3482849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482853 : List Nat := [1, 3, 1, 4, 3, 1, 3, 1, 1, 2, 3]
def baseStart_3482853 : Nat := 118140960795 + 3482853 * 2 ^ 59
def prefixEnd_3482853 : Nat := 4983230072969 + 3 ^ 40 * 3482853 * 2
def baseEnd_3482853 : Nat := 1788377637953767055320157

theorem tailTrace_3482853 : CollatzResearch.WordTrace tailWord_3482853 prefixEnd_3482853 1788377637953767055320157 := by
  unfold tailWord_3482853
  simp only [CollatzResearch.WordTrace]
  refine ⟨127030084851225879781157213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84686723234150586520771475 127030084851225879781157213)
  ·
    refine ⟨47636281819209704917933955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127030084851225879781157213 47636281819209704917933955)
    ·
      refine ⟨71454422728814557376900933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47636281819209704917933955 71454422728814557376900933)
      ·
        refine ⟨13397704261652729508168925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71454422728814557376900933 13397704261652729508168925)
        ·
          refine ⟨5024139098119773565563347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13397704261652729508168925 5024139098119773565563347)
          ·
            refine ⟨7536208647179660348345021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5024139098119773565563347 7536208647179660348345021)
            ·
              refine ⟨2826078242692372630629383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7536208647179660348345021 2826078242692372630629383)
              ·
                refine ⟨4239117364038558945944075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2826078242692372630629383 4239117364038558945944075)
                ·
                  refine ⟨6358676046057838418916113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4239117364038558945944075 6358676046057838418916113)
                  ·
                    refine ⟨4769007034543378814187085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6358676046057838418916113 4769007034543378814187085)
                    ·
                      refine ⟨1788377637953767055320157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4769007034543378814187085 1788377637953767055320157)
                      ·
                        rfl

theorem cell23_3482853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_3482853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482853 prefixEnd_3482853 := by exact prefixLift 3482853
  have htrace : WordTrace (prefixWord ++ tailWord_3482853) baseStart_3482853 baseEnd_3482853 := by
    simpa [prefixWord, tailWord_3482853, baseEnd_3482853] using wordTrace_append hprefix tailTrace_3482853
  have hstable : (prefixWord ++ tailWord_3482853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482853).length < 2 ^ (prefixWord ++ tailWord_3482853).sum := by decide
  have hdescent : baseEnd_3482853 < baseStart_3482853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482862 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 2, 2, 5]
def baseStart_3482862 : Nat := 118140960795 + 3482862 * 2 ^ 59
def prefixEnd_3482862 : Nat := 4983230072969 + 3 ^ 40 * 3482862 * 2
def baseEnd_3482862 : Nat := 1788382259279657520107615

theorem tailTrace_3482862 : CollatzResearch.WordTrace tailWord_3482862 prefixEnd_3482862 1788382259279657520107615 := by
  unfold tailWord_3482862
  simp only [CollatzResearch.WordTrace]
  refine ⟨15878801638524159289779355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84686942072128849545489893 15878801638524159289779355)
  ·
    refine ⟨23818202457786238934669033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15878801638524159289779355 23818202457786238934669033)
    ·
      refine ⟨17863651843339679201001775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23818202457786238934669033 17863651843339679201001775)
      ·
        refine ⟨26795477765009518801502663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17863651843339679201001775 26795477765009518801502663)
        ·
          refine ⟨40193216647514278202253995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26795477765009518801502663 40193216647514278202253995)
          ·
            refine ⟨60289824971271417303380993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40193216647514278202253995 60289824971271417303380993)
            ·
              refine ⟨45217368728453562977535745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60289824971271417303380993 45217368728453562977535745)
              ·
                refine ⟨33913026546340172233151809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45217368728453562977535745 33913026546340172233151809)
                ·
                  refine ⟨25434769909755129174863857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33913026546340172233151809 25434769909755129174863857)
                  ·
                    refine ⟨19076077432316346881147893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25434769909755129174863857 19076077432316346881147893)
                    ·
                      refine ⟨1788382259279657520107615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19076077432316346881147893 1788382259279657520107615)
                      ·
                        rfl

theorem cell23_3482862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_3482862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482862 prefixEnd_3482862 := by exact prefixLift 3482862
  have htrace : WordTrace (prefixWord ++ tailWord_3482862) baseStart_3482862 baseEnd_3482862 := by
    simpa [prefixWord, tailWord_3482862, baseEnd_3482862] using wordTrace_append hprefix tailTrace_3482862
  have hstable : (prefixWord ++ tailWord_3482862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482862).length < 2 ^ (prefixWord ++ tailWord_3482862).sum := by decide
  have hdescent : baseEnd_3482862 < baseStart_3482862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482906 : List Nat := [3, 1, 1, 3, 3, 1, 2, 2, 1, 4, 2]
def baseStart_3482906 : Nat := 118140960795 + 3482906 * 2 ^ 59
def prefixEnd_3482906 : Nat := 4983230072969 + 3 ^ 40 * 3482906 * 2
def baseEnd_3482906 : Nat := 1788404852428455347957413

theorem tailTrace_3482906 : CollatzResearch.WordTrace tailWord_3482906 prefixEnd_3482906 1788404852428455347957413 := by
  unfold tailWord_3482906
  simp only [CollatzResearch.WordTrace]
  refine ⟨31758004480008467458209143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84688011946689246555224381 31758004480008467458209143)
  ·
    refine ⟨47637006720012701187313715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31758004480008467458209143 47637006720012701187313715)
    ·
      refine ⟨71455510080019051780970573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47637006720012701187313715 71455510080019051780970573)
      ·
        refine ⟨26795816280007144417863965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71455510080019051780970573 26795816280007144417863965)
        ·
          refine ⟨10048431105002679156698987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26795816280007144417863965 10048431105002679156698987)
          ·
            refine ⟨15072646657504018735048481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10048431105002679156698987 15072646657504018735048481)
            ·
              refine ⟨11304484993128014051286361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15072646657504018735048481 11304484993128014051286361)
              ·
                refine ⟨8478363744846010538464771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11304484993128014051286361 8478363744846010538464771)
                ·
                  refine ⟨12717545617269015807697157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8478363744846010538464771 12717545617269015807697157)
                  ·
                    refine ⟨2384539803237940463943217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12717545617269015807697157 2384539803237940463943217)
                    ·
                      refine ⟨1788404852428455347957413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2384539803237940463943217 1788404852428455347957413)
                      ·
                        rfl

theorem cell23_3482906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_3482906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482906 prefixEnd_3482906 := by exact prefixLift 3482906
  have htrace : WordTrace (prefixWord ++ tailWord_3482906) baseStart_3482906 baseEnd_3482906 := by
    simpa [prefixWord, tailWord_3482906, baseEnd_3482906] using wordTrace_append hprefix tailTrace_3482906
  have hstable : (prefixWord ++ tailWord_3482906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482906).length < 2 ^ (prefixWord ++ tailWord_3482906).sum := by decide
  have hdescent : baseEnd_3482906 < baseStart_3482906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482929 : List Nat := [1, 2, 2, 3, 3, 2, 2, 1, 7]
def baseStart_3482929 : Nat := 118140960795 + 3482929 * 2 ^ 59
def prefixEnd_3482929 : Nat := 4983230072969 + 3 ^ 40 * 3482929 * 2
def baseEnd_3482929 : Nat := 198712962498167639774423

theorem tailTrace_3482929 : CollatzResearch.WordTrace tailWord_3482929 prefixEnd_3482929 198712962498167639774423 := by
  unfold tailWord_3482929
  simp only [CollatzResearch.WordTrace]
  refine ⟨127032856798950544760923841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84688571199300363173949227 127032856798950544760923841)
  ·
    refine ⟨95274642599212908570692881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127032856798950544760923841 95274642599212908570692881)
    ·
      refine ⟨71455981949409681428019661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95274642599212908570692881 71455981949409681428019661)
      ·
        refine ⟨26795993231028630535507373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71455981949409681428019661 26795993231028630535507373)
        ·
          refine ⟨10048497461635736450815265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26795993231028630535507373 10048497461635736450815265)
          ·
            refine ⟨7536373096226802338111449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10048497461635736450815265 7536373096226802338111449)
            ·
              refine ⟨5652279822170101753583587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7536373096226802338111449 5652279822170101753583587)
              ·
                refine ⟨8478419733255152630375381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5652279822170101753583587 8478419733255152630375381)
                ·
                  refine ⟨198712962498167639774423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8478419733255152630375381 198712962498167639774423)
                  ·
                    rfl

theorem cell23_3482929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 7].length) (baseStart_3482929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482929 prefixEnd_3482929 := by exact prefixLift 3482929
  have htrace : WordTrace (prefixWord ++ tailWord_3482929) baseStart_3482929 baseEnd_3482929 := by
    simpa [prefixWord, tailWord_3482929, baseEnd_3482929] using wordTrace_append hprefix tailTrace_3482929
  have hstable : (prefixWord ++ tailWord_3482929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482929).length < 2 ^ (prefixWord ++ tailWord_3482929).sum := by decide
  have hdescent : baseEnd_3482929 < baseStart_3482929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482940 : List Nat := [2, 2, 2, 2, 1, 4, 3, 1, 2, 2, 2]
def baseStart_3482940 : Nat := 118140960795 + 3482940 * 2 ^ 59
def prefixEnd_3482940 : Nat := 4983230072969 + 3 ^ 40 * 3482940 * 2
def baseEnd_3482940 : Nat := 1788422310770708214932257

theorem tailTrace_3482940 : CollatzResearch.WordTrace tailWord_3482940 prefixEnd_3482940 1788422310770708214932257 := by
  unfold tailWord_3482940
  simp only [CollatzResearch.WordTrace]
  refine ⟨63516629000955346819787137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84688838667940462426382849 63516629000955346819787137)
  ·
    refine ⟨47637471750716510114840353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63516629000955346819787137 47637471750716510114840353)
    ·
      refine ⟨35728103813037382586130265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47637471750716510114840353 35728103813037382586130265)
      ·
        refine ⟨26796077859778036939597699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35728103813037382586130265 26796077859778036939597699)
        ·
          refine ⟨40194116789667055409396549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26796077859778036939597699 40194116789667055409396549)
          ·
            refine ⟨7536396898062572889261853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40194116789667055409396549 7536396898062572889261853)
            ·
              refine ⟨2826148836773464833473195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7536396898062572889261853 2826148836773464833473195)
              ·
                refine ⟨4239223255160197250209793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2826148836773464833473195 4239223255160197250209793)
                ·
                  refine ⟨3179417441370147937657345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4239223255160197250209793 3179417441370147937657345)
                  ·
                    refine ⟨2384563081027610953243009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3179417441370147937657345 2384563081027610953243009)
                    ·
                      refine ⟨1788422310770708214932257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2384563081027610953243009 1788422310770708214932257)
                      ·
                        rfl

theorem cell23_3482940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_3482940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3482940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3482940 prefixEnd_3482940 := by exact prefixLift 3482940
  have htrace : WordTrace (prefixWord ++ tailWord_3482940) baseStart_3482940 baseEnd_3482940 := by
    simpa [prefixWord, tailWord_3482940, baseEnd_3482940] using wordTrace_append hprefix tailTrace_3482940
  have hstable : (prefixWord ++ tailWord_3482940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482940).length < 2 ^ (prefixWord ++ tailWord_3482940).sum := by decide
  have hdescent : baseEnd_3482940 < baseStart_3482940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
