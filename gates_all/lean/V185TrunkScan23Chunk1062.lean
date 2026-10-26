import V185TrunkScan23Chunk1061

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6286783 : List Nat := [1, 1, 2, 2, 2, 1, 1, 6, 2, 5]
def baseStart_6286783 : Nat := 118140960795 + 6286783 * 2 ^ 59
def prefixEnd_6286783 : Nat := 4983230072969 + 3 ^ 40 * 6286783 * 2
def baseEnd_6286783 : Nat := 1076047149838327222100039

theorem tailTrace_6286783 : CollatzResearch.WordTrace tailWord_6286783 prefixEnd_6286783 1076047149838327222100039 := by
  unfold tailWord_6286783
  simp only [CollatzResearch.WordTrace]
  refine ⟨229297813583066362900121003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152865209055377575266747335 229297813583066362900121003)
  ·
    refine ⟨343946720374599544350181505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229297813583066362900121003 343946720374599544350181505)
    ·
      refine ⟨257960040280949658262636129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343946720374599544350181505 257960040280949658262636129)
      ·
        refine ⟨193470030210712243696977097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257960040280949658262636129 193470030210712243696977097)
        ·
          refine ⟨145102522658034182772732823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193470030210712243696977097 145102522658034182772732823)
          ·
            refine ⟨217653783987051274159099235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145102522658034182772732823 217653783987051274159099235)
            ·
              refine ⟨326480675980576911238648853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217653783987051274159099235 326480675980576911238648853)
              ·
                refine ⟨15303781686589542714311665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 326480675980576911238648853 15303781686589542714311665)
                ·
                  refine ⟨11477836264942157035733749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15303781686589542714311665 11477836264942157035733749)
                  ·
                    refine ⟨1076047149838327222100039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11477836264942157035733749 1076047149838327222100039)
                    ·
                      rfl

theorem cell23_6286783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 5].length) (baseStart_6286783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286783 prefixEnd_6286783 := by exact prefixLift 6286783
  have htrace : WordTrace (prefixWord ++ tailWord_6286783) baseStart_6286783 baseEnd_6286783 := by
    simpa [prefixWord, tailWord_6286783, baseEnd_6286783] using wordTrace_append hprefix tailTrace_6286783
  have hstable : (prefixWord ++ tailWord_6286783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286783).length < 2 ^ (prefixWord ++ tailWord_6286783).sum := by decide
  have hdescent : baseEnd_6286783 < baseStart_6286783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286820 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 1, 6, 2]
def baseStart_6286820 : Nat := 118140960795 + 6286820 * 2 ^ 59
def prefixEnd_6286820 : Nat := 4983230072969 + 3 ^ 40 * 6286820 * 2
def baseEnd_6286820 : Nat := 3228160448299198021537447

theorem tailTrace_6286820 : CollatzResearch.WordTrace tailWord_6286820 prefixEnd_6286820 3228160448299198021537447 := by
  unfold tailWord_6286820
  simp only [CollatzResearch.WordTrace]
  refine ⟨114649581541966159109608957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152866108722621545479478609 114649581541966159109608957)
  ·
    refine ⟨42993593078237309666103359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114649581541966159109608957 42993593078237309666103359)
    ·
      refine ⟨64490389617355964499155039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42993593078237309666103359 64490389617355964499155039)
      ·
        refine ⟨96735584426033946748732559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64490389617355964499155039 96735584426033946748732559)
        ·
          refine ⟨145103376639050920123098839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96735584426033946748732559 145103376639050920123098839)
          ·
            refine ⟨217655064958576380184648259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145103376639050920123098839 217655064958576380184648259)
            ·
              refine ⟨326482597437864570276972389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217655064958576380184648259 326482597437864570276972389)
              ·
                refine ⟨61215487019599606926932323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 326482597437864570276972389 61215487019599606926932323)
                ·
                  refine ⟨91823230529399410390398485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61215487019599606926932323 91823230529399410390398485)
                  ·
                    refine ⟨4304213931065597362049929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 91823230529399410390398485 4304213931065597362049929)
                    ·
                      refine ⟨3228160448299198021537447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4304213931065597362049929 3228160448299198021537447)
                      ·
                        rfl

theorem cell23_6286820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 1, 6, 2].length) (baseStart_6286820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286820 prefixEnd_6286820 := by exact prefixLift 6286820
  have htrace : WordTrace (prefixWord ++ tailWord_6286820) baseStart_6286820 baseEnd_6286820 := by
    simpa [prefixWord, tailWord_6286820, baseEnd_6286820] using wordTrace_append hprefix tailTrace_6286820
  have hstable : (prefixWord ++ tailWord_6286820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286820).length < 2 ^ (prefixWord ++ tailWord_6286820).sum := by decide
  have hdescent : baseEnd_6286820 < baseStart_6286820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286837 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_6286837 : Nat := 118140960795 + 6286837 * 2 ^ 59
def prefixEnd_6286837 : Nat := 4983230072969 + 3 ^ 40 * 6286837 * 2
def baseEnd_6286837 : Nat := 3228169177470324455024869

theorem tailTrace_6286837 : CollatzResearch.WordTrace tailWord_6286837 prefixEnd_6286837 3228169177470324455024869 := by
  unfold tailWord_6286837
  simp only [CollatzResearch.WordTrace]
  refine ⟨229299783124870730122586765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152866522083247153415057843 229299783124870730122586765)
  ·
    refine ⟨85987418671826523795970037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229299783124870730122586765 85987418671826523795970037)
    ·
      refine ⟨8061320500483736605872191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85987418671826523795970037 8061320500483736605872191)
      ·
        refine ⟨12091980750725604908808287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8061320500483736605872191 12091980750725604908808287)
        ·
          refine ⟨18137971126088407363212431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12091980750725604908808287 18137971126088407363212431)
          ·
            refine ⟨27206956689132611044818647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18137971126088407363212431 27206956689132611044818647)
            ·
              refine ⟨40810435033698916567227971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27206956689132611044818647 40810435033698916567227971)
              ·
                refine ⟨61215652550548374850841957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40810435033698916567227971 61215652550548374850841957)
                ·
                  refine ⟨11477934853227820284532867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61215652550548374850841957 11477934853227820284532867)
                  ·
                    refine ⟨17216902279841730426799301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11477934853227820284532867 17216902279841730426799301)
                    ·
                      refine ⟨3228169177470324455024869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17216902279841730426799301 3228169177470324455024869)
                      ·
                        rfl

theorem cell23_6286837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_6286837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286837 prefixEnd_6286837 := by exact prefixLift 6286837
  have htrace : WordTrace (prefixWord ++ tailWord_6286837) baseStart_6286837 baseEnd_6286837 := by
    simpa [prefixWord, tailWord_6286837, baseEnd_6286837] using wordTrace_append hprefix tailTrace_6286837
  have hstable : (prefixWord ++ tailWord_6286837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286837).length < 2 ^ (prefixWord ++ tailWord_6286837).sum := by decide
  have hdescent : baseEnd_6286837 < baseStart_6286837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286840 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 4, 2, 3]
def baseStart_6286840 : Nat := 118140960795 + 6286840 * 2 ^ 59
def prefixEnd_6286840 : Nat := 4983230072969 + 3 ^ 40 * 6286840 * 2
def baseEnd_6286840 : Nat := 3228170717912287943287355

theorem tailTrace_6286840 : CollatzResearch.WordTrace tailWord_6286840 prefixEnd_6286840 3228170717912287943287355 := by
  unfold tailWord_6286840
  simp only [CollatzResearch.WordTrace]
  refine ⟨114649946271929930817472987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152866595029239907756630649 114649946271929930817472987)
  ·
    refine ⟨171974919407894896226209481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114649946271929930817472987 171974919407894896226209481)
    ·
      refine ⟨128981189555921172169657111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171974919407894896226209481 128981189555921172169657111)
      ·
        refine ⟨193471784333881758254485667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128981189555921172169657111 193471784333881758254485667)
        ·
          refine ⟨290207676500822637381728501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193471784333881758254485667 290207676500822637381728501)
          ·
            refine ⟨27206969671952122254537047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 290207676500822637381728501 27206969671952122254537047)
            ·
              refine ⟨40810454507928183381805571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27206969671952122254537047 40810454507928183381805571)
              ·
                refine ⟨61215681761892275072708357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40810454507928183381805571 61215681761892275072708357)
                ·
                  refine ⟨11477940330354801576132817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61215681761892275072708357 11477940330354801576132817)
                  ·
                    refine ⟨8608455247766101182099613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11477940330354801576132817 8608455247766101182099613)
                    ·
                      refine ⟨3228170717912287943287355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8608455247766101182099613 3228170717912287943287355)
                      ·
                        rfl

theorem cell23_6286840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 4, 2, 3].length) (baseStart_6286840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286840 prefixEnd_6286840 := by exact prefixLift 6286840
  have htrace : WordTrace (prefixWord ++ tailWord_6286840) baseStart_6286840 baseEnd_6286840 := by
    simpa [prefixWord, tailWord_6286840, baseEnd_6286840] using wordTrace_append hprefix tailTrace_6286840
  have hstable : (prefixWord ++ tailWord_6286840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286840).length < 2 ^ (prefixWord ++ tailWord_6286840).sum := by decide
  have hdescent : baseEnd_6286840 < baseStart_6286840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286920 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 8, 4]
def baseStart_6286920 : Nat := 118140960795 + 6286920 * 2 ^ 59
def prefixEnd_6286920 : Nat := 4983230072969 + 3 ^ 40 * 6286920 * 2
def baseEnd_6286920 : Nat := 1076070598788215876762329

theorem tailTrace_6286920 : CollatzResearch.WordTrace tailWord_6286920 prefixEnd_6286920 1076070598788215876762329 := by
  unfold tailWord_6286920
  simp only [CollatzResearch.WordTrace]
  refine ⟨114651405191785017648929107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152868540255713356865238809 114651405191785017648929107)
  ·
    refine ⟨171977107787677526473393661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114651405191785017648929107 171977107787677526473393661)
    ·
      refine ⟨64491415420379072427522623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171977107787677526473393661 64491415420379072427522623)
      ·
        refine ⟨96737123130568608641283935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64491415420379072427522623 96737123130568608641283935)
        ·
          refine ⟨145105684695852912961925903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96737123130568608641283935 145105684695852912961925903)
          ·
            refine ⟨217658527043779369442888855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145105684695852912961925903 217658527043779369442888855)
            ·
              refine ⟨326487790565669054164333283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217658527043779369442888855 326487790565669054164333283)
              ·
                refine ⟨489731685848503581246499925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 326487790565669054164333283 489731685848503581246499925)
                ·
                  refine ⟨5739043193537151342732421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 489731685848503581246499925 5739043193537151342732421)
                  ·
                    refine ⟨1076070598788215876762329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5739043193537151342732421 1076070598788215876762329)
                    ·
                      rfl

theorem cell23_6286920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_6286920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286920 prefixEnd_6286920 := by exact prefixLift 6286920
  have htrace : WordTrace (prefixWord ++ tailWord_6286920) baseStart_6286920 baseEnd_6286920 := by
    simpa [prefixWord, tailWord_6286920, baseEnd_6286920] using wordTrace_append hprefix tailTrace_6286920
  have hstable : (prefixWord ++ tailWord_6286920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286920).length < 2 ^ (prefixWord ++ tailWord_6286920).sum := by decide
  have hdescent : baseEnd_6286920 < baseStart_6286920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286941 : List Nat := [1, 4, 4, 2, 1, 1, 1, 3, 1, 5]
def baseStart_6286941 : Nat := 118140960795 + 6286941 * 2 ^ 59
def prefixEnd_6286941 : Nat := 4983230072969 + 3 ^ 40 * 6286941 * 2
def baseEnd_6286941 : Nat := 1076074193152797349374797

theorem tailTrace_6286941 : CollatzResearch.WordTrace tailWord_6286941 prefixEnd_6286941 1076074193152797349374797 := by
  unfold tailWord_6286941
  simp only [CollatzResearch.WordTrace]
  refine ⟨229303576316493955884372677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152869050877662637256248451 229303576316493955884372677)
  ·
    refine ⟨42994420559342616728319877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229303576316493955884372677 42994420559342616728319877)
    ·
      refine ⟨8061453854876740636559977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42994420559342616728319877 8061453854876740636559977)
      ·
        refine ⟨6046090391157555477419983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8061453854876740636559977 6046090391157555477419983)
        ·
          refine ⟨9069135586736333216129975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6046090391157555477419983 9069135586736333216129975)
          ·
            refine ⟨13603703380104499824194963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9069135586736333216129975 13603703380104499824194963)
            ·
              refine ⟨20405555070156749736292445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13603703380104499824194963 20405555070156749736292445)
              ·
                refine ⟨7652083151308781151109667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20405555070156749736292445 7652083151308781151109667)
                ·
                  refine ⟨11478124726963171726664501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7652083151308781151109667 11478124726963171726664501)
                  ·
                    refine ⟨1076074193152797349374797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11478124726963171726664501 1076074193152797349374797)
                    ·
                      rfl

theorem cell23_6286941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_6286941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286941 prefixEnd_6286941 := by exact prefixLift 6286941
  have htrace : WordTrace (prefixWord ++ tailWord_6286941) baseStart_6286941 baseEnd_6286941 := by
    simpa [prefixWord, tailWord_6286941, baseEnd_6286941] using wordTrace_append hprefix tailTrace_6286941
  have hstable : (prefixWord ++ tailWord_6286941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286941).length < 2 ^ (prefixWord ++ tailWord_6286941).sum := by decide
  have hdescent : baseEnd_6286941 < baseStart_6286941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6286954 : List Nat := [3, 1, 3, 2, 1, 2, 3, 2, 2, 4]
def baseStart_6286954 : Nat := 118140960795 + 6286954 * 2 ^ 59
def prefixEnd_6286954 : Nat := 4983230072969 + 3 ^ 40 * 6286954 * 2
def baseEnd_6286954 : Nat := 1076076418235633499087277

theorem tailTrace_6286954 : CollatzResearch.WordTrace tailWord_6286954 prefixEnd_6286954 1076076418235633499087277 := by
  unfold tailWord_6286954
  simp only [CollatzResearch.WordTrace]
  refine ⟨57326012616361714776148979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152869366976964572736397277 57326012616361714776148979)
  ·
    refine ⟨85989018924542572164223469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57326012616361714776148979 85989018924542572164223469)
    ·
      refine ⟨32245882096703464561583801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85989018924542572164223469 32245882096703464561583801)
      ·
        refine ⟨24184411572527598421187851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32245882096703464561583801 24184411572527598421187851)
        ·
          refine ⟨36276617358791397631781777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24184411572527598421187851 36276617358791397631781777)
          ·
            refine ⟨27207463019093548223836333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36276617358791397631781777 27207463019093548223836333)
            ·
              refine ⟨10202798632160080583938625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27207463019093548223836333 10202798632160080583938625)
              ·
                refine ⟨7652098974120060437953969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10202798632160080583938625 7652098974120060437953969)
                ·
                  refine ⟨5739074230590045328465477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7652098974120060437953969 5739074230590045328465477)
                  ·
                    refine ⟨1076076418235633499087277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5739074230590045328465477 1076076418235633499087277)
                    ·
                      rfl

theorem cell23_6286954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_6286954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6286954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6286954 prefixEnd_6286954 := by exact prefixLift 6286954
  have htrace : WordTrace (prefixWord ++ tailWord_6286954) baseStart_6286954 baseEnd_6286954 := by
    simpa [prefixWord, tailWord_6286954, baseEnd_6286954] using wordTrace_append hprefix tailTrace_6286954
  have hstable : (prefixWord ++ tailWord_6286954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6286954).length < 2 ^ (prefixWord ++ tailWord_6286954).sum := by decide
  have hdescent : baseEnd_6286954 < baseStart_6286954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6286954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287038 : List Nat := [4, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2]
def baseStart_6287038 : Nat := 118140960795 + 6287038 * 2 ^ 59
def prefixEnd_6287038 : Nat := 4983230072969 + 3 ^ 40 * 6287038 * 2
def baseEnd_6287038 : Nat := 3228272387081878168611445

theorem tailTrace_6287038 : CollatzResearch.WordTrace tailWord_6287038 prefixEnd_6287038 3228272387081878168611445 := by
  unfold tailWord_6287038
  simp only [CollatzResearch.WordTrace]
  refine ⟨28663389274642817681331721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152871409464761694300435845 28663389274642817681331721)
  ·
    refine ⟨21497541955982113260998791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28663389274642817681331721 21497541955982113260998791)
    ·
      refine ⟨32246312933973169891498187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21497541955982113260998791 32246312933973169891498187)
      ·
        refine ⟨48369469400959754837247281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32246312933973169891498187 48369469400959754837247281)
        ·
          refine ⟨36277102050719816127935461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48369469400959754837247281 36277102050719816127935461)
          ·
            refine ⟨6801956634509965523987899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36277102050719816127935461 6801956634509965523987899)
            ·
              refine ⟨10202934951764948285981849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6801956634509965523987899 10202934951764948285981849)
              ·
                refine ⟨7652201213823711214486387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10202934951764948285981849 7652201213823711214486387)
                ·
                  refine ⟨11478301820735566821729581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7652201213823711214486387 11478301820735566821729581)
                  ·
                    refine ⟨4304363182775837558148593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11478301820735566821729581 4304363182775837558148593)
                    ·
                      refine ⟨3228272387081878168611445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4304363182775837558148593 3228272387081878168611445)
                      ·
                        rfl

theorem cell23_6287038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_6287038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287038 prefixEnd_6287038 := by exact prefixLift 6287038
  have htrace : WordTrace (prefixWord ++ tailWord_6287038) baseStart_6287038 baseEnd_6287038 := by
    simpa [prefixWord, tailWord_6287038, baseEnd_6287038] using wordTrace_append hprefix tailTrace_6287038
  have hstable : (prefixWord ++ tailWord_6287038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287038).length < 2 ^ (prefixWord ++ tailWord_6287038).sum := by decide
  have hdescent : baseEnd_6287038 < baseStart_6287038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287040 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 9]
def baseStart_6287040 : Nat := 118140960795 + 6287040 * 2 ^ 59
def prefixEnd_6287040 : Nat := 4983230072969 + 3 ^ 40 * 6287040 * 2
def baseEnd_6287040 : Nat := 358697046004798573420715

theorem tailTrace_6287040 : CollatzResearch.WordTrace tailWord_6287040 prefixEnd_6287040 358697046004798573420715 := by
  unfold tailWord_6287040
  simp only [CollatzResearch.WordTrace]
  refine ⟨114653593571567647896113287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152871458095423530528151049 114653593571567647896113287)
  ·
    refine ⟨171980390357351471844169931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114653593571567647896113287 171980390357351471844169931)
    ·
      refine ⟨257970585536027207766254897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171980390357351471844169931 257970585536027207766254897)
      ·
        refine ⟨193477939152020405824691173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257970585536027207766254897 193477939152020405824691173)
        ·
          refine ⟨36277113591003826092129595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193477939152020405824691173 36277113591003826092129595)
          ·
            refine ⟨54415670386505739138194393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36277113591003826092129595 54415670386505739138194393)
            ·
              refine ⟨40811752789879304353645795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54415670386505739138194393 40811752789879304353645795)
              ·
                refine ⟨61217629184818956530468693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40811752789879304353645795 61217629184818956530468693)
                ·
                  refine ⟨358697046004798573420715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61217629184818956530468693 358697046004798573420715)
                  ·
                    rfl

theorem cell23_6287040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 9].length) (baseStart_6287040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287040 prefixEnd_6287040 := by exact prefixLift 6287040
  have htrace : WordTrace (prefixWord ++ tailWord_6287040) baseStart_6287040 baseEnd_6287040 := by
    simpa [prefixWord, tailWord_6287040, baseEnd_6287040] using wordTrace_append hprefix tailTrace_6287040
  have hstable : (prefixWord ++ tailWord_6287040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287040).length < 2 ^ (prefixWord ++ tailWord_6287040).sum := by decide
  have hdescent : baseEnd_6287040 < baseStart_6287040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287144 : List Nat := [2, 1, 5, 1, 1, 2, 1, 2, 1, 4, 3]
def baseStart_6287144 : Nat := 118140960795 + 6287144 * 2 ^ 59
def prefixEnd_6287144 : Nat := 4983230072969 + 3 ^ 40 * 6287144 * 2
def baseEnd_6287144 : Nat := 3228326816031254753885957

theorem tailTrace_6287144 : CollatzResearch.WordTrace tailWord_6287144 prefixEnd_6287144 3228326816031254753885957 := by
  unfold tailWord_6287144
  simp only [CollatzResearch.WordTrace]
  refine ⟨114655490167379260777006243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152873986889839014369341657 114655490167379260777006243)
  ·
    refine ⟨171983235251068891165509365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114655490167379260777006243 171983235251068891165509365)
    ·
      refine ⟨16123428304787708546766503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 171983235251068891165509365 16123428304787708546766503)
      ·
        refine ⟨24185142457181562820149755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16123428304787708546766503 24185142457181562820149755)
        ·
          refine ⟨36277713685772344230224633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24185142457181562820149755 36277713685772344230224633)
          ·
            refine ⟨27208285264329258172668475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36277713685772344230224633 27208285264329258172668475)
            ·
              refine ⟨40812427896493887259002713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27208285264329258172668475 40812427896493887259002713)
              ·
                refine ⟨30609320922370415444252035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40812427896493887259002713 30609320922370415444252035)
                ·
                  refine ⟨45913981383555623166378053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30609320922370415444252035 45913981383555623166378053)
                  ·
                    refine ⟨8608871509416679343695885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45913981383555623166378053 8608871509416679343695885)
                    ·
                      refine ⟨3228326816031254753885957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8608871509416679343695885 3228326816031254753885957)
                      ·
                        rfl

theorem cell23_6287144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_6287144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287144 prefixEnd_6287144 := by exact prefixLift 6287144
  have htrace : WordTrace (prefixWord ++ tailWord_6287144) baseStart_6287144 baseEnd_6287144 := by
    simpa [prefixWord, tailWord_6287144, baseEnd_6287144] using wordTrace_append hprefix tailTrace_6287144
  have hstable : (prefixWord ++ tailWord_6287144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287144).length < 2 ^ (prefixWord ++ tailWord_6287144).sum := by decide
  have hdescent : baseEnd_6287144 < baseStart_6287144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287241 : List Nat := [1, 2, 1, 1, 5, 1, 4, 2, 2, 4]
def baseStart_6287241 : Nat := 118140960795 + 6287241 * 2 ^ 59
def prefixEnd_6287241 : Nat := 4983230072969 + 3 ^ 40 * 6287241 * 2
def baseEnd_6287241 : Nat := 1076125541218246958124337

theorem tailTrace_6287241 : CollatzResearch.WordTrace tailWord_6287241 prefixEnd_6287241 1076125541218246958124337 := by
  unfold tailWord_6287241
  simp only [CollatzResearch.WordTrace]
  refine ⟨229314518215407107120293577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152876345476938071413529051 229314518215407107120293577)
  ·
    refine ⟨171985888661555330340220183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229314518215407107120293577 171985888661555330340220183)
    ·
      refine ⟨257978832992332995510330275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171985888661555330340220183 257978832992332995510330275)
      ·
        refine ⟨386968249488499493265495413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257978832992332995510330275 386968249488499493265495413)
        ·
          refine ⟨36278273389546827493640195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 386968249488499493265495413 36278273389546827493640195)
          ·
            refine ⟨54417410084320241240460293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36278273389546827493640195 54417410084320241240460293)
            ·
              refine ⟨10203264390810045232586305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54417410084320241240460293 10203264390810045232586305)
              ·
                refine ⟨7652448293107533924439729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10203264390810045232586305 7652448293107533924439729)
                ·
                  refine ⟨5739336219830650443329797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7652448293107533924439729 5739336219830650443329797)
                  ·
                    refine ⟨1076125541218246958124337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5739336219830650443329797 1076125541218246958124337)
                    ·
                      rfl

theorem cell23_6287241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 2, 4].length) (baseStart_6287241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287241 prefixEnd_6287241 := by exact prefixLift 6287241
  have htrace : WordTrace (prefixWord ++ tailWord_6287241) baseStart_6287241 baseEnd_6287241 := by
    simpa [prefixWord, tailWord_6287241, baseEnd_6287241] using wordTrace_append hprefix tailTrace_6287241
  have hstable : (prefixWord ++ tailWord_6287241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287241).length < 2 ^ (prefixWord ++ tailWord_6287241).sum := by decide
  have hdescent : baseEnd_6287241 < baseStart_6287241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287257 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 2, 2, 6]
def baseStart_6287257 : Nat := 118140960795 + 6287257 * 2 ^ 59
def prefixEnd_6287257 : Nat := 4983230072969 + 3 ^ 40 * 6287257 * 2
def baseEnd_6287257 : Nat := 3228384839345212811772937

theorem tailTrace_6287257 : CollatzResearch.WordTrace tailWord_6287257 prefixEnd_6287257 3228384839345212811772937 := by
  unfold tailWord_6287257
  simp only [CollatzResearch.WordTrace]
  refine ⟨229315101783349141852876025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152876734522232761235250683 229315101783349141852876025)
  ·
    refine ⟨171986326337511856389657019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229315101783349141852876025 171986326337511856389657019)
    ·
      refine ⟨257979489506267784584485529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171986326337511856389657019 257979489506267784584485529)
      ·
        refine ⟨193484617129700838438364147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257979489506267784584485529 193484617129700838438364147)
        ·
          refine ⟨290226925694551257657546221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193484617129700838438364147 290226925694551257657546221)
          ·
            refine ⟨108835097135456721621579833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 290226925694551257657546221 108835097135456721621579833)
            ·
              refine ⟨81626322851592541216184875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108835097135456721621579833 81626322851592541216184875)
              ·
                refine ⟨122439484277388811824277313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81626322851592541216184875 122439484277388811824277313)
                ·
                  refine ⟨91829613208041608868207985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122439484277388811824277313 91829613208041608868207985)
                  ·
                    refine ⟨68872209906031206651155989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91829613208041608868207985 68872209906031206651155989)
                    ·
                      refine ⟨3228384839345212811772937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68872209906031206651155989 3228384839345212811772937)
                      ·
                        rfl

theorem cell23_6287257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_6287257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287257 prefixEnd_6287257 := by exact prefixLift 6287257
  have htrace : WordTrace (prefixWord ++ tailWord_6287257) baseStart_6287257 baseEnd_6287257 := by
    simpa [prefixWord, tailWord_6287257, baseEnd_6287257] using wordTrace_append hprefix tailTrace_6287257
  have hstable : (prefixWord ++ tailWord_6287257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287257).length < 2 ^ (prefixWord ++ tailWord_6287257).sum := by decide
  have hdescent : baseEnd_6287257 < baseStart_6287257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287261 : List Nat := [1, 4, 2, 1, 2, 3, 2, 1, 1, 2, 4]
def baseStart_6287261 : Nat := 118140960795 + 6287261 * 2 ^ 59
def prefixEnd_6287261 : Nat := 4983230072969 + 3 ^ 40 * 6287261 * 2
def baseEnd_6287261 : Nat := 3228386893267830796122919

theorem tailTrace_6287261 : CollatzResearch.WordTrace tailWord_6287261 prefixEnd_6287261 3228386893267830796122919 := by
  unfold tailWord_6287261
  simp only [CollatzResearch.WordTrace]
  refine ⟨229315247675334650536021637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152876831783556433690681091 229315247675334650536021637)
  ·
    refine ⟨42996608939125246975504057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229315247675334650536021637 42996608939125246975504057)
    ·
      refine ⟨32247456704343935231628043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42996608939125246975504057 32247456704343935231628043)
      ·
        refine ⟨48371185056515902847442065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32247456704343935231628043 48371185056515902847442065)
        ·
          refine ⟨36278388792386927135581549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48371185056515902847442065 36278388792386927135581549)
          ·
            refine ⟨13604395797145097675843081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36278388792386927135581549 13604395797145097675843081)
            ·
              refine ⟨10203296847858823256882311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13604395797145097675843081 10203296847858823256882311)
              ·
                refine ⟨15304945271788234885323467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10203296847858823256882311 15304945271788234885323467)
                ·
                  refine ⟨22957417907682352327985201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15304945271788234885323467 22957417907682352327985201)
                  ·
                    refine ⟨17218063430761764245988901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22957417907682352327985201 17218063430761764245988901)
                    ·
                      refine ⟨3228386893267830796122919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17218063430761764245988901 3228386893267830796122919)
                      ·
                        rfl

theorem cell23_6287261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_6287261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287261 prefixEnd_6287261 := by exact prefixLift 6287261
  have htrace : WordTrace (prefixWord ++ tailWord_6287261) baseStart_6287261 baseEnd_6287261 := by
    simpa [prefixWord, tailWord_6287261, baseEnd_6287261] using wordTrace_append hprefix tailTrace_6287261
  have hstable : (prefixWord ++ tailWord_6287261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287261).length < 2 ^ (prefixWord ++ tailWord_6287261).sum := by decide
  have hdescent : baseEnd_6287261 < baseStart_6287261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287265 : List Nat := [1, 2, 3, 4, 2, 1, 1, 2, 3, 2, 2]
def baseStart_6287265 : Nat := 118140960795 + 6287265 * 2 ^ 59
def prefixEnd_6287265 : Nat := 4983230072969 + 3 ^ 40 * 6287265 * 2
def baseEnd_6287265 : Nat := 3228388947190448780472901

theorem tailTrace_6287265 : CollatzResearch.WordTrace tailWord_6287265 prefixEnd_6287265 3228388947190448780472901 := by
  unfold tailWord_6287265
  simp only [CollatzResearch.WordTrace]
  refine ⟨229315393567320159219167249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152876929044880106146111499 229315393567320159219167249)
  ·
    refine ⟨171986545175490119414375437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229315393567320159219167249 171986545175490119414375437)
    ·
      refine ⟨64494954440808794780390789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171986545175490119414375437 64494954440808794780390789)
      ·
        refine ⟨12092803957651649021323273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64494954440808794780390789 12092803957651649021323273)
        ·
          refine ⟨9069602968238736765992455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12092803957651649021323273 9069602968238736765992455)
          ·
            refine ⟨13604404452358105148988683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9069602968238736765992455 13604404452358105148988683)
            ·
              refine ⟨20406606678537157723483025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13604404452358105148988683 20406606678537157723483025)
              ·
                refine ⟨15304955008902868292612269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20406606678537157723483025 15304955008902868292612269)
                ·
                  refine ⟨5739358128338575609729601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15304955008902868292612269 5739358128338575609729601)
                  ·
                    refine ⟨4304518596253931707297201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5739358128338575609729601 4304518596253931707297201)
                    ·
                      refine ⟨3228388947190448780472901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4304518596253931707297201 3228388947190448780472901)
                      ·
                        rfl

theorem cell23_6287265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_6287265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287265 prefixEnd_6287265 := by exact prefixLift 6287265
  have htrace : WordTrace (prefixWord ++ tailWord_6287265) baseStart_6287265 baseEnd_6287265 := by
    simpa [prefixWord, tailWord_6287265, baseEnd_6287265] using wordTrace_append hprefix tailTrace_6287265
  have hstable : (prefixWord ++ tailWord_6287265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287265).length < 2 ^ (prefixWord ++ tailWord_6287265).sum := by decide
  have hdescent : baseEnd_6287265 < baseStart_6287265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287267 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 4, 7]
def baseStart_6287267 : Nat := 118140960795 + 6287267 * 2 ^ 59
def prefixEnd_6287267 : Nat := 4983230072969 + 3 ^ 40 * 6287267 * 2
def baseEnd_6287267 : Nat := 1076129991383919257549297

theorem tailTrace_6287267 : CollatzResearch.WordTrace tailWord_6287267 prefixEnd_6287267 1076129991383919257549297 := by
  unfold tailWord_6287267
  simp only [CollatzResearch.WordTrace]
  refine ⟨229315466513312913560740055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152876977675541942373826703 229315466513312913560740055)
  ·
    refine ⟨343973199769969370341110083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229315466513312913560740055 343973199769969370341110083)
    ·
      refine ⟨515959799654954055511665125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343973199769969370341110083 515959799654954055511665125)
      ·
        refine ⟨96742462435303885408437211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 515959799654954055511665125 96742462435303885408437211)
        ·
          refine ⟨145113693652955828112655817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96742462435303885408437211 145113693652955828112655817)
          ·
            refine ⟨108835270239716871084491863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145113693652955828112655817 108835270239716871084491863)
            ·
              refine ⟨163252905359575306626737795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108835270239716871084491863 163252905359575306626737795)
              ·
                refine ⟨244879358039362959940106693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163252905359575306626737795 244879358039362959940106693)
                ·
                  refine ⟨45914879632380554988770005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 244879358039362959940106693 45914879632380554988770005)
                  ·
                    refine ⟨1076129991383919257549297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45914879632380554988770005 1076129991383919257549297)
                    ·
                      rfl

theorem cell23_6287267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 7].length) (baseStart_6287267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287267 prefixEnd_6287267 := by exact prefixLift 6287267
  have htrace : WordTrace (prefixWord ++ tailWord_6287267) baseStart_6287267 baseEnd_6287267 := by
    simpa [prefixWord, tailWord_6287267, baseEnd_6287267] using wordTrace_append hprefix tailTrace_6287267
  have hstable : (prefixWord ++ tailWord_6287267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287267).length < 2 ^ (prefixWord ++ tailWord_6287267).sum := by decide
  have hdescent : baseEnd_6287267 < baseStart_6287267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287271 : List Nat := [1, 1, 6, 1, 2, 2, 3, 7]
def baseStart_6287271 : Nat := 118140960795 + 6287271 * 2 ^ 59
def prefixEnd_6287271 : Nat := 4983230072969 + 3 ^ 40 * 6287271 * 2
def baseEnd_6287271 : Nat := 119570075113865768777699

theorem tailTrace_6287271 : CollatzResearch.WordTrace tailWord_6287271 prefixEnd_6287271 119570075113865768777699 := by
  unfold tailWord_6287271
  simp only [CollatzResearch.WordTrace]
  refine ⟨229315612405298422243885667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152877074936865614829257111 229315612405298422243885667)
  ·
    refine ⟨343973418607947633365828501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229315612405298422243885667 343973418607947633365828501)
    ·
      refine ⟨16123753997247545314023211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 343973418607947633365828501 16123753997247545314023211)
      ·
        refine ⟨24185630995871317971034817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16123753997247545314023211 24185630995871317971034817)
        ·
          refine ⟨18139223246903488478276113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24185630995871317971034817 18139223246903488478276113)
          ·
            refine ⟨13604417435177616358707085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18139223246903488478276113 13604417435177616358707085)
            ·
              refine ⟨5101656538191606134515157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13604417435177616358707085 5101656538191606134515157)
              ·
                refine ⟨119570075113865768777699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5101656538191606134515157 119570075113865768777699)
                ·
                  rfl

theorem cell23_6287271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 7].length) (baseStart_6287271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287271 prefixEnd_6287271 := by exact prefixLift 6287271
  have htrace : WordTrace (prefixWord ++ tailWord_6287271) baseStart_6287271 baseEnd_6287271 := by
    simpa [prefixWord, tailWord_6287271, baseEnd_6287271] using wordTrace_append hprefix tailTrace_6287271
  have hstable : (prefixWord ++ tailWord_6287271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287271).length < 2 ^ (prefixWord ++ tailWord_6287271).sum := by decide
  have hdescent : baseEnd_6287271 < baseStart_6287271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287281 : List Nat := [1, 2, 2, 4, 2, 1, 2, 2, 1, 3, 3]
def baseStart_6287281 : Nat := 118140960795 + 6287281 * 2 ^ 59
def prefixEnd_6287281 : Nat := 4983230072969 + 3 ^ 40 * 6287281 * 2
def baseEnd_6287281 : Nat := 3228397162880920717872827

theorem tailTrace_6287281 : CollatzResearch.WordTrace tailWord_6287281 prefixEnd_6287281 3228397162880920717872827 := by
  unfold tailWord_6287281
  simp only [CollatzResearch.WordTrace]
  refine ⟨229315977135262193951749697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152877318090174795967833131 229315977135262193951749697)
  ·
    refine ⟨171986982851446645463812273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229315977135262193951749697 171986982851446645463812273)
    ·
      refine ⟨128990237138584984097859205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171986982851446645463812273 128990237138584984097859205)
      ·
        refine ⟨24185669463484684518348601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128990237138584984097859205 24185669463484684518348601)
        ·
          refine ⟨18139252097613513388761451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24185669463484684518348601 18139252097613513388761451)
          ·
            refine ⟨27208878146420270083142177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18139252097613513388761451 27208878146420270083142177)
            ·
              refine ⟨20406658609815202562356633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27208878146420270083142177 20406658609815202562356633)
              ·
                refine ⟨15304993957361401921767475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20406658609815202562356633 15304993957361401921767475)
                ·
                  refine ⟨22957490936042102882651213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15304993957361401921767475 22957490936042102882651213)
                  ·
                    refine ⟨8609059101015788580994205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22957490936042102882651213 8609059101015788580994205)
                    ·
                      refine ⟨3228397162880920717872827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8609059101015788580994205 3228397162880920717872827)
                      ·
                        rfl

theorem cell23_6287281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_6287281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287281 prefixEnd_6287281 := by exact prefixLift 6287281
  have htrace : WordTrace (prefixWord ++ tailWord_6287281) baseStart_6287281 baseEnd_6287281 := by
    simpa [prefixWord, tailWord_6287281, baseEnd_6287281] using wordTrace_append hprefix tailTrace_6287281
  have hstable : (prefixWord ++ tailWord_6287281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287281).length < 2 ^ (prefixWord ++ tailWord_6287281).sum := by decide
  have hdescent : baseEnd_6287281 < baseStart_6287281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287285 : List Nat := [1, 3, 3, 2, 1, 4, 2, 1, 1, 2, 3]
def baseStart_6287285 : Nat := 118140960795 + 6287285 * 2 ^ 59
def prefixEnd_6287285 : Nat := 4983230072969 + 3 ^ 40 * 6287285 * 2
def baseEnd_6287285 : Nat := 3228399216803538702222809

theorem tailTrace_6287285 : CollatzResearch.WordTrace tailWord_6287285 prefixEnd_6287285 3228399216803538702222809 := by
  unfold tailWord_6287285
  simp only [CollatzResearch.WordTrace]
  refine ⟨229316123027247702634895309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152877415351498468423263539 229316123027247702634895309)
  ·
    refine ⟨85993546135217888488085741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229316123027247702634895309 85993546135217888488085741)
    ·
      refine ⟨32247579800706708183032153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85993546135217888488085741 32247579800706708183032153)
      ·
        refine ⟨24185684850530031137274115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32247579800706708183032153 24185684850530031137274115)
        ·
          refine ⟨36278527275795046705911173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24185684850530031137274115 36278527275795046705911173)
          ·
            refine ⟨6802223864211571257358345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36278527275795046705911173 6802223864211571257358345)
            ·
              refine ⟨5101667898158678443018759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6802223864211571257358345 5101667898158678443018759)
              ·
                refine ⟨7652501847238017664528139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5101667898158678443018759 7652501847238017664528139)
                ·
                  refine ⟨11478752770857026496792209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7652501847238017664528139 11478752770857026496792209)
                  ·
                    refine ⟨8609064578142769872594157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11478752770857026496792209 8609064578142769872594157)
                    ·
                      refine ⟨3228399216803538702222809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8609064578142769872594157 3228399216803538702222809)
                      ·
                        rfl

theorem cell23_6287285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_6287285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287285 prefixEnd_6287285 := by exact prefixLift 6287285
  have htrace : WordTrace (prefixWord ++ tailWord_6287285) baseStart_6287285 baseEnd_6287285 := by
    simpa [prefixWord, tailWord_6287285, baseEnd_6287285] using wordTrace_append hprefix tailTrace_6287285
  have hstable : (prefixWord ++ tailWord_6287285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287285).length < 2 ^ (prefixWord ++ tailWord_6287285).sum := by decide
  have hdescent : baseEnd_6287285 < baseStart_6287285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287292 : List Nat := [2, 2, 2, 5, 2, 1, 1, 2, 2, 4]
def baseStart_6287292 : Nat := 118140960795 + 6287292 * 2 ^ 59
def prefixEnd_6287292 : Nat := 4983230072969 + 3 ^ 40 * 6287292 * 2
def baseEnd_6287292 : Nat := 1076134270389373391611759

theorem tailTrace_6287292 : CollatzResearch.WordTrace tailWord_6287292 prefixEnd_6287292 1076134270389373391611759 := by
  unfold tailWord_6287292
  simp only [CollatzResearch.WordTrace]
  refine ⟨114658189169111171415200065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152877585558814895220266753 114658189169111171415200065)
  ·
    refine ⟨85993641876833378561400049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114658189169111171415200065 85993641876833378561400049)
    ·
      refine ⟨64495231407625033921050037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85993641876833378561400049 64495231407625033921050037)
      ·
        refine ⟨6046427944464846930098441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64495231407625033921050037 6046427944464846930098441)
        ·
          refine ⟨4534820958348635197573831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6046427944464846930098441 4534820958348635197573831)
          ·
            refine ⟨6802231437522952796360747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4534820958348635197573831 6802231437522952796360747)
            ·
              refine ⟨10203347156284429194541121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6802231437522952796360747 10203347156284429194541121)
              ·
                refine ⟨7652510367213321895905841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10203347156284429194541121 7652510367213321895905841)
                ·
                  refine ⟨5739382775409991421929381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7652510367213321895905841 5739382775409991421929381)
                  ·
                    refine ⟨1076134270389373391611759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5739382775409991421929381 1076134270389373391611759)
                    ·
                      rfl

theorem cell23_6287292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_6287292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287292 prefixEnd_6287292 := by exact prefixLift 6287292
  have htrace : WordTrace (prefixWord ++ tailWord_6287292) baseStart_6287292 baseEnd_6287292 := by
    simpa [prefixWord, tailWord_6287292, baseEnd_6287292] using wordTrace_append hprefix tailTrace_6287292
  have hstable : (prefixWord ++ tailWord_6287292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287292).length < 2 ^ (prefixWord ++ tailWord_6287292).sum := by decide
  have hdescent : baseEnd_6287292 < baseStart_6287292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287338 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 6, 2, 2]
def baseStart_6287338 : Nat := 118140960795 + 6287338 * 2 ^ 59
def prefixEnd_6287338 : Nat := 4983230072969 + 3 ^ 40 * 6287338 * 2
def baseEnd_6287338 : Nat := 3228426431278226994860065

theorem tailTrace_6287338 : CollatzResearch.WordTrace tailWord_6287338 prefixEnd_6287338 3228426431278226994860065 := by
  unfold tailWord_6287338
  simp only [CollatzResearch.WordTrace]
  refine ⟨57329514024013923171643667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152878704064037128457716445 57329514024013923171643667)
  ·
    refine ⟨85994271036020884757465501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57329514024013923171643667 85994271036020884757465501)
    ·
      refine ⟨32247851638507831784049563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85994271036020884757465501 32247851638507831784049563)
      ·
        refine ⟨48371777457761747676074345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32247851638507831784049563 48371777457761747676074345)
        ·
          refine ⟨36278833093321310757055759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48371777457761747676074345 36278833093321310757055759)
          ·
            refine ⟨54418249639981966135583639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36278833093321310757055759 54418249639981966135583639)
            ·
              refine ⟨81627374459972949203375459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54418249639981966135583639 81627374459972949203375459)
              ·
                refine ⟨122441061689959423805063189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81627374459972949203375459 122441061689959423805063189)
                ·
                  refine ⟨5739424766716847990862337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 122441061689959423805063189 5739424766716847990862337)
                  ·
                    refine ⟨4304568575037635993146753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5739424766716847990862337 4304568575037635993146753)
                    ·
                      refine ⟨3228426431278226994860065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4304568575037635993146753 3228426431278226994860065)
                      ·
                        rfl

theorem cell23_6287338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_6287338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287338 prefixEnd_6287338 := by exact prefixLift 6287338
  have htrace : WordTrace (prefixWord ++ tailWord_6287338) baseStart_6287338 baseEnd_6287338 := by
    simpa [prefixWord, tailWord_6287338, baseEnd_6287338] using wordTrace_append hprefix tailTrace_6287338
  have hstable : (prefixWord ++ tailWord_6287338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287338).length < 2 ^ (prefixWord ++ tailWord_6287338).sum := by decide
  have hdescent : baseEnd_6287338 < baseStart_6287338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287366 : List Nat := [6, 2, 1, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_6287366 : Nat := 118140960795 + 6287366 * 2 ^ 59
def prefixEnd_6287366 : Nat := 4983230072969 + 3 ^ 40 * 6287366 * 2
def baseEnd_6287366 : Nat := 3228440808736552885309937

theorem tailTrace_6287366 : CollatzResearch.WordTrace tailWord_6287366 prefixEnd_6287366 3228440808736552885309937 := by
  unfold tailWord_6287366
  simp only [CollatzResearch.WordTrace]
  refine ⟨7166221166873570420893561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 152879384893302835645729301 7166221166873570420893561)
  ·
    refine ⟨5374665875155177815670171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7166221166873570420893561 5374665875155177815670171)
    ·
      refine ⟨8061998812732766723505257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5374665875155177815670171 8061998812732766723505257)
      ·
        refine ⟨6046499109549575042628943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8061998812732766723505257 6046499109549575042628943)
        ·
          refine ⟨9069748664324362563943415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6046499109549575042628943 9069748664324362563943415)
          ·
            refine ⟨13604622996486543845915123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9069748664324362563943415 13604622996486543845915123)
            ·
              refine ⟨20406934494729815768872685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13604622996486543845915123 20406934494729815768872685)
              ·
                refine ⟨7652600435523680913327257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20406934494729815768872685 7652600435523680913327257)
                ·
                  refine ⟨5739450326642760684995443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7652600435523680913327257 5739450326642760684995443)
                  ·
                    refine ⟨8609175489964141027493165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5739450326642760684995443 8609175489964141027493165)
                    ·
                      refine ⟨3228440808736552885309937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8609175489964141027493165 3228440808736552885309937)
                      ·
                        rfl

theorem cell23_6287366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_6287366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287366 prefixEnd_6287366 := by exact prefixLift 6287366
  have htrace : WordTrace (prefixWord ++ tailWord_6287366) baseStart_6287366 baseEnd_6287366 := by
    simpa [prefixWord, tailWord_6287366, baseEnd_6287366] using wordTrace_append hprefix tailTrace_6287366
  have hstable : (prefixWord ++ tailWord_6287366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287366).length < 2 ^ (prefixWord ++ tailWord_6287366).sum := by decide
  have hdescent : baseEnd_6287366 < baseStart_6287366 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287384 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 1, 1, 7]
def baseStart_6287384 : Nat := 118140960795 + 6287384 * 2 ^ 59
def prefixEnd_6287384 : Nat := 4983230072969 + 3 ^ 40 * 6287384 * 2
def baseEnd_6287384 : Nat := 3228450051388333814884853

theorem tailTrace_6287384 : CollatzResearch.WordTrace tailWord_6287384 prefixEnd_6287384 3228450051388333814884853 := by
  unfold tailWord_6287384
  simp only [CollatzResearch.WordTrace]
  refine ⟨114659866926944521271374603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152879822569259361695166137 114659866926944521271374603)
  ·
    refine ⟨171989800390416781907061905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114659866926944521271374603 171989800390416781907061905)
    ·
      refine ⟨128992350292812586430296429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171989800390416781907061905 128992350292812586430296429)
      ·
        refine ⟨48372131359804719911361161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128992350292812586430296429 48372131359804719911361161)
        ·
          refine ⟨36279098519853539933520871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48372131359804719911361161 36279098519853539933520871)
          ·
            refine ⟨54418647779780309900281307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36279098519853539933520871 54418647779780309900281307)
            ·
              refine ⟨81627971669670464850421961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54418647779780309900281307 81627971669670464850421961)
              ·
                refine ⟨61220978752252848637816471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81627971669670464850421961 61220978752252848637816471)
                ·
                  refine ⟨91831468128379272956724707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61220978752252848637816471 91831468128379272956724707)
                  ·
                    refine ⟨137747202192568909435087061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91831468128379272956724707 137747202192568909435087061)
                    ·
                      refine ⟨3228450051388333814884853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 137747202192568909435087061 3228450051388333814884853)
                      ·
                        rfl

theorem cell23_6287384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_6287384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287384 prefixEnd_6287384 := by exact prefixLift 6287384
  have htrace : WordTrace (prefixWord ++ tailWord_6287384) baseStart_6287384 baseEnd_6287384 := by
    simpa [prefixWord, tailWord_6287384, baseEnd_6287384] using wordTrace_append hprefix tailTrace_6287384
  have hstable : (prefixWord ++ tailWord_6287384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287384).length < 2 ^ (prefixWord ++ tailWord_6287384).sum := by decide
  have hdescent : baseEnd_6287384 < baseStart_6287384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287391 : List Nat := [1, 1, 2, 4, 1, 2, 4, 1, 2, 5]
def baseStart_6287391 : Nat := 118140960795 + 6287391 * 2 ^ 59
def prefixEnd_6287391 : Nat := 4983230072969 + 3 ^ 40 * 6287391 * 2
def baseEnd_6287391 : Nat := 1076151215250971762499107

theorem tailTrace_6287391 : CollatzResearch.WordTrace tailWord_6287391 prefixEnd_6287391 1076151215250971762499107 := by
  unfold tailWord_6287391
  simp only [CollatzResearch.WordTrace]
  refine ⟨229319989164863682738254027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152879992776575788492169351 229319989164863682738254027)
  ·
    refine ⟨343979983747295524107381041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229319989164863682738254027 343979983747295524107381041)
    ·
      refine ⟨257984987810471643080535781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343979983747295524107381041 257984987810471643080535781)
      ·
        refine ⟨48372185214463433077600459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 257984987810471643080535781 48372185214463433077600459)
        ·
          refine ⟨72558277821695149616400689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48372185214463433077600459 72558277821695149616400689)
          ·
            refine ⟨54418708366271362212300517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72558277821695149616400689 54418708366271362212300517)
            ·
              refine ⟨10203507818675880414806347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54418708366271362212300517 10203507818675880414806347)
              ·
                refine ⟨15305261728013820622209521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10203507818675880414806347 15305261728013820622209521)
                ·
                  refine ⟨11478946296010365466657141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15305261728013820622209521 11478946296010365466657141)
                  ·
                    refine ⟨1076151215250971762499107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11478946296010365466657141 1076151215250971762499107)
                    ·
                      rfl

theorem cell23_6287391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 5].length) (baseStart_6287391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287391 prefixEnd_6287391 := by exact prefixLift 6287391
  have htrace : WordTrace (prefixWord ++ tailWord_6287391) baseStart_6287391 baseEnd_6287391 := by
    simpa [prefixWord, tailWord_6287391, baseEnd_6287391] using wordTrace_append hprefix tailTrace_6287391
  have hstable : (prefixWord ++ tailWord_6287391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287391).length < 2 ^ (prefixWord ++ tailWord_6287391).sum := by decide
  have hdescent : baseEnd_6287391 < baseStart_6287391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287411 : List Nat := [1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 4]
def baseStart_6287411 : Nat := 118140960795 + 6287411 * 2 ^ 59
def prefixEnd_6287411 : Nat := 4983230072969 + 3 ^ 40 * 6287411 * 2
def baseEnd_6287411 : Nat := 3228463915366005209247229

theorem tailTrace_6287411 : CollatzResearch.WordTrace tailWord_6287411 prefixEnd_6287411 3228463915366005209247229 := by
  unfold tailWord_6287411
  simp only [CollatzResearch.WordTrace]
  refine ⟨229320718624791226153982087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152880479083194150769321391 229320718624791226153982087)
  ·
    refine ⟨343981077937186839230973131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229320718624791226153982087 343981077937186839230973131)
    ·
      refine ⟨515971616905780258846459697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343981077937186839230973131 515971616905780258846459697)
      ·
        refine ⟨386978712679335194134844773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 515971616905780258846459697 386978712679335194134844773)
        ·
          refine ⟨72558508627375348900283395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 386978712679335194134844773 72558508627375348900283395)
          ·
            refine ⟨108837762941063023350425093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72558508627375348900283395 108837762941063023350425093)
            ·
              refine ⟨20407080551449316878204705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108837762941063023350425093 20407080551449316878204705)
              ·
                refine ⟨15305310413586987658653529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20407080551449316878204705 15305310413586987658653529)
                ·
                  refine ⟨11478982810190240743990147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15305310413586987658653529 11478982810190240743990147)
                  ·
                    refine ⟨17218474215285361115985221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11478982810190240743990147 17218474215285361115985221)
                    ·
                      refine ⟨3228463915366005209247229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17218474215285361115985221 3228463915366005209247229)
                      ·
                        rfl

theorem cell23_6287411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 4].length) (baseStart_6287411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287411 prefixEnd_6287411 := by exact prefixLift 6287411
  have htrace : WordTrace (prefixWord ++ tailWord_6287411) baseStart_6287411 baseEnd_6287411 := by
    simpa [prefixWord, tailWord_6287411, baseEnd_6287411] using wordTrace_append hprefix tailTrace_6287411
  have hstable : (prefixWord ++ tailWord_6287411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287411).length < 2 ^ (prefixWord ++ tailWord_6287411).sum := by decide
  have hdescent : baseEnd_6287411 < baseStart_6287411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287431 : List Nat := [1, 1, 4, 1, 3, 1, 2, 2, 1, 4, 3]
def baseStart_6287431 : Nat := 118140960795 + 6287431 * 2 ^ 59
def prefixEnd_6287431 : Nat := 4983230072969 + 3 ^ 40 * 6287431 * 2
def baseEnd_6287431 : Nat := 3228474184979095130997137

theorem tailTrace_6287431 : CollatzResearch.WordTrace tailWord_6287431 prefixEnd_6287431 3228474184979095130997137 := by
  unfold tailWord_6287431
  simp only [CollatzResearch.WordTrace]
  refine ⟨229321448084718769569710147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152880965389812513046473431 229321448084718769569710147)
  ·
    refine ⟨343982172127078154354565221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229321448084718769569710147 343982172127078154354565221)
    ·
      refine ⟨64496657273827153941480979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 343982172127078154354565221 64496657273827153941480979)
      ·
        refine ⟨96744985910740730912221469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64496657273827153941480979 96744985910740730912221469)
        ·
          refine ⟨36279369716527774092083051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96744985910740730912221469 36279369716527774092083051)
          ·
            refine ⟨54419054574791661138124577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36279369716527774092083051 54419054574791661138124577)
            ·
              refine ⟨40814290931093745853593433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54419054574791661138124577 40814290931093745853593433)
              ·
                refine ⟨30610718198320309390195075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40814290931093745853593433 30610718198320309390195075)
                ·
                  refine ⟨45916077297480464085292613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30610718198320309390195075 45916077297480464085292613)
                  ·
                    refine ⟨8609264493277587015992365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45916077297480464085292613 8609264493277587015992365)
                    ·
                      refine ⟨3228474184979095130997137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8609264493277587015992365 3228474184979095130997137)
                      ·
                        rfl

theorem cell23_6287431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_6287431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287431 prefixEnd_6287431 := by exact prefixLift 6287431
  have htrace : WordTrace (prefixWord ++ tailWord_6287431) baseStart_6287431 baseEnd_6287431 := by
    simpa [prefixWord, tailWord_6287431, baseEnd_6287431] using wordTrace_append hprefix tailTrace_6287431
  have hstable : (prefixWord ++ tailWord_6287431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287431).length < 2 ^ (prefixWord ++ tailWord_6287431).sum := by decide
  have hdescent : baseEnd_6287431 < baseStart_6287431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287434 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 10]
def baseStart_6287434 : Nat := 118140960795 + 6287434 * 2 ^ 59
def prefixEnd_6287434 : Nat := 4983230072969 + 3 ^ 40 * 6287434 * 2
def baseEnd_6287434 : Nat := 358719525046784291028847

theorem tailTrace_6287434 : CollatzResearch.WordTrace tailWord_6287434 prefixEnd_6287434 358719525046784291028847 := by
  unfold tailWord_6287434
  simp only [CollatzResearch.WordTrace]
  refine ⟨57330389375926975270517339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152881038335805267388046237 57330389375926975270517339)
  ·
    refine ⟨85995584063890462905776009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57330389375926975270517339 85995584063890462905776009)
    ·
      refine ⟨64496688047917847179332007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85995584063890462905776009 64496688047917847179332007)
      ·
        refine ⟨96745032071876770768998011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64496688047917847179332007 96745032071876770768998011)
        ·
          refine ⟨145117548107815156153497017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96745032071876770768998011 145117548107815156153497017)
          ·
            refine ⟨108838161080861367115122763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145117548107815156153497017 108838161080861367115122763)
            ·
              refine ⟨163257241621292050672684145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108838161080861367115122763 163257241621292050672684145)
              ·
                refine ⟨122442931215969038004513109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163257241621292050672684145 122442931215969038004513109)
                ·
                  refine ⟨358719525046784291028847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 122442931215969038004513109 358719525046784291028847)
                  ·
                    rfl

theorem cell23_6287434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 10].length) (baseStart_6287434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287434 prefixEnd_6287434 := by exact prefixLift 6287434
  have htrace : WordTrace (prefixWord ++ tailWord_6287434) baseStart_6287434 baseEnd_6287434 := by
    simpa [prefixWord, tailWord_6287434, baseEnd_6287434] using wordTrace_append hprefix tailTrace_6287434
  have hstable : (prefixWord ++ tailWord_6287434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287434).length < 2 ^ (prefixWord ++ tailWord_6287434).sum := by decide
  have hdescent : baseEnd_6287434 < baseStart_6287434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287438 : List Nat := [4, 1, 1, 1, 1, 5, 1, 2, 3, 4]
def baseStart_6287438 : Nat := 118140960795 + 6287438 * 2 ^ 59
def prefixEnd_6287438 : Nat := 4983230072969 + 3 ^ 40 * 6287438 * 2
def baseEnd_6287438 : Nat := 1076159259781225534536535

theorem tailTrace_6287438 : CollatzResearch.WordTrace tailWord_6287438 prefixEnd_6287438 1076159259781225534536535 := by
  unfold tailWord_6287438
  simp only [CollatzResearch.WordTrace]
  refine ⟨28665212924461676220651871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152881135597128939843476645 28665212924461676220651871)
  ·
    refine ⟨42997819386692514330977807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28665212924461676220651871 42997819386692514330977807)
    ·
      refine ⟨64496729080038771496466711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42997819386692514330977807 64496729080038771496466711)
      ·
        refine ⟨96745093620058157244700067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64496729080038771496466711 96745093620058157244700067)
        ·
          refine ⟨145117640430087235867050101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96745093620058157244700067 145117640430087235867050101)
          ·
            refine ⟨13604778790320678362535947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 145117640430087235867050101 13604778790320678362535947)
            ·
              refine ⟨20407168185481017543803921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13604778790320678362535947 20407168185481017543803921)
              ·
                refine ⟨15305376139110763157852941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20407168185481017543803921 15305376139110763157852941)
                ·
                  refine ⟨5739516052166536184194853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15305376139110763157852941 5739516052166536184194853)
                  ·
                    refine ⟨1076159259781225534536535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5739516052166536184194853 1076159259781225534536535)
                    ·
                      rfl

theorem cell23_6287438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_6287438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287438 prefixEnd_6287438 := by exact prefixLift 6287438
  have htrace : WordTrace (prefixWord ++ tailWord_6287438) baseStart_6287438 baseEnd_6287438 := by
    simpa [prefixWord, tailWord_6287438, baseEnd_6287438] using wordTrace_append hprefix tailTrace_6287438
  have hstable : (prefixWord ++ tailWord_6287438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287438).length < 2 ^ (prefixWord ++ tailWord_6287438).sum := by decide
  have hdescent : baseEnd_6287438 < baseStart_6287438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287448 : List Nat := [2, 1, 2, 2, 1, 4, 3, 1, 2, 2, 3]
def baseStart_6287448 : Nat := 118140960795 + 6287448 * 2 ^ 59
def prefixEnd_6287448 : Nat := 4983230072969 + 3 ^ 40 * 6287448 * 2
def baseEnd_6287448 : Nat := 3228482914150221564484559

theorem tailTrace_6287448 : CollatzResearch.WordTrace tailWord_6287448 prefixEnd_6287448 3228482914150221564484559 := by
  unfold tailWord_6287448
  simp only [CollatzResearch.WordTrace]
  refine ⟨114661034062828590736539499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152881378750438120982052665 114661034062828590736539499)
  ·
    refine ⟨171991551094242886104809249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114661034062828590736539499 171991551094242886104809249)
    ·
      refine ⟨128993663320682164578606937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171991551094242886104809249 128993663320682164578606937)
      ·
        refine ⟨96745247490511623433955203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128993663320682164578606937 96745247490511623433955203)
        ·
          refine ⟨145117871235767435150932805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96745247490511623433955203 145117871235767435150932805)
          ·
            refine ⟨27209600856706394090799901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145117871235767435150932805 27209600856706394090799901)
            ·
              refine ⟨10203600321264897784049963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27209600856706394090799901 10203600321264897784049963)
              ·
                refine ⟨15305400481897346676074945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10203600321264897784049963 15305400481897346676074945)
                ·
                  refine ⟨11479050361423010007056209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15305400481897346676074945 11479050361423010007056209)
                  ·
                    refine ⟨8609287771067257505292157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11479050361423010007056209 8609287771067257505292157)
                    ·
                      refine ⟨3228482914150221564484559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8609287771067257505292157 3228482914150221564484559)
                      ·
                        rfl

theorem cell23_6287448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_6287448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287448 prefixEnd_6287448 := by exact prefixLift 6287448
  have htrace : WordTrace (prefixWord ++ tailWord_6287448) baseStart_6287448 baseEnd_6287448 := by
    simpa [prefixWord, tailWord_6287448, baseEnd_6287448] using wordTrace_append hprefix tailTrace_6287448
  have hstable : (prefixWord ++ tailWord_6287448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287448).length < 2 ^ (prefixWord ++ tailWord_6287448).sum := by decide
  have hdescent : baseEnd_6287448 < baseStart_6287448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287468 : List Nat := [2, 2, 1, 1, 3, 5, 1, 2, 6]
def baseStart_6287468 : Nat := 118140960795 + 6287468 * 2 ^ 59
def prefixEnd_6287468 : Nat := 4983230072969 + 3 ^ 40 * 6287468 * 2
def baseEnd_6287468 : Nat := 358721464862590165137163

theorem tailTrace_6287468 : CollatzResearch.WordTrace tailWord_6287468 prefixEnd_6287468 358721464862590165137163 := by
  unfold tailWord_6287468
  simp only [CollatzResearch.WordTrace]
  refine ⟨114661398792792362444403529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152881865057056483259204705 114661398792792362444403529)
  ·
    refine ⟨85996049094594271833302647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114661398792792362444403529 85996049094594271833302647)
    ·
      refine ⟨128994073641891407749953971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85996049094594271833302647 128994073641891407749953971)
      ·
        refine ⟨193491110462837111624930957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128994073641891407749953971 193491110462837111624930957)
        ·
          refine ⟨72559166423563916859349109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193491110462837111624930957 72559166423563916859349109)
          ·
            refine ⟨6802421852209117205563979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72559166423563916859349109 6802421852209117205563979)
            ·
              refine ⟨10203632778313675808345969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6802421852209117205563979 10203632778313675808345969)
              ·
                refine ⟨7652724583735256856259477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10203632778313675808345969 7652724583735256856259477)
                ·
                  refine ⟨358721464862590165137163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7652724583735256856259477 358721464862590165137163)
                  ·
                    rfl

theorem cell23_6287468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 6].length) (baseStart_6287468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287468 prefixEnd_6287468 := by exact prefixLift 6287468
  have htrace : WordTrace (prefixWord ++ tailWord_6287468) baseStart_6287468 baseEnd_6287468 := by
    simpa [prefixWord, tailWord_6287468, baseEnd_6287468] using wordTrace_append hprefix tailTrace_6287468
  have hstable : (prefixWord ++ tailWord_6287468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287468).length < 2 ^ (prefixWord ++ tailWord_6287468).sum := by decide
  have hdescent : baseEnd_6287468 < baseStart_6287468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287498 : List Nat := [3, 1, 2, 3, 1, 2, 1, 4, 1, 5]
def baseStart_6287498 : Nat := 118140960795 + 6287498 * 2 ^ 59
def prefixEnd_6287498 : Nat := 4983230072969 + 3 ^ 40 * 6287498 * 2
def baseEnd_6287498 : Nat := 1076169529394315456286443

theorem tailTrace_6287498 : CollatzResearch.WordTrace tailWord_6287498 prefixEnd_6287498 1076169529394315456286443 := by
  unfold tailWord_6287498
  simp only [CollatzResearch.WordTrace]
  refine ⟨57330972943869010003099787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152882594516984026674932765 57330972943869010003099787)
  ·
    refine ⟨85996459415803515004649681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57330972943869010003099787 85996459415803515004649681)
    ·
      refine ⟨64497344561852636253487261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85996459415803515004649681 64497344561852636253487261)
      ·
        refine ⟨24186504210694738595057723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64497344561852636253487261 24186504210694738595057723)
        ·
          refine ⟨36279756316042107892586585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24186504210694738595057723 36279756316042107892586585)
          ·
            refine ⟨27209817237031580919439939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36279756316042107892586585 27209817237031580919439939)
            ·
              refine ⟨40814725855547371379159909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27209817237031580919439939 40814725855547371379159909)
              ·
                refine ⟨7652761097915132133592483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40814725855547371379159909 7652761097915132133592483)
                ·
                  refine ⟨11479141646872698200388725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7652761097915132133592483 11479141646872698200388725)
                  ·
                    refine ⟨1076169529394315456286443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11479141646872698200388725 1076169529394315456286443)
                    ·
                      rfl

theorem cell23_6287498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_6287498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287498 prefixEnd_6287498 := by exact prefixLift 6287498
  have htrace : WordTrace (prefixWord ++ tailWord_6287498) baseStart_6287498 baseEnd_6287498 := by
    simpa [prefixWord, tailWord_6287498, baseEnd_6287498] using wordTrace_append hprefix tailTrace_6287498
  have hstable : (prefixWord ++ tailWord_6287498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287498).length < 2 ^ (prefixWord ++ tailWord_6287498).sum := by decide
  have hdescent : baseEnd_6287498 < baseStart_6287498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287522 : List Nat := [3, 3, 1, 3, 1, 2, 1, 2, 2, 3, 2]
def baseStart_6287522 : Nat := 118140960795 + 6287522 * 2 ^ 59
def prefixEnd_6287522 : Nat := 4983230072969 + 3 ^ 40 * 6287522 * 2
def baseEnd_6287522 : Nat := 3228520911718654274959219

theorem tailTrace_6287522 : CollatzResearch.WordTrace tailWord_6287522 prefixEnd_6287522 3228520911718654274959219 := by
  unfold tailWord_6287522
  simp only [CollatzResearch.WordTrace]
  refine ⟨57331191781847273027818205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152883178084926061407515213 57331191781847273027818205)
  ·
    refine ⟨21499196918192727385431827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57331191781847273027818205 21499196918192727385431827)
    ·
      refine ⟨32248795377289091078147741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21499196918192727385431827 32248795377289091078147741)
      ·
        refine ⟨12093298266483409154305403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32248795377289091078147741 12093298266483409154305403)
        ·
          refine ⟨18139947399725113731458105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12093298266483409154305403 18139947399725113731458105)
          ·
            refine ⟨13604960549793835298593579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18139947399725113731458105 13604960549793835298593579)
            ·
              refine ⟨20407440824690752947890369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13604960549793835298593579 20407440824690752947890369)
              ·
                refine ⟨15305580618518064710917777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20407440824690752947890369 15305580618518064710917777)
                ·
                  refine ⟨11479185463888548533188333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15305580618518064710917777 11479185463888548533188333)
                  ·
                    refine ⟨4304694548958205699945625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11479185463888548533188333 4304694548958205699945625)
                    ·
                      refine ⟨3228520911718654274959219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4304694548958205699945625 3228520911718654274959219)
                      ·
                        rfl

theorem cell23_6287522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_6287522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287522 prefixEnd_6287522 := by exact prefixLift 6287522
  have htrace : WordTrace (prefixWord ++ tailWord_6287522) baseStart_6287522 baseEnd_6287522 := by
    simpa [prefixWord, tailWord_6287522, baseEnd_6287522] using wordTrace_append hprefix tailTrace_6287522
  have hstable : (prefixWord ++ tailWord_6287522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287522).length < 2 ^ (prefixWord ++ tailWord_6287522).sum := by decide
  have hdescent : baseEnd_6287522 < baseStart_6287522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287538 : List Nat := [3, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3]
def baseStart_6287538 : Nat := 118140960795 + 6287538 * 2 ^ 59
def prefixEnd_6287538 : Nat := 4983230072969 + 3 ^ 40 * 6287538 * 2
def baseEnd_6287538 : Nat := 3228529127409126212359145

theorem tailTrace_6287538 : CollatzResearch.WordTrace tailWord_6287538 prefixEnd_6287538 3228529127409126212359145 := by
  unfold tailWord_6287538
  simp only [CollatzResearch.WordTrace]
  refine ⟨57331337673832781710963817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152883567130220751229236845 57331337673832781710963817)
  ·
    refine ⟨42998503255374586283222863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57331337673832781710963817 42998503255374586283222863)
    ·
      refine ⟨64497754883061879424834295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42998503255374586283222863 64497754883061879424834295)
      ·
        refine ⟨96746632324592819137251443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64497754883061879424834295 96746632324592819137251443)
        ·
          refine ⟨145119948486889228705877165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96746632324592819137251443 145119948486889228705877165)
          ·
            refine ⟨54419980682583460764703937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145119948486889228705877165 54419980682583460764703937)
            ·
              refine ⟨40814985511937595573527953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54419980682583460764703937 40814985511937595573527953)
              ·
                refine ⟨30611239133953196680145965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40814985511937595573527953 30611239133953196680145965)
                ·
                  refine ⟨11479214675232448755054737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30611239133953196680145965 11479214675232448755054737)
                  ·
                    refine ⟨8609411006424336566291053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11479214675232448755054737 8609411006424336566291053)
                    ·
                      refine ⟨3228529127409126212359145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8609411006424336566291053 3228529127409126212359145)
                      ·
                        rfl

theorem cell23_6287538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_6287538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287538 prefixEnd_6287538 := by exact prefixLift 6287538
  have htrace : WordTrace (prefixWord ++ tailWord_6287538) baseStart_6287538 baseEnd_6287538 := by
    simpa [prefixWord, tailWord_6287538, baseEnd_6287538] using wordTrace_append hprefix tailTrace_6287538
  have hstable : (prefixWord ++ tailWord_6287538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287538).length < 2 ^ (prefixWord ++ tailWord_6287538).sum := by decide
  have hdescent : baseEnd_6287538 < baseStart_6287538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287580 : List Nat := [2, 2, 5, 2, 2, 1, 2, 2, 1, 1, 3]
def baseStart_6287580 : Nat := 118140960795 + 6287580 * 2 ^ 59
def prefixEnd_6287580 : Nat := 4983230072969 + 3 ^ 40 * 6287580 * 2
def baseEnd_6287580 : Nat := 3228550693596615048033953

theorem tailTrace_6287580 : CollatzResearch.WordTrace tailWord_6287580 prefixEnd_6287580 3228550693596615048033953 := by
  unfold tailWord_6287580
  simp only [CollatzResearch.WordTrace]
  refine ⟨114663441280589484008442097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152884588374119312011256129 114663441280589484008442097)
  ·
    refine ⟨85997580960442113006331573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114663441280589484008442097 85997580960442113006331573)
    ·
      refine ⟨8062273215041448094343585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85997580960442113006331573 8062273215041448094343585)
      ·
        refine ⟨6046704911281086070757689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8062273215041448094343585 6046704911281086070757689)
        ·
          refine ⟨4535028683460814553068267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6046704911281086070757689 4535028683460814553068267)
          ·
            refine ⟨6802543025191221829602401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4535028683460814553068267 6802543025191221829602401)
            ·
              refine ⟨5101907268893416372201801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6802543025191221829602401 5101907268893416372201801)
              ·
                refine ⟨3826430451670062279151351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5101907268893416372201801 3826430451670062279151351)
                ·
                  refine ⟨5739645677505093418727027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3826430451670062279151351 5739645677505093418727027)
                  ·
                    refine ⟨8609468516257640128090541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5739645677505093418727027 8609468516257640128090541)
                    ·
                      refine ⟨3228550693596615048033953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8609468516257640128090541 3228550693596615048033953)
                      ·
                        rfl

theorem cell23_6287580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_6287580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287580 prefixEnd_6287580 := by exact prefixLift 6287580
  have htrace : WordTrace (prefixWord ++ tailWord_6287580) baseStart_6287580 baseEnd_6287580 := by
    simpa [prefixWord, tailWord_6287580, baseEnd_6287580] using wordTrace_append hprefix tailTrace_6287580
  have hstable : (prefixWord ++ tailWord_6287580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287580).length < 2 ^ (prefixWord ++ tailWord_6287580).sum := by decide
  have hdescent : baseEnd_6287580 < baseStart_6287580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287601 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 1, 8]
def baseStart_6287601 : Nat := 118140960795 + 6287601 * 2 ^ 59
def prefixEnd_6287601 : Nat := 4983230072969 + 3 ^ 40 * 6287601 * 2
def baseEnd_6287601 : Nat := 1076187158896786488623785

theorem tailTrace_6287601 : CollatzResearch.WordTrace tailWord_6287601 prefixEnd_6287601 1076187158896786488623785 := by
  unfold tailWord_6287601
  simp only [CollatzResearch.WordTrace]
  refine ⟨229327648494102888603398657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152885098996068592402265771 229327648494102888603398657)
  ·
    refine ⟨171995736370577166452548993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229327648494102888603398657 171995736370577166452548993)
    ·
      refine ⟨128996802277932874839411745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171995736370577166452548993 128996802277932874839411745)
      ·
        refine ⟨96747601708449656129558809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128996802277932874839411745 96747601708449656129558809)
        ·
          refine ⟨72560701281337242097169107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96747601708449656129558809 72560701281337242097169107)
          ·
            refine ⟨108841051922005863145753661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72560701281337242097169107 108841051922005863145753661)
            ·
              refine ⟨40815394470752198679657623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108841051922005863145753661 40815394470752198679657623)
              ·
                refine ⟨61223091706128298019486435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40815394470752198679657623 61223091706128298019486435)
                ·
                  refine ⟨91834637559192447029229653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61223091706128298019486435 91834637559192447029229653)
                  ·
                    refine ⟨1076187158896786488623785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 91834637559192447029229653 1076187158896786488623785)
                    ·
                      rfl

theorem cell23_6287601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 8].length) (baseStart_6287601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287601 prefixEnd_6287601 := by exact prefixLift 6287601
  have htrace : WordTrace (prefixWord ++ tailWord_6287601) baseStart_6287601 baseEnd_6287601 := by
    simpa [prefixWord, tailWord_6287601, baseEnd_6287601] using wordTrace_append hprefix tailTrace_6287601
  have hstable : (prefixWord ++ tailWord_6287601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287601).length < 2 ^ (prefixWord ++ tailWord_6287601).sum := by decide
  have hdescent : baseEnd_6287601 < baseStart_6287601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287602 : List Nat := [3, 2, 1, 3, 2, 1, 2, 3, 2, 1, 3]
def baseStart_6287602 : Nat := 118140960795 + 6287602 * 2 ^ 59
def prefixEnd_6287602 : Nat := 4983230072969 + 3 ^ 40 * 6287602 * 2
def baseEnd_6287602 : Nat := 3228561990171013961958851

theorem tailTrace_6287602 : CollatzResearch.WordTrace tailWord_6287602 prefixEnd_6287602 3228561990171013961958851 := by
  unfold tailWord_6287602
  simp only [CollatzResearch.WordTrace]
  refine ⟨57331921241774816443546265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152885123311399510516123373 57331921241774816443546265)
  ·
    refine ⟨42998940931331112332659699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57331921241774816443546265 42998940931331112332659699)
    ·
      refine ⟨64498411396996668498989549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42998940931331112332659699 64498411396996668498989549)
      ·
        refine ⟨24186904273873750687121081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64498411396996668498989549 24186904273873750687121081)
        ·
          refine ⟨18140178205405313015340811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24186904273873750687121081 18140178205405313015340811)
          ·
            refine ⟨27210267308107969523011217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18140178205405313015340811 27210267308107969523011217)
            ·
              refine ⟨20407700481080977142258413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27210267308107969523011217 20407700481080977142258413)
              ·
                refine ⟨7652887680405366428346905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20407700481080977142258413 7652887680405366428346905)
                ·
                  refine ⟨5739665760304024821260179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7652887680405366428346905 5739665760304024821260179)
                  ·
                    refine ⟨8609498640456037231890269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5739665760304024821260179 8609498640456037231890269)
                    ·
                      refine ⟨3228561990171013961958851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8609498640456037231890269 3228561990171013961958851)
                      ·
                        rfl

theorem cell23_6287602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_6287602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287602 prefixEnd_6287602 := by exact prefixLift 6287602
  have htrace : WordTrace (prefixWord ++ tailWord_6287602) baseStart_6287602 baseEnd_6287602 := by
    simpa [prefixWord, tailWord_6287602, baseEnd_6287602] using wordTrace_append hprefix tailTrace_6287602
  have hstable : (prefixWord ++ tailWord_6287602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287602).length < 2 ^ (prefixWord ++ tailWord_6287602).sum := by decide
  have hdescent : baseEnd_6287602 < baseStart_6287602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287625 : List Nat := [1, 2, 1, 1, 3, 4, 2, 2, 1, 4, 2]
def baseStart_6287625 : Nat := 118140960795 + 6287625 * 2 ^ 59
def prefixEnd_6287625 : Nat := 4983230072969 + 3 ^ 40 * 6287625 * 2
def baseEnd_6287625 : Nat := 3228573800226067371971245

theorem tailTrace_6287625 : CollatzResearch.WordTrace tailWord_6287625 prefixEnd_6287625 3228573800226067371971245 := by
  unfold tailWord_6287625
  simp only [CollatzResearch.WordTrace]
  refine ⟨229328523846015940702272329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152885682564010627134848219 229328523846015940702272329)
  ·
    refine ⟨171996392884511955526704247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229328523846015940702272329 171996392884511955526704247)
    ·
      refine ⟨257994589326767933290056371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171996392884511955526704247 257994589326767933290056371)
      ·
        refine ⟨386991883990151899935084557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257994589326767933290056371 386991883990151899935084557)
        ·
          refine ⟨145121956496306962475656709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 386991883990151899935084557 145121956496306962475656709)
          ·
            refine ⟨27210366843057555464185633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145121956496306962475656709 27210366843057555464185633)
            ·
              refine ⟨20407775132293166598139225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27210366843057555464185633 20407775132293166598139225)
              ·
                refine ⟨15305831349219874948604419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20407775132293166598139225 15305831349219874948604419)
                ·
                  refine ⟨22958747023829812422906629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15305831349219874948604419 22958747023829812422906629)
                  ·
                    refine ⟨4304765066968089829294993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22958747023829812422906629 4304765066968089829294993)
                    ·
                      refine ⟨3228573800226067371971245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4304765066968089829294993 3228573800226067371971245)
                      ·
                        rfl

theorem cell23_6287625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 4, 2].length) (baseStart_6287625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287625 prefixEnd_6287625 := by exact prefixLift 6287625
  have htrace : WordTrace (prefixWord ++ tailWord_6287625) baseStart_6287625 baseEnd_6287625 := by
    simpa [prefixWord, tailWord_6287625, baseEnd_6287625] using wordTrace_append hprefix tailTrace_6287625
  have hstable : (prefixWord ++ tailWord_6287625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287625).length < 2 ^ (prefixWord ++ tailWord_6287625).sum := by decide
  have hdescent : baseEnd_6287625 < baseStart_6287625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287648 : List Nat := [2, 1, 1, 5, 2, 1, 1, 3, 7]
def baseStart_6287648 : Nat := 118140960795 + 6287648 * 2 ^ 59
def prefixEnd_6287648 : Nat := 4983230072969 + 3 ^ 40 * 6287648 * 2
def baseEnd_6287648 : Nat := 358731734475680086887071

theorem tailTrace_6287648 : CollatzResearch.WordTrace tailWord_6287648 prefixEnd_6287648 358731734475680086887071 := by
  unfold tailWord_6287648
  simp only [CollatzResearch.WordTrace]
  refine ⟨114664681362466307815179799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152886241816621743753573065 114664681362466307815179799)
  ·
    refine ⟨171997022043699461722769699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114664681362466307815179799 171997022043699461722769699)
    ·
      refine ⟨257995533065549192584154549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171997022043699461722769699 257995533065549192584154549)
      ·
        refine ⟨24187081224895236804764489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 257995533065549192584154549 24187081224895236804764489)
        ·
          refine ⟨18140310918671427603573367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24187081224895236804764489 18140310918671427603573367)
          ·
            refine ⟨27210466378007141405360051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18140310918671427603573367 27210466378007141405360051)
            ·
              refine ⟨40815699567010712108040077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27210466378007141405360051 40815699567010712108040077)
              ·
                refine ⟨15305887337629017040515029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40815699567010712108040077 15305887337629017040515029)
                ·
                  refine ⟨358731734475680086887071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15305887337629017040515029 358731734475680086887071)
                  ·
                    rfl

theorem cell23_6287648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 7].length) (baseStart_6287648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287648 prefixEnd_6287648 := by exact prefixLift 6287648
  have htrace : WordTrace (prefixWord ++ tailWord_6287648) baseStart_6287648 baseEnd_6287648 := by
    simpa [prefixWord, tailWord_6287648, baseEnd_6287648] using wordTrace_append hprefix tailTrace_6287648
  have hstable : (prefixWord ++ tailWord_6287648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287648).length < 2 ^ (prefixWord ++ tailWord_6287648).sum := by decide
  have hdescent : baseEnd_6287648 < baseStart_6287648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287715 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 1, 6, 2]
def baseStart_6287715 : Nat := 118140960795 + 6287715 * 2 ^ 59
def prefixEnd_6287715 : Nat := 4983230072969 + 3 ^ 40 * 6287715 * 2
def baseEnd_6287715 : Nat := 3228620013484972019845831

theorem tailTrace_6287715 : CollatzResearch.WordTrace tailWord_6287715 prefixEnd_6287715 3228620013484972019845831 := by
  unfold tailWord_6287715
  simp only [CollatzResearch.WordTrace]
  refine ⟨229331806415689886073048599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152887870943793257382032399 229331806415689886073048599)
  ·
    refine ⟨343997709623534829109572899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229331806415689886073048599 343997709623534829109572899)
    ·
      refine ⟨515996564435302243664359349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343997709623534829109572899 515996564435302243664359349)
      ·
        refine ⟨48374677915809585343533689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 515996564435302243664359349 48374677915809585343533689)
        ·
          refine ⟨36281008436857189007650267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48374677915809585343533689 36281008436857189007650267)
          ·
            refine ⟨54421512655285783511475401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36281008436857189007650267 54421512655285783511475401)
            ·
              refine ⟨40816134491464337633606551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54421512655285783511475401 40816134491464337633606551)
              ·
                refine ⟨61224201737196506450409827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40816134491464337633606551 61224201737196506450409827)
                ·
                  refine ⟨91836302605794759675614741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61224201737196506450409827 91836302605794759675614741)
                  ·
                    refine ⟨4304826684646629359794441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 91836302605794759675614741 4304826684646629359794441)
                    ·
                      refine ⟨3228620013484972019845831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4304826684646629359794441 3228620013484972019845831)
                      ·
                        rfl

theorem cell23_6287715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_6287715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287715 prefixEnd_6287715 := by exact prefixLift 6287715
  have htrace : WordTrace (prefixWord ++ tailWord_6287715) baseStart_6287715 baseEnd_6287715 := by
    simpa [prefixWord, tailWord_6287715, baseEnd_6287715] using wordTrace_append hprefix tailTrace_6287715
  have hstable : (prefixWord ++ tailWord_6287715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287715).length < 2 ^ (prefixWord ++ tailWord_6287715).sum := by decide
  have hdescent : baseEnd_6287715 < baseStart_6287715 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287725 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 5, 4]
def baseStart_6287725 : Nat := 118140960795 + 6287725 * 2 ^ 59
def prefixEnd_6287725 : Nat := 4983230072969 + 3 ^ 40 * 6287725 * 2
def baseEnd_6287725 : Nat := 1076208382763838993573595

theorem tailTrace_6287725 : CollatzResearch.WordTrace tailWord_6287725 prefixEnd_6287725 1076208382763838993573595 := by
  unfold tailWord_6287725
  simp only [CollatzResearch.WordTrace]
  refine ⟨229332171145653657780912629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152888114097102438520608419 229332171145653657780912629)
  ·
    refine ⟨21499891044905030416960559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 229332171145653657780912629 21499891044905030416960559)
    ·
      refine ⟨32249836567357545625440839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21499891044905030416960559 32249836567357545625440839)
      ·
        refine ⟨48374754851036318438161259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32249836567357545625440839 48374754851036318438161259)
        ·
          refine ⟨72562132276554477657241889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48374754851036318438161259 72562132276554477657241889)
          ·
            refine ⟨54421599207415858242931417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72562132276554477657241889 54421599207415858242931417)
            ·
              refine ⟨40816199405561893682198563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54421599207415858242931417 40816199405561893682198563)
              ·
                refine ⟨61224299108342840523297845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40816199405561893682198563 61224299108342840523297845)
                ·
                  refine ⟨5739778041407141299059173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61224299108342840523297845 5739778041407141299059173)
                  ·
                    refine ⟨1076208382763838993573595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5739778041407141299059173 1076208382763838993573595)
                    ·
                      rfl

theorem cell23_6287725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_6287725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287725 prefixEnd_6287725 := by exact prefixLift 6287725
  have htrace : WordTrace (prefixWord ++ tailWord_6287725) baseStart_6287725 baseEnd_6287725 := by
    simpa [prefixWord, tailWord_6287725, baseEnd_6287725] using wordTrace_append hprefix tailTrace_6287725
  have hstable : (prefixWord ++ tailWord_6287725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287725).length < 2 ^ (prefixWord ++ tailWord_6287725).sum := by decide
  have hdescent : baseEnd_6287725 < baseStart_6287725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287755 : List Nat := [1, 1, 1, 1, 4, 5, 2, 2, 6]
def baseStart_6287755 : Nat := 118140960795 + 6287755 * 2 ^ 59
def prefixEnd_6287755 : Nat := 4983230072969 + 3 ^ 40 * 6287755 * 2
def baseEnd_6287755 : Nat := 358737839190127984816183

theorem tailTrace_6287755 : CollatzResearch.WordTrace tailWord_6287755 prefixEnd_6287755 358737839190127984816183 := by
  unfold tailWord_6287755
  simp only [CollatzResearch.WordTrace]
  refine ⟨229333265335544972904504719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152888843557029981936336479 229333265335544972904504719)
  ·
    refine ⟨343999898003317459356757079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229333265335544972904504719 343999898003317459356757079)
    ·
      refine ⟨515999847004976189035135619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343999898003317459356757079 515999847004976189035135619)
      ·
        refine ⟨773999770507464283552703429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515999847004976189035135619 773999770507464283552703429)
        ·
          refine ⟨145124956970149553166131893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 773999770507464283552703429 145124956970149553166131893)
          ·
            refine ⟨13605464715951520609324865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 145124956970149553166131893 13605464715951520609324865)
            ·
              refine ⟨10204098536963640456993649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13605464715951520609324865 10204098536963640456993649)
              ·
                refine ⟨7653073902722730342745237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10204098536963640456993649 7653073902722730342745237)
                ·
                  refine ⟨358737839190127984816183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7653073902722730342745237 358737839190127984816183)
                  ·
                    rfl

theorem cell23_6287755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 6].length) (baseStart_6287755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287755 prefixEnd_6287755 := by exact prefixLift 6287755
  have htrace : WordTrace (prefixWord ++ tailWord_6287755) baseStart_6287755 baseEnd_6287755 := by
    simpa [prefixWord, tailWord_6287755, baseEnd_6287755] using wordTrace_append hprefix tailTrace_6287755
  have hstable : (prefixWord ++ tailWord_6287755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287755).length < 2 ^ (prefixWord ++ tailWord_6287755).sum := by decide
  have hdescent : baseEnd_6287755 < baseStart_6287755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287786 : List Nat := [3, 1, 6, 1, 1, 1, 1, 1, 1, 4, 3]
def baseStart_6287786 : Nat := 118140960795 + 6287786 * 2 ^ 59
def prefixEnd_6287786 : Nat := 4983230072969 + 3 ^ 40 * 6287786 * 2
def baseEnd_6287786 : Nat := 3228656470611441242058005

theorem tailTrace_6287786 : CollatzResearch.WordTrace tailWord_6287786 prefixEnd_6287786 3228656470611441242058005 := by
  unfold tailWord_6287786
  simp only [CollatzResearch.WordTrace]
  refine ⟨57333598999608166299720803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152889597332288443465922141 57333598999608166299720803)
  ·
    refine ⟨86000398499412249449581205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57333598999608166299720803 86000398499412249449581205)
    ·
      refine ⟨4031268679659949192949119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86000398499412249449581205 4031268679659949192949119)
      ·
        refine ⟨6046903019489923789423679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4031268679659949192949119 6046903019489923789423679)
        ·
          refine ⟨9070354529234885684135519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6046903019489923789423679 9070354529234885684135519)
          ·
            refine ⟨13605531793852328526203279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9070354529234885684135519 13605531793852328526203279)
            ·
              refine ⟨20408297690778492789304919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13605531793852328526203279 20408297690778492789304919)
              ·
                refine ⟨30612446536167739183957379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20408297690778492789304919 30612446536167739183957379)
                ·
                  refine ⟨45918669804251608775936069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30612446536167739183957379 45918669804251608775936069)
                  ·
                    refine ⟨8609750588297176645488013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45918669804251608775936069 8609750588297176645488013)
                    ·
                      refine ⟨3228656470611441242058005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8609750588297176645488013 3228656470611441242058005)
                      ·
                        rfl

theorem cell23_6287786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_6287786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287786 prefixEnd_6287786 := by exact prefixLift 6287786
  have htrace : WordTrace (prefixWord ++ tailWord_6287786) baseStart_6287786 baseEnd_6287786 := by
    simpa [prefixWord, tailWord_6287786, baseEnd_6287786] using wordTrace_append hprefix tailTrace_6287786
  have hstable : (prefixWord ++ tailWord_6287786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287786).length < 2 ^ (prefixWord ++ tailWord_6287786).sum := by decide
  have hdescent : baseEnd_6287786 < baseStart_6287786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287799 : List Nat := [1, 1, 3, 1, 3, 3, 1, 5, 1, 1, 3]
def baseStart_6287799 : Nat := 118140960795 + 6287799 * 2 ^ 59
def prefixEnd_6287799 : Nat := 4983230072969 + 3 ^ 40 * 6287799 * 2
def baseEnd_6287799 : Nat := 3228663145859949691195445

theorem tailTrace_6287799 : CollatzResearch.WordTrace tailWord_6287799 prefixEnd_6287799 3228663145859949691195445 := by
  unfold tailWord_6287799
  simp only [CollatzResearch.WordTrace]
  refine ⟨229334870147385568419106451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152889913431590378946070967 229334870147385568419106451)
  ·
    refine ⟨344002305221078352628659677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229334870147385568419106451 344002305221078352628659677)
    ·
      refine ⟨129000864457904382235747379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344002305221078352628659677 129000864457904382235747379)
      ·
        refine ⟨193501296686856573353621069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129000864457904382235747379 193501296686856573353621069)
        ·
          refine ⟨72562986257571215007607901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193501296686856573353621069 72562986257571215007607901)
          ·
            refine ⟨27211119846589205627852963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72562986257571215007607901 27211119846589205627852963)
            ·
              refine ⟨40816679769883808441779445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27211119846589205627852963 40816679769883808441779445)
              ·
                refine ⟨3826563728426607041416823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40816679769883808441779445 3826563728426607041416823)
                ·
                  refine ⟨5739845592639910562125235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3826563728426607041416823 5739845592639910562125235)
                  ·
                    refine ⟨8609768388959865843187853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5739845592639910562125235 8609768388959865843187853)
                    ·
                      refine ⟨3228663145859949691195445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8609768388959865843187853 3228663145859949691195445)
                      ·
                        rfl

theorem cell23_6287799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 5, 1, 1, 3].length) (baseStart_6287799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287799 prefixEnd_6287799 := by exact prefixLift 6287799
  have htrace : WordTrace (prefixWord ++ tailWord_6287799) baseStart_6287799 baseEnd_6287799 := by
    simpa [prefixWord, tailWord_6287799, baseEnd_6287799] using wordTrace_append hprefix tailTrace_6287799
  have hstable : (prefixWord ++ tailWord_6287799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287799).length < 2 ^ (prefixWord ++ tailWord_6287799).sum := by decide
  have hdescent : baseEnd_6287799 < baseStart_6287799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287825 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 5, 2, 3]
def baseStart_6287825 : Nat := 118140960795 + 6287825 * 2 ^ 59
def prefixEnd_6287825 : Nat := 4983230072969 + 3 ^ 40 * 6287825 * 2
def baseEnd_6287825 : Nat := 3228676496356966589470325

theorem tailTrace_6287825 : CollatzResearch.WordTrace tailWord_6287825 prefixEnd_6287825 3228676496356966589470325 := by
  unfold tailWord_6287825
  simp only [CollatzResearch.WordTrace]
  refine ⟨229335818445291374859552929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152890545630194249906368619 229335818445291374859552929)
  ·
    refine ⟨172001863833968531144664697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229335818445291374859552929 172001863833968531144664697)
    ·
      refine ⟨129001397875476398358498523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172001863833968531144664697 129001397875476398358498523)
      ·
        refine ⟨193502096813214597537747785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129001397875476398358498523 193502096813214597537747785)
        ·
          refine ⟨145126572609910948153310839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193502096813214597537747785 145126572609910948153310839)
          ·
            refine ⟨217689858914866422229966259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145126572609910948153310839 217689858914866422229966259)
            ·
              refine ⟨326534788372299633344949389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217689858914866422229966259 326534788372299633344949389)
              ·
                refine ⟨122450545639612362504356021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 326534788372299633344949389 122450545639612362504356021)
                ·
                  refine ⟨11479738653713658984783377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122450545639612362504356021 11479738653713658984783377)
                  ·
                    refine ⟨8609803990285244238587533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11479738653713658984783377 8609803990285244238587533)
                    ·
                      refine ⟨3228676496356966589470325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8609803990285244238587533 3228676496356966589470325)
                      ·
                        rfl

theorem cell23_6287825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 2, 3].length) (baseStart_6287825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287825 prefixEnd_6287825 := by exact prefixLift 6287825
  have htrace : WordTrace (prefixWord ++ tailWord_6287825) baseStart_6287825 baseEnd_6287825 := by
    simpa [prefixWord, tailWord_6287825, baseEnd_6287825] using wordTrace_append hprefix tailTrace_6287825
  have hstable : (prefixWord ++ tailWord_6287825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287825).length < 2 ^ (prefixWord ++ tailWord_6287825).sum := by decide
  have hdescent : baseEnd_6287825 < baseStart_6287825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287839 : List Nat := [1, 1, 2, 3, 3, 2, 2, 2, 3, 2, 2]
def baseStart_6287839 : Nat := 118140960795 + 6287839 * 2 ^ 59
def prefixEnd_6287839 : Nat := 4983230072969 + 3 ^ 40 * 6287839 * 2
def baseEnd_6287839 : Nat := 3228683685086129534695261

theorem tailTrace_6287839 : CollatzResearch.WordTrace tailWord_6287839 prefixEnd_6287839 3228683685086129534695261 := by
  unfold tailWord_6287839
  simp only [CollatzResearch.WordTrace]
  refine ⟨229336329067240655250562571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152890886044827103500375047 229336329067240655250562571)
  ·
    refine ⟨344004493600860982875843857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229336329067240655250562571 344004493600860982875843857)
    ·
      refine ⟨258003370200645737156882893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344004493600860982875843857 258003370200645737156882893)
      ·
        refine ⟨96751263825242151433831085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258003370200645737156882893 96751263825242151433831085)
        ·
          refine ⟨36281723934465806787686657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96751263825242151433831085 36281723934465806787686657)
          ·
            refine ⟨27211292950849355090764993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36281723934465806787686657 27211292950849355090764993)
            ·
              refine ⟨20408469713137016318073745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27211292950849355090764993 20408469713137016318073745)
              ·
                refine ⟨15306352284852762238555309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20408469713137016318073745 15306352284852762238555309)
                ·
                  refine ⟨5739882106819785839458241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15306352284852762238555309 5739882106819785839458241)
                  ·
                    refine ⟨4304911580114839379593681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5739882106819785839458241 4304911580114839379593681)
                    ·
                      refine ⟨3228683685086129534695261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4304911580114839379593681 3228683685086129534695261)
                      ·
                        rfl

theorem cell23_6287839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 3, 2, 2].length) (baseStart_6287839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287839 prefixEnd_6287839 := by exact prefixLift 6287839
  have htrace : WordTrace (prefixWord ++ tailWord_6287839) baseStart_6287839 baseEnd_6287839 := by
    simpa [prefixWord, tailWord_6287839, baseEnd_6287839] using wordTrace_append hprefix tailTrace_6287839
  have hstable : (prefixWord ++ tailWord_6287839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287839).length < 2 ^ (prefixWord ++ tailWord_6287839).sum := by decide
  have hdescent : baseEnd_6287839 < baseStart_6287839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287855 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 3, 3, 3]
def baseStart_6287855 : Nat := 118140960795 + 6287855 * 2 ^ 59
def prefixEnd_6287855 : Nat := 4983230072969 + 3 ^ 40 * 6287855 * 2
def baseEnd_6287855 : Nat := 3228691900776601472095187

theorem tailTrace_6287855 : CollatzResearch.WordTrace tailWord_6287855 prefixEnd_6287855 3228691900776601472095187 := by
  unfold tailWord_6287855
  simp only [CollatzResearch.WordTrace]
  refine ⟨229336912635182689983145019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152891275090121793322096679 229336912635182689983145019)
  ·
    refine ⟨344005368952774034974717529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229336912635182689983145019 344005368952774034974717529)
    ·
      refine ⟨258004026714580526231038147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344005368952774034974717529 258004026714580526231038147)
      ·
        refine ⟨387006040071870789346557221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258004026714580526231038147 387006040071870789346557221)
        ·
          refine ⟨72563632513475773002479479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 387006040071870789346557221 72563632513475773002479479)
          ·
            refine ⟨108845448770213659503719219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72563632513475773002479479 108845448770213659503719219)
            ·
              refine ⟨163268173155320489255578829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108845448770213659503719219 163268173155320489255578829)
              ·
                refine ⟨61225564933245183470842061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163268173155320489255578829 61225564933245183470842061)
                ·
                  refine ⟨22959586849966943801565773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61225564933245183470842061 22959586849966943801565773)
                  ·
                    refine ⟨8609845068737603925587165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22959586849966943801565773 8609845068737603925587165)
                    ·
                      refine ⟨3228691900776601472095187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8609845068737603925587165 3228691900776601472095187)
                      ·
                        rfl

theorem cell23_6287855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 3, 3].length) (baseStart_6287855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287855 prefixEnd_6287855 := by exact prefixLift 6287855
  have htrace : WordTrace (prefixWord ++ tailWord_6287855) baseStart_6287855 baseEnd_6287855 := by
    simpa [prefixWord, tailWord_6287855, baseEnd_6287855] using wordTrace_append hprefix tailTrace_6287855
  have hstable : (prefixWord ++ tailWord_6287855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287855).length < 2 ^ (prefixWord ++ tailWord_6287855).sum := by decide
  have hdescent : baseEnd_6287855 < baseStart_6287855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287915 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 4, 4, 3]
def baseStart_6287915 : Nat := 118140960795 + 6287915 * 2 ^ 59
def prefixEnd_6287915 : Nat := 4983230072969 + 3 ^ 40 * 6287915 * 2
def baseEnd_6287915 : Nat := 3228722709615871237344911

theorem tailTrace_6287915 : CollatzResearch.WordTrace tailWord_6287915 prefixEnd_6287915 3228722709615871237344911 := by
  unfold tailWord_6287915
  simp only [CollatzResearch.WordTrace]
  refine ⟨229339101014965320230329199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152892734009976880153552799 229339101014965320230329199)
  ·
    refine ⟨344008651522447980345493799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229339101014965320230329199 344008651522447980345493799)
    ·
      refine ⟨516012977283671970518240699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344008651522447980345493799 516012977283671970518240699)
      ·
        refine ⟨774019465925507955777361049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516012977283671970518240699 774019465925507955777361049)
        ·
          refine ⟨580514599444130966833020787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 774019465925507955777361049 580514599444130966833020787)
          ·
            refine ⟨870771899166196450249531181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580514599444130966833020787 870771899166196450249531181)
            ·
              refine ⟨326539462187323668843574193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 870771899166196450249531181 326539462187323668843574193)
              ·
                refine ⟨244904596640492751632680645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326539462187323668843574193 244904596640492751632680645)
                ·
                  refine ⟨45919611870092390931127621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 244904596640492751632680645 45919611870092390931127621)
                  ·
                    refine ⟨8609927225642323299586429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45919611870092390931127621 8609927225642323299586429)
                    ·
                      refine ⟨3228722709615871237344911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8609927225642323299586429 3228722709615871237344911)
                      ·
                        rfl

theorem cell23_6287915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 4, 3].length) (baseStart_6287915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287915 prefixEnd_6287915 := by exact prefixLift 6287915
  have htrace : WordTrace (prefixWord ++ tailWord_6287915) baseStart_6287915 baseEnd_6287915 := by
    simpa [prefixWord, tailWord_6287915, baseEnd_6287915] using wordTrace_append hprefix tailTrace_6287915
  have hstable : (prefixWord ++ tailWord_6287915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287915).length < 2 ^ (prefixWord ++ tailWord_6287915).sum := by decide
  have hdescent : baseEnd_6287915 < baseStart_6287915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287924 : List Nat := [2, 5, 1, 3, 1, 2, 2, 2, 1, 2, 2]
def baseStart_6287924 : Nat := 118140960795 + 6287924 * 2 ^ 59
def prefixEnd_6287924 : Nat := 4983230072969 + 3 ^ 40 * 6287924 * 2
def baseEnd_6287924 : Nat := 3228727330941761702132371

theorem tailTrace_6287924 : CollatzResearch.WordTrace tailWord_6287924 prefixEnd_6287924 3228727330941761702132371 := by
  unfold tailWord_6287924
  simp only [CollatzResearch.WordTrace]
  refine ⟨114669714635966357383703413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152892952847955143178271217 114669714635966357383703413)
  ·
    refine ⟨10750285747121846004722195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114669714635966357383703413 10750285747121846004722195)
    ·
      refine ⟨16125428620682769007083293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10750285747121846004722195 16125428620682769007083293)
      ·
        refine ⟨6047035732756038377656235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16125428620682769007083293 6047035732756038377656235)
        ·
          refine ⟨9070553599134057566484353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6047035732756038377656235 9070553599134057566484353)
          ·
            refine ⟨6802915199350543174863265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9070553599134057566484353 6802915199350543174863265)
            ·
              refine ⟨5102186399512907381147449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6802915199350543174863265 5102186399512907381147449)
              ·
                refine ⟨3826639799634680535860587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5102186399512907381147449 3826639799634680535860587)
                ·
                  refine ⟨5739959699452020803790881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3826639799634680535860587 5739959699452020803790881)
                  ·
                    refine ⟨4304969774589015602843161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5739959699452020803790881 4304969774589015602843161)
                    ·
                      refine ⟨3228727330941761702132371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4304969774589015602843161 3228727330941761702132371)
                      ·
                        rfl

theorem cell23_6287924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_6287924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287924 prefixEnd_6287924 := by exact prefixLift 6287924
  have htrace : WordTrace (prefixWord ++ tailWord_6287924) baseStart_6287924 baseEnd_6287924 := by
    simpa [prefixWord, tailWord_6287924, baseEnd_6287924] using wordTrace_append hprefix tailTrace_6287924
  have hstable : (prefixWord ++ tailWord_6287924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287924).length < 2 ^ (prefixWord ++ tailWord_6287924).sum := by decide
  have hdescent : baseEnd_6287924 < baseStart_6287924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287932 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 2, 4, 3]
def baseStart_6287932 : Nat := 118140960795 + 6287932 * 2 ^ 59
def prefixEnd_6287932 : Nat := 4983230072969 + 3 ^ 40 * 6287932 * 2
def baseEnd_6287932 : Nat := 3228731438786997670832333

theorem tailTrace_6287932 : CollatzResearch.WordTrace tailWord_6287932 prefixEnd_6287932 3228731438786997670832333 := by
  unfold tailWord_6287932
  simp only [CollatzResearch.WordTrace]
  refine ⟨114669860527951866066849025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152893147370602488089132033 114669860527951866066849025)
  ·
    refine ⟨86002395395963899550136769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114669860527951866066849025 86002395395963899550136769)
    ·
      refine ⟨64501796546972924662602577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86002395395963899550136769 64501796546972924662602577)
      ·
        refine ⟨48376347410229693496951933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64501796546972924662602577 48376347410229693496951933)
        ·
          refine ⟨18141130278836135061356975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48376347410229693496951933 18141130278836135061356975)
          ·
            refine ⟨27211695418254202592035463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18141130278836135061356975 27211695418254202592035463)
            ·
              refine ⟨40817543127381303888053195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27211695418254202592035463 40817543127381303888053195)
              ·
                refine ⟨61226314691071955832079793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40817543127381303888053195 61226314691071955832079793)
                ·
                  refine ⟨45919736018303966874059845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61226314691071955832079793 45919736018303966874059845)
                  ·
                    refine ⟨8609950503431993788886221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45919736018303966874059845 8609950503431993788886221)
                    ·
                      refine ⟨3228731438786997670832333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8609950503431993788886221 3228731438786997670832333)
                      ·
                        rfl

theorem cell23_6287932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_6287932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287932 prefixEnd_6287932 := by exact prefixLift 6287932
  have htrace : WordTrace (prefixWord ++ tailWord_6287932) baseStart_6287932 baseEnd_6287932 := by
    simpa [prefixWord, tailWord_6287932, baseEnd_6287932] using wordTrace_append hprefix tailTrace_6287932
  have hstable : (prefixWord ++ tailWord_6287932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287932).length < 2 ^ (prefixWord ++ tailWord_6287932).sum := by decide
  have hdescent : baseEnd_6287932 < baseStart_6287932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287935 : List Nat := [1, 1, 2, 2, 3, 2, 2, 3, 7]
def baseStart_6287935 : Nat := 118140960795 + 6287935 * 2 ^ 59
def prefixEnd_6287935 : Nat := 4983230072969 + 3 ^ 40 * 6287935 * 2
def baseEnd_6287935 : Nat := 358748108803217906566091

theorem tailTrace_6287935 : CollatzResearch.WordTrace tailWord_6287935 prefixEnd_6287935 358748108803217906566091 := by
  unfold tailWord_6287935
  simp only [CollatzResearch.WordTrace]
  refine ⟨229339830474892863646057259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152893220316595242430704839 229339830474892863646057259)
  ·
    refine ⟨344009745712339295469085889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229339830474892863646057259 344009745712339295469085889)
    ·
      refine ⟨258007309284254471601814417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344009745712339295469085889 258007309284254471601814417)
      ·
        refine ⟨193505481963190853701360813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258007309284254471601814417 193505481963190853701360813)
        ·
          refine ⟨72564555736196570138010305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193505481963190853701360813 72564555736196570138010305)
          ·
            refine ⟨54423416802147427603507729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72564555736196570138010305 54423416802147427603507729)
            ·
              refine ⟨40817562601610570702630797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54423416802147427603507729 40817562601610570702630797)
              ·
                refine ⟨15306585975603964013486549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40817562601610570702630797 15306585975603964013486549)
                ·
                  refine ⟨358748108803217906566091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15306585975603964013486549 358748108803217906566091)
                  ·
                    rfl

theorem cell23_6287935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 7].length) (baseStart_6287935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287935 prefixEnd_6287935 := by exact prefixLift 6287935
  have htrace : WordTrace (prefixWord ++ tailWord_6287935) baseStart_6287935 baseEnd_6287935 := by
    simpa [prefixWord, tailWord_6287935, baseEnd_6287935] using wordTrace_append hprefix tailTrace_6287935
  have hstable : (prefixWord ++ tailWord_6287935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287935).length < 2 ^ (prefixWord ++ tailWord_6287935).sum := by decide
  have hdescent : baseEnd_6287935 < baseStart_6287935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287946 : List Nat := [3, 1, 2, 1, 1, 4, 2, 3, 2, 2, 2]
def baseStart_6287946 : Nat := 118140960795 + 6287946 * 2 ^ 59
def prefixEnd_6287946 : Nat := 4983230072969 + 3 ^ 40 * 6287946 * 2
def baseEnd_6287946 : Nat := 3228738627516160616057269

theorem tailTrace_6287946 : CollatzResearch.WordTrace tailWord_6287946 prefixEnd_6287946 3228738627516160616057269 := by
  unfold tailWord_6287946
  simp only [CollatzResearch.WordTrace]
  refine ⟨57335057919463253131176923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152893487785235341683138461 57335057919463253131176923)
  ·
    refine ⟨86002586879194879696765385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57335057919463253131176923 86002586879194879696765385)
    ·
      refine ⟨64501940159396159772574039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86002586879194879696765385 64501940159396159772574039)
      ·
        refine ⟨96752910239094239658861059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64501940159396159772574039 96752910239094239658861059)
        ·
          refine ⟨145129365358641359488291589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96752910239094239658861059 145129365358641359488291589)
          ·
            refine ⟨27211756004745254904054673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145129365358641359488291589 27211756004745254904054673)
            ·
              refine ⟨20408817003558941178041005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27211756004745254904054673 20408817003558941178041005)
              ·
                refine ⟨7653306376334602941765377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20408817003558941178041005 7653306376334602941765377)
                ·
                  refine ⟨5739979782250952206324033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7653306376334602941765377 5739979782250952206324033)
                  ·
                    refine ⟨4304984836688214154743025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5739979782250952206324033 4304984836688214154743025)
                    ·
                      refine ⟨3228738627516160616057269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4304984836688214154743025 3228738627516160616057269)
                      ·
                        rfl

theorem cell23_6287946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 2, 2, 2].length) (baseStart_6287946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287946 prefixEnd_6287946 := by exact prefixLift 6287946
  have htrace : WordTrace (prefixWord ++ tailWord_6287946) baseStart_6287946 baseEnd_6287946 := by
    simpa [prefixWord, tailWord_6287946, baseEnd_6287946] using wordTrace_append hprefix tailTrace_6287946
  have hstable : (prefixWord ++ tailWord_6287946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287946).length < 2 ^ (prefixWord ++ tailWord_6287946).sum := by decide
  have hdescent : baseEnd_6287946 < baseStart_6287946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6287969 : List Nat := [1, 2, 3, 1, 1, 5, 2, 3, 5]
def baseStart_6287969 : Nat := 118140960795 + 6287969 * 2 ^ 59
def prefixEnd_6287969 : Nat := 4983230072969 + 3 ^ 40 * 6287969 * 2
def baseEnd_6287969 : Nat := 358750048619023780674407

theorem tailTrace_6287969 : CollatzResearch.WordTrace tailWord_6287969 prefixEnd_6287969 358750048619023780674407 := by
  unfold tailWord_6287969
  simp only [CollatzResearch.WordTrace]
  refine ⟨229341070556769687452794961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152894047037846458301863307 229341070556769687452794961)
  ·
    refine ⟨172005802917577265589596221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229341070556769687452794961 172005802917577265589596221)
    ·
      refine ⟨64502176094091474596098583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172005802917577265589596221 64502176094091474596098583)
      ·
        refine ⟨96753264141137211894147875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64502176094091474596098583 96753264141137211894147875)
        ·
          refine ⟨145129896211705817841221813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96753264141137211894147875 145129896211705817841221813)
          ·
            refine ⟨13605927769847420422614545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 145129896211705817841221813 13605927769847420422614545)
            ·
              refine ⟨10204445827385565316960909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13605927769847420422614545 10204445827385565316960909)
              ·
                refine ⟨3826667185269586993860341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10204445827385565316960909 3826667185269586993860341)
                ·
                  refine ⟨358750048619023780674407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3826667185269586993860341 358750048619023780674407)
                  ·
                    rfl

theorem cell23_6287969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 3, 5].length) (baseStart_6287969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6287969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6287969 prefixEnd_6287969 := by exact prefixLift 6287969
  have htrace : WordTrace (prefixWord ++ tailWord_6287969) baseStart_6287969 baseEnd_6287969 := by
    simpa [prefixWord, tailWord_6287969, baseEnd_6287969] using wordTrace_append hprefix tailTrace_6287969
  have hstable : (prefixWord ++ tailWord_6287969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6287969).length < 2 ^ (prefixWord ++ tailWord_6287969).sum := by decide
  have hdescent : baseEnd_6287969 < baseStart_6287969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6287969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288012 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 5, 4]
def baseStart_6288012 : Nat := 118140960795 + 6288012 * 2 ^ 59
def prefixEnd_6288012 : Nat := 4983230072969 + 3 ^ 40 * 6288012 * 2
def baseEnd_6288012 : Nat := 1076257505746452452610655

theorem tailTrace_6288012 : CollatzResearch.WordTrace tailWord_6288012 prefixEnd_6288012 1076257505746452452610655 := by
  unfold tailWord_6288012
  simp only [CollatzResearch.WordTrace]
  refine ⟨114671319447806952898305145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152895092597075937197740193 114671319447806952898305145)
  ·
    refine ⟨86003489585855214673728859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114671319447806952898305145 86003489585855214673728859)
    ·
      refine ⟨129005234378782822010593289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86003489585855214673728859 129005234378782822010593289)
      ·
        refine ⟨96753925784087116507944967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129005234378782822010593289 96753925784087116507944967)
        ·
          refine ⟨145130888676130674761917451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96753925784087116507944967 145130888676130674761917451)
          ·
            refine ⟨217696333014196012142876177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145130888676130674761917451 217696333014196012142876177)
            ·
              refine ⟨163272249760647009107157133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217696333014196012142876177 163272249760647009107157133)
              ·
                refine ⟨61227093660242628415183925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163272249760647009107157133 61227093660242628415183925)
                ·
                  refine ⟨5740040030647746413923493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61227093660242628415183925 5740040030647746413923493)
                  ·
                    refine ⟨1076257505746452452610655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5740040030647746413923493 1076257505746452452610655)
                    ·
                      rfl

theorem cell23_6288012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 5, 4].length) (baseStart_6288012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288012 prefixEnd_6288012 := by exact prefixLift 6288012
  have htrace : WordTrace (prefixWord ++ tailWord_6288012) baseStart_6288012 baseEnd_6288012 := by
    simpa [prefixWord, tailWord_6288012, baseEnd_6288012] using wordTrace_append hprefix tailTrace_6288012
  have hstable : (prefixWord ++ tailWord_6288012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288012).length < 2 ^ (prefixWord ++ tailWord_6288012).sum := by decide
  have hdescent : baseEnd_6288012 < baseStart_6288012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288015 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 6]
def baseStart_6288015 : Nat := 118140960795 + 6288015 * 2 ^ 59
def prefixEnd_6288015 : Nat := 4983230072969 + 3 ^ 40 * 6288015 * 2
def baseEnd_6288015 : Nat := 3228774057681320846094451

theorem tailTrace_6288015 : CollatzResearch.WordTrace tailWord_6288015 prefixEnd_6288015 3228774057681320846094451 := by
  unfold tailWord_6288015
  simp only [CollatzResearch.WordTrace]
  refine ⟨229342748314603037308969499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152895165543068691539312999 229342748314603037308969499)
  ·
    refine ⟨344014122471904555963454249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229342748314603037308969499 344014122471904555963454249)
    ·
      refine ⟨258010591853928416972590687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344014122471904555963454249 258010591853928416972590687)
      ·
        refine ⟨387015887780892625458886031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258010591853928416972590687 387015887780892625458886031)
        ·
          refine ⟨580523831671338938188329047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387015887780892625458886031 580523831671338938188329047)
          ·
            refine ⟨870785747507008407282493571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580523831671338938188329047 870785747507008407282493571)
            ·
              refine ⟨1306178621260512610923740357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 870785747507008407282493571 1306178621260512610923740357)
              ·
                refine ⟨244908491486346114548201317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1306178621260512610923740357 244908491486346114548201317)
                ·
                  refine ⟨45920342153689896477787747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 244908491486346114548201317 45920342153689896477787747)
                  ·
                    refine ⟨68880513230534844716681621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45920342153689896477787747 68880513230534844716681621)
                    ·
                      refine ⟨3228774057681320846094451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68880513230534844716681621 3228774057681320846094451)
                      ·
                        rfl

theorem cell23_6288015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 6].length) (baseStart_6288015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288015 prefixEnd_6288015 := by exact prefixLift 6288015
  have htrace : WordTrace (prefixWord ++ tailWord_6288015) baseStart_6288015 baseEnd_6288015 := by
    simpa [prefixWord, tailWord_6288015, baseEnd_6288015] using wordTrace_append hprefix tailTrace_6288015
  have hstable : (prefixWord ++ tailWord_6288015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288015).length < 2 ^ (prefixWord ++ tailWord_6288015).sum := by decide
  have hdescent : baseEnd_6288015 < baseStart_6288015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288025 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 10]
def baseStart_6288025 : Nat := 118140960795 + 6288025 * 2 ^ 59
def prefixEnd_6288025 : Nat := 4983230072969 + 3 ^ 40 * 6288025 * 2
def baseEnd_6288025 : Nat := 358753243609762867441045

theorem tailTrace_6288025 : CollatzResearch.WordTrace tailWord_6288025 prefixEnd_6288025 358753243609762867441045 := by
  unfold tailWord_6288025
  simp only [CollatzResearch.WordTrace]
  refine ⟨229343113044566809016833529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152895408696377872677889019 229343113044566809016833529)
  ·
    refine ⟨172007334783425106762625147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229343113044566809016833529 172007334783425106762625147)
    ·
      refine ⟨258011002175137660143937721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172007334783425106762625147 258011002175137660143937721)
      ·
        refine ⟨193508251631353245107953291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258011002175137660143937721 193508251631353245107953291)
        ·
          refine ⟨290262377447029867661929937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193508251631353245107953291 290262377447029867661929937)
          ·
            refine ⟨217696783085272400746447453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290262377447029867661929937 217696783085272400746447453)
            ·
              refine ⟨81636293656977150279917795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217696783085272400746447453 81636293656977150279917795)
              ·
                refine ⟨122454440485465725419876693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81636293656977150279917795 122454440485465725419876693)
                ·
                  refine ⟨358753243609762867441045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 122454440485465725419876693 358753243609762867441045)
                  ·
                    rfl

theorem cell23_6288025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 10].length) (baseStart_6288025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288025 prefixEnd_6288025 := by exact prefixLift 6288025
  have htrace : WordTrace (prefixWord ++ tailWord_6288025) baseStart_6288025 baseEnd_6288025 := by
    simpa [prefixWord, tailWord_6288025, baseEnd_6288025] using wordTrace_append hprefix tailTrace_6288025
  have hstable : (prefixWord ++ tailWord_6288025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288025).length < 2 ^ (prefixWord ++ tailWord_6288025).sum := by decide
  have hdescent : baseEnd_6288025 < baseStart_6288025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288070 : List Nat := [6, 1, 2, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_6288070 : Nat := 118140960795 + 6288070 * 2 ^ 59
def prefixEnd_6288070 : Nat := 4983230072969 + 3 ^ 40 * 6288070 * 2
def baseEnd_6288070 : Nat := 3228802299117318130906699

theorem tailTrace_6288070 : CollatzResearch.WordTrace tailWord_6288070 prefixEnd_6288070 3228802299117318130906699 := by
  unfold tailWord_6288070
  simp only [CollatzResearch.WordTrace]
  refine ⟨7167023572793868178194427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 152896502886269187801481109 7167023572793868178194427)
  ·
    refine ⟨10750535359190802267291641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7167023572793868178194427 10750535359190802267291641)
    ·
      refine ⟨8062901519393101700468731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10750535359190802267291641 8062901519393101700468731)
      ·
        refine ⟨12094352279089652550703097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8062901519393101700468731 12094352279089652550703097)
        ·
          refine ⟨9070764209317239413027323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12094352279089652550703097 9070764209317239413027323)
          ·
            refine ⟨13606146313975859119540985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9070764209317239413027323 13606146313975859119540985)
            ·
              refine ⟨10204609735481894339655739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13606146313975859119540985 10204609735481894339655739)
              ·
                refine ⟨15306914603222841509483609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10204609735481894339655739 15306914603222841509483609)
                ·
                  refine ⟨11480185952417131132112707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15306914603222841509483609 11480185952417131132112707)
                  ·
                    refine ⟨17220278928625696698169061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11480185952417131132112707 17220278928625696698169061)
                    ·
                      refine ⟨3228802299117318130906699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17220278928625696698169061 3228802299117318130906699)
                      ·
                        rfl

theorem cell23_6288070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_6288070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288070 prefixEnd_6288070 := by exact prefixLift 6288070
  have htrace : WordTrace (prefixWord ++ tailWord_6288070) baseStart_6288070 baseEnd_6288070 := by
    simpa [prefixWord, tailWord_6288070, baseEnd_6288070] using wordTrace_append hprefix tailTrace_6288070
  have hstable : (prefixWord ++ tailWord_6288070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288070).length < 2 ^ (prefixWord ++ tailWord_6288070).sum := by decide
  have hdescent : baseEnd_6288070 < baseStart_6288070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288109 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 5, 1, 4]
def baseStart_6288109 : Nat := 118140960795 + 6288109 * 2 ^ 59
def prefixEnd_6288109 : Nat := 4983230072969 + 3 ^ 40 * 6288109 * 2
def baseEnd_6288109 : Nat := 3228822324862843478319019

theorem tailTrace_6288109 : CollatzResearch.WordTrace tailWord_6288109 prefixEnd_6288109 3228822324862843478319019 := by
  unfold tailWord_6288109
  simp only [CollatzResearch.WordTrace]
  refine ⟨229346176776262491362891381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152897451184174994241927587 229346176776262491362891381)
  ·
    refine ⟨21501204072774608565271067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 229346176776262491362891381 21501204072774608565271067)
    ·
      refine ⟨32251806109161912847906601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21501204072774608565271067 32251806109161912847906601)
      ·
        refine ⟨24188854581871434635929951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32251806109161912847906601 24188854581871434635929951)
        ·
          refine ⟨36283281872807151953894927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24188854581871434635929951 36283281872807151953894927)
          ·
            refine ⟨54424922809210727930842391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36283281872807151953894927 54424922809210727930842391)
            ·
              refine ⟨81637384213816091896263587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54424922809210727930842391 81637384213816091896263587)
              ·
                refine ⟨122456076320724137844395381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81637384213816091896263587 122456076320724137844395381)
                ·
                  refine ⟨11480257155067887922912067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122456076320724137844395381 11480257155067887922912067)
                  ·
                    refine ⟨17220385732601831884368101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11480257155067887922912067 17220385732601831884368101)
                    ·
                      refine ⟨3228822324862843478319019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17220385732601831884368101 3228822324862843478319019)
                      ·
                        rfl

theorem cell23_6288109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_6288109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288109 prefixEnd_6288109 := by exact prefixLift 6288109
  have htrace : WordTrace (prefixWord ++ tailWord_6288109) baseStart_6288109 baseEnd_6288109 := by
    simpa [prefixWord, tailWord_6288109, baseEnd_6288109] using wordTrace_append hprefix tailTrace_6288109
  have hstable : (prefixWord ++ tailWord_6288109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288109).length < 2 ^ (prefixWord ++ tailWord_6288109).sum := by decide
  have hdescent : baseEnd_6288109 < baseStart_6288109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288112 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 5]
def baseStart_6288112 : Nat := 118140960795 + 6288112 * 2 ^ 59
def prefixEnd_6288112 : Nat := 4983230072969 + 3 ^ 40 * 6288112 * 2
def baseEnd_6288112 : Nat := 3228823865304806966581505

theorem tailTrace_6288112 : CollatzResearch.WordTrace tailWord_6288112 prefixEnd_6288112 3228823865304806966581505 := by
  unfold tailWord_6288112
  simp only [CollatzResearch.WordTrace]
  refine ⟨114673143097625811437625295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152897524130167748583500393 114673143097625811437625295)
  ·
    refine ⟨172009714646438717156437943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114673143097625811437625295 172009714646438717156437943)
    ·
      refine ⟨258014571969658075734656915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172009714646438717156437943 258014571969658075734656915)
      ·
        refine ⟨387021857954487113601985373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258014571969658075734656915 387021857954487113601985373)
        ·
          refine ⟨145133196732932667600744515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 387021857954487113601985373 145133196732932667600744515)
          ·
            refine ⟨217699795099399001401116773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145133196732932667600744515 217699795099399001401116773)
            ·
              refine ⟨40818711581137312762709395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 217699795099399001401116773 40818711581137312762709395)
              ·
                refine ⟨61228067371705969144064093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40818711581137312762709395 61228067371705969144064093)
                ·
                  refine ⟨22960525264389738429024035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61228067371705969144064093 22960525264389738429024035)
                  ·
                    refine ⟨34440787896584607643536053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22960525264389738429024035 34440787896584607643536053)
                    ·
                      refine ⟨3228823865304806966581505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34440787896584607643536053 3228823865304806966581505)
                      ·
                        rfl

theorem cell23_6288112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 5].length) (baseStart_6288112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288112 prefixEnd_6288112 := by exact prefixLift 6288112
  have htrace : WordTrace (prefixWord ++ tailWord_6288112) baseStart_6288112 baseEnd_6288112 := by
    simpa [prefixWord, tailWord_6288112, baseEnd_6288112] using wordTrace_append hprefix tailTrace_6288112
  have hstable : (prefixWord ++ tailWord_6288112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288112).length < 2 ^ (prefixWord ++ tailWord_6288112).sum := by decide
  have hdescent : baseEnd_6288112 < baseStart_6288112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288122 : List Nat := [3, 1, 1, 1, 1, 3, 2, 3, 1, 1, 6]
def baseStart_6288122 : Nat := 118140960795 + 6288122 * 2 ^ 59
def prefixEnd_6288122 : Nat := 4983230072969 + 3 ^ 40 * 6288122 * 2
def baseEnd_6288122 : Nat := 3228829000111351927456459

theorem tailTrace_6288122 : CollatzResearch.WordTrace tailWord_6288122 prefixEnd_6288122 3228829000111351927456459 := by
  unfold tailWord_6288122
  simp only [CollatzResearch.WordTrace]
  refine ⟨57336662731303848645778655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152897767283476929722076413 57336662731303848645778655)
  ·
    refine ⟨86004994096955772968667983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57336662731303848645778655 86004994096955772968667983)
    ·
      refine ⟨129007491145433659453001975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86004994096955772968667983 129007491145433659453001975)
      ·
        refine ⟨193511236718150489179502963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129007491145433659453001975 193511236718150489179502963)
        ·
          refine ⟨290266855077225733769254445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193511236718150489179502963 290266855077225733769254445)
          ·
            refine ⟨108850070653959650163470417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 290266855077225733769254445 108850070653959650163470417)
            ·
              refine ⟨81637552990469737622602813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108850070653959650163470417 81637552990469737622602813)
              ·
                refine ⟨30614082371426151608476055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81637552990469737622602813 30614082371426151608476055)
                ·
                  refine ⟨45921123557139227412714083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30614082371426151608476055 45921123557139227412714083)
                  ·
                    refine ⟨68881685335708841119071125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45921123557139227412714083 68881685335708841119071125)
                    ·
                      refine ⟨3228829000111351927456459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68881685335708841119071125 3228829000111351927456459)
                      ·
                        rfl

theorem cell23_6288122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_6288122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288122 prefixEnd_6288122 := by exact prefixLift 6288122
  have htrace : WordTrace (prefixWord ++ tailWord_6288122) baseStart_6288122 baseEnd_6288122 := by
    simpa [prefixWord, tailWord_6288122, baseEnd_6288122] using wordTrace_append hprefix tailTrace_6288122
  have hstable : (prefixWord ++ tailWord_6288122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288122).length < 2 ^ (prefixWord ++ tailWord_6288122).sum := by decide
  have hdescent : baseEnd_6288122 < baseStart_6288122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288126 : List Nat := [4, 2, 2, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_6288126 : Nat := 118140960795 + 6288126 * 2 ^ 59
def prefixEnd_6288126 : Nat := 4983230072969 + 3 ^ 40 * 6288126 * 2
def baseEnd_6288126 : Nat := 3228831054033969911806441

theorem tailTrace_6288126 : CollatzResearch.WordTrace tailWord_6288126 prefixEnd_6288126 3228831054033969911806441 := by
  unfold tailWord_6288126
  simp only [CollatzResearch.WordTrace]
  refine ⟨28668349602150112908282529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152897864544800602177506821 28668349602150112908282529)
  ·
    refine ⟨21501262201612584681211897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28668349602150112908282529 21501262201612584681211897)
    ·
      refine ⟨16125946651209438510908923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21501262201612584681211897 16125946651209438510908923)
      ·
        refine ⟨24188919976814157766363385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16125946651209438510908923 24188919976814157766363385)
        ·
          refine ⟨18141689982610618324772539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24188919976814157766363385 18141689982610618324772539)
          ·
            refine ⟨27212534973915927487158809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18141689982610618324772539 27212534973915927487158809)
            ·
              refine ⟨20409401230436945615369107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27212534973915927487158809 20409401230436945615369107)
              ·
                refine ⟨30614101845655418423053661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20409401230436945615369107 30614101845655418423053661)
                ·
                  refine ⟨11480288192120781908645123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30614101845655418423053661 11480288192120781908645123)
                  ·
                    refine ⟨17220432288181172862967685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11480288192120781908645123 17220432288181172862967685)
                    ·
                      refine ⟨3228831054033969911806441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17220432288181172862967685 3228831054033969911806441)
                      ·
                        rfl

theorem cell23_6288126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_6288126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288126 prefixEnd_6288126 := by exact prefixLift 6288126
  have htrace : WordTrace (prefixWord ++ tailWord_6288126) baseStart_6288126 baseEnd_6288126 := by
    simpa [prefixWord, tailWord_6288126, baseEnd_6288126] using wordTrace_append hprefix tailTrace_6288126
  have hstable : (prefixWord ++ tailWord_6288126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288126).length < 2 ^ (prefixWord ++ tailWord_6288126).sum := by decide
  have hdescent : baseEnd_6288126 < baseStart_6288126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288130 : List Nat := [3, 4, 1, 1, 1, 4, 1, 1, 2, 3, 2]
def baseStart_6288130 : Nat := 118140960795 + 6288130 * 2 ^ 59
def prefixEnd_6288130 : Nat := 4983230072969 + 3 ^ 40 * 6288130 * 2
def baseEnd_6288130 : Nat := 3228833107956587896156423

theorem tailTrace_6288130 : CollatzResearch.WordTrace tailWord_6288130 prefixEnd_6288130 3228833107956587896156423 := by
  unfold tailWord_6288130
  simp only [CollatzResearch.WordTrace]
  refine ⟨57336735677296602987351461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152897961806124274632937229 57336735677296602987351461)
  ·
    refine ⟨10750637939493113060128399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57336735677296602987351461 10750637939493113060128399)
    ·
      refine ⟨16125956909239669590192599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10750637939493113060128399 16125956909239669590192599)
      ·
        refine ⟨24188935363859504385288899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16125956909239669590192599 24188935363859504385288899)
        ·
          refine ⟨36283403045789256577933349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24188935363859504385288899 36283403045789256577933349)
          ·
            refine ⟨6803138071085485608362503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36283403045789256577933349 6803138071085485608362503)
            ·
              refine ⟨10204707106628228412543755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6803138071085485608362503 10204707106628228412543755)
              ·
                refine ⟨15307060659942342618815633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10204707106628228412543755 15307060659942342618815633)
                ·
                  refine ⟨11480295494956756964111725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15307060659942342618815633 11480295494956756964111725)
                  ·
                    refine ⟨4305110810608783861541897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11480295494956756964111725 4305110810608783861541897)
                    ·
                      refine ⟨3228833107956587896156423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4305110810608783861541897 3228833107956587896156423)
                      ·
                        rfl

theorem cell23_6288130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_6288130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288130 prefixEnd_6288130 := by exact prefixLift 6288130
  have htrace : WordTrace (prefixWord ++ tailWord_6288130) baseStart_6288130 baseEnd_6288130 := by
    simpa [prefixWord, tailWord_6288130, baseEnd_6288130] using wordTrace_append hprefix tailTrace_6288130
  have hstable : (prefixWord ++ tailWord_6288130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288130).length < 2 ^ (prefixWord ++ tailWord_6288130).sum := by decide
  have hdescent : baseEnd_6288130 < baseStart_6288130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288152 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 2, 2, 6]
def baseStart_6288152 : Nat := 118140960795 + 6288152 * 2 ^ 59
def prefixEnd_6288152 : Nat := 4983230072969 + 3 ^ 40 * 6288152 * 2
def baseEnd_6288152 : Nat := 3228844404530986810081321

theorem tailTrace_6288152 : CollatzResearch.WordTrace tailWord_6288152 prefixEnd_6288152 3228844404530986810081321 := by
  unfold tailWord_6288152
  simp only [CollatzResearch.WordTrace]
  refine ⟨114673872557553354853353355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152898496743404473137804473 114673872557553354853353355)
  ·
    refine ⟨172010808836330032280030033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114673872557553354853353355 172010808836330032280030033)
    ·
      refine ⟨129008106627247524210022525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172010808836330032280030033 129008106627247524210022525)
      ·
        refine ⟨48378039985217821578758447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129008106627247524210022525 48378039985217821578758447)
        ·
          refine ⟨72567059977826732368137671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48378039985217821578758447 72567059977826732368137671)
          ·
            refine ⟨108850589966740098552206507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72567059977826732368137671 108850589966740098552206507)
            ·
              refine ⟨163275884950110147828309761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108850589966740098552206507 163275884950110147828309761)
              ·
                refine ⟨122456913712582610871232321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163275884950110147828309761 122456913712582610871232321)
                ·
                  refine ⟨91842685284436958153424241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122456913712582610871232321 91842685284436958153424241)
                  ·
                    refine ⟨68882013963327718615068181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91842685284436958153424241 68882013963327718615068181)
                    ·
                      refine ⟨3228844404530986810081321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68882013963327718615068181 3228844404530986810081321)
                      ·
                        rfl

theorem cell23_6288152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_6288152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288152 prefixEnd_6288152 := by exact prefixLift 6288152
  have htrace : WordTrace (prefixWord ++ tailWord_6288152) baseStart_6288152 baseEnd_6288152 := by
    simpa [prefixWord, tailWord_6288152, baseEnd_6288152] using wordTrace_append hprefix tailTrace_6288152
  have hstable : (prefixWord ++ tailWord_6288152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288152).length < 2 ^ (prefixWord ++ tailWord_6288152).sum := by decide
  have hdescent : baseEnd_6288152 < baseStart_6288152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288160 : List Nat := [2, 1, 1, 5, 1, 2, 2, 4, 1, 2, 2]
def baseStart_6288160 : Nat := 118140960795 + 6288160 * 2 ^ 59
def prefixEnd_6288160 : Nat := 4983230072969 + 3 ^ 40 * 6288160 * 2
def baseEnd_6288160 : Nat := 3228848512376222778781285

theorem tailTrace_6288160 : CollatzResearch.WordTrace tailWord_6288160 prefixEnd_6288160 3228848512376222778781285 := by
  unfold tailWord_6288160
  simp only [CollatzResearch.WordTrace]
  refine ⟨114674018449538863536498967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152898691266051818048665289 114674018449538863536498967)
  ·
    refine ⟨172011027674308295304748451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114674018449538863536498967 172011027674308295304748451)
    ·
      refine ⟨258016541511462442957122677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172011027674308295304748451 258016541511462442957122677)
      ·
        refine ⟨24189050766699604027230251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 258016541511462442957122677 24189050766699604027230251)
        ·
          refine ⟨36283576150049406040845377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24189050766699604027230251 36283576150049406040845377)
          ·
            refine ⟨27212682112537054530634033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36283576150049406040845377 27212682112537054530634033)
            ·
              refine ⟨20409511584402790897975525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27212682112537054530634033 20409511584402790897975525)
              ·
                refine ⟨3826783422075523293370411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20409511584402790897975525 3826783422075523293370411)
                ·
                  refine ⟨5740175133113284940055617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3826783422075523293370411 5740175133113284940055617)
                  ·
                    refine ⟨4305131349834963705041713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5740175133113284940055617 4305131349834963705041713)
                    ·
                      refine ⟨3228848512376222778781285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4305131349834963705041713 3228848512376222778781285)
                      ·
                        rfl

theorem cell23_6288160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_6288160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288160 prefixEnd_6288160 := by exact prefixLift 6288160
  have htrace : WordTrace (prefixWord ++ tailWord_6288160) baseStart_6288160 baseEnd_6288160 := by
    simpa [prefixWord, tailWord_6288160, baseEnd_6288160] using wordTrace_append hprefix tailTrace_6288160
  have hstable : (prefixWord ++ tailWord_6288160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288160).length < 2 ^ (prefixWord ++ tailWord_6288160).sum := by decide
  have hdescent : baseEnd_6288160 < baseStart_6288160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288170 : List Nat := [3, 1, 4, 3, 2, 1, 1, 1, 1, 6]
def baseStart_6288170 : Nat := 118140960795 + 6288170 * 2 ^ 59
def prefixEnd_6288170 : Nat := 4983230072969 + 3 ^ 40 * 6288170 * 2
def baseEnd_6288170 : Nat := 1076284549060922579885413

theorem tailTrace_6288170 : CollatzResearch.WordTrace tailWord_6288170 prefixEnd_6288170 1076284549060922579885413 := by
  unfold tailWord_6288170
  simp only [CollatzResearch.WordTrace]
  refine ⟨57337100407260374695215491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152898934419360999187241309 57337100407260374695215491)
  ·
    refine ⟨86005650610890562042823237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57337100407260374695215491 86005650610890562042823237)
    ·
      refine ⟨16126059489541980383029357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86005650610890562042823237 16126059489541980383029357)
      ·
        refine ⟨6047272308578242643636009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16126059489541980383029357 6047272308578242643636009)
        ·
          refine ⟨4535454231433681982727007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6047272308578242643636009 4535454231433681982727007)
          ·
            refine ⟨6803181347150522974090511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4535454231433681982727007 6803181347150522974090511)
            ·
              refine ⟨10204772020725784461135767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6803181347150522974090511 10204772020725784461135767)
              ·
                refine ⟨15307158031088676691703651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10204772020725784461135767 15307158031088676691703651)
                ·
                  refine ⟨22960737046633015037555477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15307158031088676691703651 22960737046633015037555477)
                  ·
                    refine ⟨1076284549060922579885413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22960737046633015037555477 1076284549060922579885413)
                    ·
                      rfl

theorem cell23_6288170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_6288170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288170 prefixEnd_6288170 := by exact prefixLift 6288170
  have htrace : WordTrace (prefixWord ++ tailWord_6288170) baseStart_6288170 baseEnd_6288170 := by
    simpa [prefixWord, tailWord_6288170, baseEnd_6288170] using wordTrace_append hprefix tailTrace_6288170
  have hstable : (prefixWord ++ tailWord_6288170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288170).length < 2 ^ (prefixWord ++ tailWord_6288170).sum := by decide
  have hdescent : baseEnd_6288170 < baseStart_6288170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288173 : List Nat := [1, 5, 3, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_6288173 : Nat := 118140960795 + 6288173 * 2 ^ 59
def prefixEnd_6288173 : Nat := 4983230072969 + 3 ^ 40 * 6288173 * 2
def baseEnd_6288173 : Nat := 3228855187624731227918725

theorem tailTrace_6288173 : CollatzResearch.WordTrace tailWord_6288173 prefixEnd_6288173 3228855187624731227918725 := by
  unfold tailWord_6288173
  simp only [CollatzResearch.WordTrace]
  refine ⟨229348511048030630293221173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152899007365353753528814115 229348511048030630293221173)
  ·
    refine ⟨21501422910752871589989485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 229348511048030630293221173 21501422910752871589989485)
    ·
      refine ⟨8063033591532326846246057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21501422910752871589989485 8063033591532326846246057)
      ·
        refine ⟨6047275193649245134684543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8063033591532326846246057 6047275193649245134684543)
        ·
          refine ⟨9070912790473867702026815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6047275193649245134684543 9070912790473867702026815)
          ·
            refine ⟨13606369185710801553040223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9070912790473867702026815 13606369185710801553040223)
            ·
              refine ⟨20409553778566202329560335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13606369185710801553040223 20409553778566202329560335)
              ·
                refine ⟨30614330667849303494340503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20409553778566202329560335 30614330667849303494340503)
                ·
                  refine ⟨45921496001773955241510755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30614330667849303494340503 45921496001773955241510755)
                  ·
                    refine ⟨68882244002660932862266133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45921496001773955241510755 68882244002660932862266133)
                    ·
                      refine ⟨3228855187624731227918725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68882244002660932862266133 3228855187624731227918725)
                      ·
                        rfl

theorem cell23_6288173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_6288173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288173 prefixEnd_6288173 := by exact prefixLift 6288173
  have htrace : WordTrace (prefixWord ++ tailWord_6288173) baseStart_6288173 baseEnd_6288173 := by
    simpa [prefixWord, tailWord_6288173, baseEnd_6288173] using wordTrace_append hprefix tailTrace_6288173
  have hstable : (prefixWord ++ tailWord_6288173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288173).length < 2 ^ (prefixWord ++ tailWord_6288173).sum := by decide
  have hdescent : baseEnd_6288173 < baseStart_6288173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288176 : List Nat := [2, 1, 1, 1, 2, 2, 1, 7, 2, 1, 3]
def baseStart_6288176 : Nat := 118140960795 + 6288176 * 2 ^ 59
def prefixEnd_6288176 : Nat := 4983230072969 + 3 ^ 40 * 6288176 * 2
def baseEnd_6288176 : Nat := 3228856728066694716181211

theorem tailTrace_6288176 : CollatzResearch.WordTrace tailWord_6288176 prefixEnd_6288176 3228856728066694716181211 := by
  unfold tailWord_6288176
  simp only [CollatzResearch.WordTrace]
  refine ⟨114674310233509880902790191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152899080311346507870386921 114674310233509880902790191)
  ·
    refine ⟨172011465350264821354185287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114674310233509880902790191 172011465350264821354185287)
    ·
      refine ⟨258017198025397232031277931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172011465350264821354185287 258017198025397232031277931)
      ·
        refine ⟨387025797038095848046916897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258017198025397232031277931 387025797038095848046916897)
        ·
          refine ⟨290269347778571886035187673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387025797038095848046916897 290269347778571886035187673)
          ·
            refine ⟨217702010833928914526390755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290269347778571886035187673 217702010833928914526390755)
            ·
              refine ⟨326553016250893371789586133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217702010833928914526390755 326553016250893371789586133)
              ·
                refine ⟨7653586318380313401318425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 326553016250893371789586133 7653586318380313401318425)
                ·
                  refine ⟨5740189738785235050988819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7653586318380313401318425 5740189738785235050988819)
                  ·
                    refine ⟨8610284608177852576483229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5740189738785235050988819 8610284608177852576483229)
                    ·
                      refine ⟨3228856728066694716181211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8610284608177852576483229 3228856728066694716181211)
                      ·
                        rfl

theorem cell23_6288176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 2, 1, 3].length) (baseStart_6288176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288176 prefixEnd_6288176 := by exact prefixLift 6288176
  have htrace : WordTrace (prefixWord ++ tailWord_6288176) baseStart_6288176 baseEnd_6288176 := by
    simpa [prefixWord, tailWord_6288176, baseEnd_6288176] using wordTrace_append hprefix tailTrace_6288176
  have hstable : (prefixWord ++ tailWord_6288176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288176).length < 2 ^ (prefixWord ++ tailWord_6288176).sum := by decide
  have hdescent : baseEnd_6288176 < baseStart_6288176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288180 : List Nat := [2, 5, 1, 1, 3, 1, 2, 2, 1, 2, 3]
def baseStart_6288180 : Nat := 118140960795 + 6288180 * 2 ^ 59
def prefixEnd_6288180 : Nat := 4983230072969 + 3 ^ 40 * 6288180 * 2
def baseEnd_6288180 : Nat := 3228858781989312700531193

theorem tailTrace_6288180 : CollatzResearch.WordTrace tailWord_6288180 prefixEnd_6288180 3228858781989312700531193 := by
  unfold tailWord_6288180
  simp only [CollatzResearch.WordTrace]
  refine ⟨114674383179502635244362997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152899177572670180325817329 114674383179502635244362997)
  ·
    refine ⟨10750723423078372054159031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114674383179502635244362997 10750723423078372054159031)
    ·
      refine ⟨16126085134617558081238547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10750723423078372054159031 16126085134617558081238547)
      ·
        refine ⟨24189127701926337121857821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16126085134617558081238547 24189127701926337121857821)
        ·
          refine ⟨9070922888222376420696683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24189127701926337121857821 9070922888222376420696683)
          ·
            refine ⟨13606384332333564631045025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9070922888222376420696683 13606384332333564631045025)
            ·
              refine ⟨10204788249250173473283769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13606384332333564631045025 10204788249250173473283769)
              ·
                refine ⟨7653591186937630104962827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10204788249250173473283769 7653591186937630104962827)
                ·
                  refine ⟨11480386780406445157444241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7653591186937630104962827 11480386780406445157444241)
                  ·
                    refine ⟨8610290085304833868083181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11480386780406445157444241 8610290085304833868083181)
                    ·
                      refine ⟨3228858781989312700531193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8610290085304833868083181 3228858781989312700531193)
                      ·
                        rfl

theorem cell23_6288180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_6288180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288180 prefixEnd_6288180 := by exact prefixLift 6288180
  have htrace : WordTrace (prefixWord ++ tailWord_6288180) baseStart_6288180 baseEnd_6288180 := by
    simpa [prefixWord, tailWord_6288180, baseEnd_6288180] using wordTrace_append hprefix tailTrace_6288180
  have hstable : (prefixWord ++ tailWord_6288180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288180).length < 2 ^ (prefixWord ++ tailWord_6288180).sum := by decide
  have hdescent : baseEnd_6288180 < baseStart_6288180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288192 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 1, 8]
def baseStart_6288192 : Nat := 118140960795 + 6288192 * 2 ^ 59
def prefixEnd_6288192 : Nat := 4983230072969 + 3 ^ 40 * 6288192 * 2
def baseEnd_6288192 : Nat := 1076288314585722217860379

theorem tailTrace_6288192 : CollatzResearch.WordTrace tailWord_6288192 prefixEnd_6288192 1076288314585722217860379 := by
  unfold tailWord_6288192
  simp only [CollatzResearch.WordTrace]
  refine ⟨114674602017480898269081415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152899469356641197692108553 114674602017480898269081415)
  ·
    refine ⟨172011903026221347403622123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114674602017480898269081415 172011903026221347403622123)
    ·
      refine ⟨258017854539332021105433185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172011903026221347403622123 258017854539332021105433185)
      ·
        refine ⟨193513390904499015829074889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258017854539332021105433185 193513390904499015829074889)
        ·
          refine ⟨145135043178374261871806167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193513390904499015829074889 145135043178374261871806167)
          ·
            refine ⟨217702564767561392807709251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145135043178374261871806167 217702564767561392807709251)
            ·
              refine ⟨326553847151342089211563877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217702564767561392807709251 326553847151342089211563877)
              ·
                refine ⟨61228846340876641727168227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 326553847151342089211563877 61228846340876641727168227)
                ·
                  refine ⟨91843269511314962590752341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61228846340876641727168227 91843269511314962590752341)
                  ·
                    refine ⟨1076288314585722217860379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 91843269511314962590752341 1076288314585722217860379)
                    ·
                      rfl

theorem cell23_6288192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 1, 8].length) (baseStart_6288192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288192 prefixEnd_6288192 := by exact prefixLift 6288192
  have htrace : WordTrace (prefixWord ++ tailWord_6288192) baseStart_6288192 baseEnd_6288192 := by
    simpa [prefixWord, tailWord_6288192, baseEnd_6288192] using wordTrace_append hprefix tailTrace_6288192
  have hstable : (prefixWord ++ tailWord_6288192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288192).length < 2 ^ (prefixWord ++ tailWord_6288192).sum := by decide
  have hdescent : baseEnd_6288192 < baseStart_6288192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288229 : List Nat := [1, 3, 1, 3, 1, 1, 2, 3, 2, 2, 4]
def baseStart_6288229 : Nat := 118140960795 + 6288229 * 2 ^ 59
def prefixEnd_6288229 : Nat := 4983230072969 + 3 ^ 40 * 6288229 * 2
def baseEnd_6288229 : Nat := 3228883942541383008818467

theorem tailTrace_6288229 : CollatzResearch.WordTrace tailWord_6288229 prefixEnd_6288229 3228883942541383008818467 := by
  unfold tailWord_6288229
  simp only [CollatzResearch.WordTrace]
  refine ⟨229350553535827751857259741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152900369023885167904839827 229350553535827751857259741)
  ·
    refine ⟨86006457575935406946472403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229350553535827751857259741 86006457575935406946472403)
    ·
      refine ⟨129009686363903110419708605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86006457575935406946472403 129009686363903110419708605)
      ·
        refine ⟨48378632386463666407390727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129009686363903110419708605 48378632386463666407390727)
        ·
          refine ⟨72567948579695499611086091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48378632386463666407390727 72567948579695499611086091)
          ·
            refine ⟨108851922869543249416629137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72567948579695499611086091 108851922869543249416629137)
            ·
              refine ⟨81638942152157437062471853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108851922869543249416629137 81638942152157437062471853)
              ·
                refine ⟨30614603307059038898426945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81638942152157437062471853 30614603307059038898426945)
                ·
                  refine ⟨22960952480294279173820209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30614603307059038898426945 22960952480294279173820209)
                  ·
                    refine ⟨17220714360220709380365157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22960952480294279173820209 17220714360220709380365157)
                    ·
                      refine ⟨3228883942541383008818467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17220714360220709380365157 3228883942541383008818467)
                      ·
                        rfl

theorem cell23_6288229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_6288229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288229 prefixEnd_6288229 := by exact prefixLift 6288229
  have htrace : WordTrace (prefixWord ++ tailWord_6288229) baseStart_6288229 baseEnd_6288229 := by
    simpa [prefixWord, tailWord_6288229, baseEnd_6288229] using wordTrace_append hprefix tailTrace_6288229
  have hstable : (prefixWord ++ tailWord_6288229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288229).length < 2 ^ (prefixWord ++ tailWord_6288229).sum := by decide
  have hdescent : baseEnd_6288229 < baseStart_6288229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288254 : List Nat := [4, 2, 3, 1, 2, 1, 3, 1, 1, 3, 2]
def baseStart_6288254 : Nat := 118140960795 + 6288254 * 2 ^ 59
def prefixEnd_6288254 : Nat := 4983230072969 + 3 ^ 40 * 6288254 * 2
def baseEnd_6288254 : Nat := 3228896779557745411005853

theorem tailTrace_6288254 : CollatzResearch.WordTrace tailWord_6288254 prefixEnd_6288254 3228896779557745411005853 := by
  unfold tailWord_6288254
  simp only [CollatzResearch.WordTrace]
  refine ⟨28668933170092147640864977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152900976907158120751279877 28668933170092147640864977)
  ·
    refine ⟨21501699877569110730648733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28668933170092147640864977 21501699877569110730648733)
    ·
      refine ⟨8063137454088416523993275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21501699877569110730648733 8063137454088416523993275)
      ·
        refine ⟨12094706181132624785989913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8063137454088416523993275 12094706181132624785989913)
        ·
          refine ⟨9071029635849468589492435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12094706181132624785989913 9071029635849468589492435)
          ·
            refine ⟨13606544453774202884238653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9071029635849468589492435 13606544453774202884238653)
            ·
              refine ⟨5102454170165326081589495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13606544453774202884238653 5102454170165326081589495)
              ·
                refine ⟨7653681255247989122384243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5102454170165326081589495 7653681255247989122384243)
                ·
                  refine ⟨11480521882871983683576365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7653681255247989122384243 11480521882871983683576365)
                  ·
                    refine ⟨4305195706076993881341137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11480521882871983683576365 4305195706076993881341137)
                    ·
                      refine ⟨3228896779557745411005853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4305195706076993881341137 3228896779557745411005853)
                      ·
                        rfl

theorem cell23_6288254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_6288254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288254 prefixEnd_6288254 := by exact prefixLift 6288254
  have htrace : WordTrace (prefixWord ++ tailWord_6288254) baseStart_6288254 baseEnd_6288254 := by
    simpa [prefixWord, tailWord_6288254, baseEnd_6288254] using wordTrace_append hprefix tailTrace_6288254
  have hstable : (prefixWord ++ tailWord_6288254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288254).length < 2 ^ (prefixWord ++ tailWord_6288254).sum := by decide
  have hdescent : baseEnd_6288254 < baseStart_6288254 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288279 : List Nat := [1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 5]
def baseStart_6288279 : Nat := 118140960795 + 6288279 * 2 ^ 59
def prefixEnd_6288279 : Nat := 4983230072969 + 3 ^ 40 * 6288279 * 2
def baseEnd_6288279 : Nat := 3228909616574107813193237

theorem tailTrace_6288279 : CollatzResearch.WordTrace tailWord_6288279 prefixEnd_6288279 3228909616574107813193237 := by
  unfold tailWord_6288279
  simp only [CollatzResearch.WordTrace]
  refine ⟨229352377185646610396579891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152901584790431073597719927 229352377185646610396579891)
  ·
    refine ⟨344028565778469915594869837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229352377185646610396579891 344028565778469915594869837)
    ·
      refine ⟨129010712166926218348076189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344028565778469915594869837 129010712166926218348076189)
      ·
        refine ⟨48379017062597331880528571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129010712166926218348076189 48379017062597331880528571)
        ·
          refine ⟨72568525593895997820792857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48379017062597331880528571 72568525593895997820792857)
          ·
            refine ⟨54426394195421998365594643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72568525593895997820792857 54426394195421998365594643)
            ·
              refine ⟨81639591293132997548391965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54426394195421998365594643 81639591293132997548391965)
              ·
                refine ⟨30614846734924874080646987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81639591293132997548391965 30614846734924874080646987)
                ·
                  refine ⟨45922270102387311120970481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30614846734924874080646987 45922270102387311120970481)
                  ·
                    refine ⟨34441702576790483340727861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45922270102387311120970481 34441702576790483340727861)
                    ·
                      refine ⟨3228909616574107813193237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34441702576790483340727861 3228909616574107813193237)
                      ·
                        rfl

theorem cell23_6288279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_6288279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288279 prefixEnd_6288279 := by exact prefixLift 6288279
  have htrace : WordTrace (prefixWord ++ tailWord_6288279) baseStart_6288279 baseEnd_6288279 := by
    simpa [prefixWord, tailWord_6288279, baseEnd_6288279] using wordTrace_append hprefix tailTrace_6288279
  have hstable : (prefixWord ++ tailWord_6288279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288279).length < 2 ^ (prefixWord ++ tailWord_6288279).sum := by decide
  have hdescent : baseEnd_6288279 < baseStart_6288279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288423 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 3, 6]
def baseStart_6288423 : Nat := 118140960795 + 6288423 * 2 ^ 59
def prefixEnd_6288423 : Nat := 4983230072969 + 3 ^ 40 * 6288423 * 2
def baseEnd_6288423 : Nat := 1076327852596118416597525

theorem tailTrace_6288423 : CollatzResearch.WordTrace tailWord_6288423 prefixEnd_6288423 1076327852596118416597525 := by
  unfold tailWord_6288423
  simp only [CollatzResearch.WordTrace]
  refine ⟨229357629297124922989821923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152905086198083281993214615 229357629297124922989821923)
  ·
    refine ⟨344036443945687384484732885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229357629297124922989821923 344036443945687384484732885)
    ·
      refine ⟨8063354154977048073860927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 344036443945687384484732885 8063354154977048073860927)
      ·
        refine ⟨12095031232465572110791391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8063354154977048073860927 12095031232465572110791391)
        ·
          refine ⟨18142546848698358166187087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12095031232465572110791391 18142546848698358166187087)
          ·
            refine ⟨27213820273047537249280631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18142546848698358166187087 27213820273047537249280631)
            ·
              refine ⟨40820730409571305873920947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27213820273047537249280631 40820730409571305873920947)
              ·
                refine ⟨61231095614356958810881421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40820730409571305873920947 61231095614356958810881421)
                ·
                  refine ⟨22961660855383859554080533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61231095614356958810881421 22961660855383859554080533)
                  ·
                    refine ⟨1076327852596118416597525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22961660855383859554080533 1076327852596118416597525)
                    ·
                      rfl

theorem cell23_6288423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_6288423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288423 prefixEnd_6288423 := by exact prefixLift 6288423
  have htrace : WordTrace (prefixWord ++ tailWord_6288423) baseStart_6288423 baseEnd_6288423 := by
    simpa [prefixWord, tailWord_6288423, baseEnd_6288423] using wordTrace_append hprefix tailTrace_6288423
  have hstable : (prefixWord ++ tailWord_6288423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288423).length < 2 ^ (prefixWord ++ tailWord_6288423).sum := by decide
  have hdescent : baseEnd_6288423 < baseStart_6288423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288440 : List Nat := [2, 1, 2, 1, 5, 2, 2, 2, 2, 4]
def baseStart_6288440 : Nat := 118140960795 + 6288440 * 2 ^ 59
def prefixEnd_6288440 : Nat := 4983230072969 + 3 ^ 40 * 6288440 * 2
def baseEnd_6288440 : Nat := 1076330762319827227759999

theorem tailTrace_6288440 : CollatzResearch.WordTrace tailWord_6288440 prefixEnd_6288440 1076330762319827227759999 := by
  unfold tailWord_6288440
  simp only [CollatzResearch.WordTrace]
  refine ⟨114679124669031667446595387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152905499558708889928793849 114679124669031667446595387)
  ·
    refine ⟨172018687003547501169893081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114679124669031667446595387 172018687003547501169893081)
    ·
      refine ⟨129014015252660625877419811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172018687003547501169893081 129014015252660625877419811)
      ·
        refine ⟨193521022878990938816129717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129014015252660625877419811 193521022878990938816129717)
        ·
          refine ⟨18142595894905400514012161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 193521022878990938816129717 18142595894905400514012161)
          ·
            refine ⟨13606946921179050385509121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18142595894905400514012161 13606946921179050385509121)
            ·
              refine ⟨10205210190884287789131841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13606946921179050385509121 10205210190884287789131841)
              ·
                refine ⟨7653907643163215841848881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10205210190884287789131841 7653907643163215841848881)
                ·
                  refine ⟨5740430732372411881386661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7653907643163215841848881 5740430732372411881386661)
                  ·
                    refine ⟨1076330762319827227759999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5740430732372411881386661 1076330762319827227759999)
                    ·
                      rfl

theorem cell23_6288440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 2, 4].length) (baseStart_6288440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288440 prefixEnd_6288440 := by exact prefixLift 6288440
  have htrace : WordTrace (prefixWord ++ tailWord_6288440) baseStart_6288440 baseEnd_6288440 := by
    simpa [prefixWord, tailWord_6288440, baseEnd_6288440] using wordTrace_append hprefix tailTrace_6288440
  have hstable : (prefixWord ++ tailWord_6288440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288440).length < 2 ^ (prefixWord ++ tailWord_6288440).sum := by decide
  have hdescent : baseEnd_6288440 < baseStart_6288440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288496 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 4, 6]
def baseStart_6288496 : Nat := 118140960795 + 6288496 * 2 ^ 59
def prefixEnd_6288496 : Nat := 4983230072969 + 3 ^ 40 * 6288496 * 2
def baseEnd_6288496 : Nat := 1076340347292044488059913

theorem tailTrace_6288496 : CollatzResearch.WordTrace tailWord_6288496 prefixEnd_6288496 1076340347292044488059913 := by
  unfold tailWord_6288496
  simp only [CollatzResearch.WordTrace]
  refine ⟨114680145912930228228614671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152906861217240304304819561 114680145912930228228614671)
  ·
    refine ⟨172020218869395342342922007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114680145912930228228614671 172020218869395342342922007)
    ·
      refine ⟨258030328304093013514383011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172020218869395342342922007 258030328304093013514383011)
      ·
        refine ⟨387045492456139520271574517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258030328304093013514383011 387045492456139520271574517)
        ·
          refine ⟨36285514917763080025460111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 387045492456139520271574517 36285514917763080025460111)
          ·
            refine ⟨54428272376644620038190167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36285514917763080025460111 54428272376644620038190167)
            ·
              refine ⟨81642408564966930057285251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54428272376644620038190167 81642408564966930057285251)
              ·
                refine ⟨122463612847450395085927877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81642408564966930057285251 122463612847450395085927877)
                ·
                  refine ⟨22961927408896949078611477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122463612847450395085927877 22961927408896949078611477)
                  ·
                    refine ⟨1076340347292044488059913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22961927408896949078611477 1076340347292044488059913)
                    ·
                      rfl

theorem cell23_6288496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 4, 6].length) (baseStart_6288496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288496 prefixEnd_6288496 := by exact prefixLift 6288496
  have htrace : WordTrace (prefixWord ++ tailWord_6288496) baseStart_6288496 baseEnd_6288496 := by
    simpa [prefixWord, tailWord_6288496, baseEnd_6288496] using wordTrace_append hprefix tailTrace_6288496
  have hstable : (prefixWord ++ tailWord_6288496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288496).length < 2 ^ (prefixWord ++ tailWord_6288496).sum := by decide
  have hdescent : baseEnd_6288496 < baseStart_6288496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288513 : List Nat := [1, 2, 4, 2, 2, 1, 2, 1, 2, 6]
def baseStart_6288513 : Nat := 118140960795 + 6288513 * 2 ^ 59
def prefixEnd_6288513 : Nat := 4983230072969 + 3 ^ 40 * 6288513 * 2
def baseEnd_6288513 : Nat := 1076343257015753299222387

theorem tailTrace_6288513 : CollatzResearch.WordTrace tailWord_6288513 prefixEnd_6288513 1076343257015753299222387 := by
  unfold tailWord_6288513
  simp only [CollatzResearch.WordTrace]
  refine ⟨229360911866798868360598193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152907274577865912240398795 229360911866798868360598193)
  ·
    refine ⟨172020683900099151270448645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229360911866798868360598193 172020683900099151270448645)
    ·
      refine ⟨32253878231268590863209121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172020683900099151270448645 32253878231268590863209121)
      ·
        refine ⟨24190408673451443147406841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32253878231268590863209121 24190408673451443147406841)
        ·
          refine ⟨18142806505088582360555131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24190408673451443147406841 18142806505088582360555131)
          ·
            refine ⟨27214209757632873540832697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18142806505088582360555131 27214209757632873540832697)
            ·
              refine ⟨20410657318224655155624523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27214209757632873540832697 20410657318224655155624523)
              ·
                refine ⟨30615985977336982733436785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20410657318224655155624523 30615985977336982733436785)
                ·
                  refine ⟨22961989483002737050077589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30615985977336982733436785 22961989483002737050077589)
                  ·
                    refine ⟨1076343257015753299222387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22961989483002737050077589 1076343257015753299222387)
                    ·
                      rfl

theorem cell23_6288513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_6288513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288513 prefixEnd_6288513 := by exact prefixLift 6288513
  have htrace : WordTrace (prefixWord ++ tailWord_6288513) baseStart_6288513 baseEnd_6288513 := by
    simpa [prefixWord, tailWord_6288513, baseEnd_6288513] using wordTrace_append hprefix tailTrace_6288513
  have hstable : (prefixWord ++ tailWord_6288513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288513).length < 2 ^ (prefixWord ++ tailWord_6288513).sum := by decide
  have hdescent : baseEnd_6288513 < baseStart_6288513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288554 : List Nat := [3, 1, 5, 1, 1, 1, 2, 1, 4, 2, 2]
def baseStart_6288554 : Nat := 118140960795 + 6288554 * 2 ^ 59
def prefixEnd_6288554 : Nat := 4983230072969 + 3 ^ 40 * 6288554 * 2
def baseEnd_6288554 : Nat := 3229050823754094237254473

theorem tailTrace_6288554 : CollatzResearch.WordTrace tailWord_6288554 prefixEnd_6288554 3229050823754094237254473 := by
  unfold tailWord_6288554
  simp only [CollatzResearch.WordTrace]
  refine ⟨57340601814912583090710179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152908271506433554908560477 57340601814912583090710179)
  ·
    refine ⟨86010902722368874636065269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57340601814912583090710179 86010902722368874636065269)
    ·
      refine ⟨8063522130222081997131119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86010902722368874636065269 8063522130222081997131119)
      ·
        refine ⟨12095283195333122995696679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8063522130222081997131119 12095283195333122995696679)
        ·
          refine ⟨18142924792999684493545019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12095283195333122995696679 18142924792999684493545019)
          ·
            refine ⟨27214387189499526740317529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18142924792999684493545019 27214387189499526740317529)
            ·
              refine ⟨20410790392124645055238147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27214387189499526740317529 20410790392124645055238147)
              ·
                refine ⟨30616185588186967582857221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20410790392124645055238147 30616185588186967582857221)
                ·
                  refine ⟨5740534797785056421785729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30616185588186967582857221 5740534797785056421785729)
                  ·
                    refine ⟨4305401098338792316339297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5740534797785056421785729 4305401098338792316339297)
                    ·
                      refine ⟨3229050823754094237254473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4305401098338792316339297 3229050823754094237254473)
                      ·
                        rfl

theorem cell23_6288554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_6288554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288554 prefixEnd_6288554 := by exact prefixLift 6288554
  have htrace : WordTrace (prefixWord ++ tailWord_6288554) baseStart_6288554 baseEnd_6288554 := by
    simpa [prefixWord, tailWord_6288554, baseEnd_6288554] using wordTrace_append hprefix tailTrace_6288554
  have hstable : (prefixWord ++ tailWord_6288554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288554).length < 2 ^ (prefixWord ++ tailWord_6288554).sum := by decide
  have hdescent : baseEnd_6288554 < baseStart_6288554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288556 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 3, 7]
def baseStart_6288556 : Nat := 118140960795 + 6288556 * 2 ^ 59
def prefixEnd_6288556 : Nat := 4983230072969 + 3 ^ 40 * 6288556 * 2
def baseEnd_6288556 : Nat := 1076350616905134409809821

theorem tailTrace_6288556 : CollatzResearch.WordTrace tailWord_6288556 prefixEnd_6288556 1076350616905134409809821 := by
  unfold tailWord_6288556
  simp only [CollatzResearch.WordTrace]
  refine ⟨114681240102821543352206761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152908320137095391136275681 114681240102821543352206761)
  ·
    refine ⟨86010930077116157514155071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114681240102821543352206761 86010930077116157514155071)
    ·
      refine ⟨129016395115674236271232607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86010930077116157514155071 129016395115674236271232607)
      ·
        refine ⟨193524592673511354406848911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129016395115674236271232607 193524592673511354406848911)
        ·
          refine ⟨290286889010267031610273367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193524592673511354406848911 290286889010267031610273367)
          ·
            refine ⟨435430333515400547415410051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290286889010267031610273367 435430333515400547415410051)
            ·
              refine ⟨653145500273100821123115077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 435430333515400547415410051 653145500273100821123115077)
              ·
                refine ⟨122464781301206403960584077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 653145500273100821123115077 122464781301206403960584077)
                ·
                  refine ⟨45924292987952401485219029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122464781301206403960584077 45924292987952401485219029)
                  ·
                    refine ⟨1076350616905134409809821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45924292987952401485219029 1076350616905134409809821)
                    ·
                      rfl

theorem cell23_6288556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 7].length) (baseStart_6288556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288556 prefixEnd_6288556 := by exact prefixLift 6288556
  have htrace : WordTrace (prefixWord ++ tailWord_6288556) baseStart_6288556 baseEnd_6288556 := by
    simpa [prefixWord, tailWord_6288556, baseEnd_6288556] using wordTrace_append hprefix tailTrace_6288556
  have hstable : (prefixWord ++ tailWord_6288556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288556).length < 2 ^ (prefixWord ++ tailWord_6288556).sum := by decide
  have hdescent : baseEnd_6288556 < baseStart_6288556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288630 : List Nat := [5, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3]
def baseStart_6288630 : Nat := 118140960795 + 6288630 * 2 ^ 59
def prefixEnd_6288630 : Nat := 4983230072969 + 3 ^ 40 * 6288630 * 2
def baseEnd_6288630 : Nat := 3229089848283835939904123

theorem tailTrace_6288630 : CollatzResearch.WordTrace tailWord_6288630 prefixEnd_6288630 3229089848283835939904123 := by
  unfold tailWord_6288630
  simp only [CollatzResearch.WordTrace]
  refine ⟨14335323700460937333912959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152910119471583331561738229 14335323700460937333912959)
  ·
    refine ⟨21502985550691406000869439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14335323700460937333912959 21502985550691406000869439)
    ·
      refine ⟨32254478326037109001304159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21502985550691406000869439 32254478326037109001304159)
      ·
        refine ⟨48381717489055663501956239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32254478326037109001304159 48381717489055663501956239)
        ·
          refine ⟨72572576233583495252934359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48381717489055663501956239 72572576233583495252934359)
          ·
            refine ⟨108858864350375242879401539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72572576233583495252934359 108858864350375242879401539)
            ·
              refine ⟨163288296525562864319102309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108858864350375242879401539 163288296525562864319102309)
              ·
                refine ⟨30616555598543037059831683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163288296525562864319102309 30616555598543037059831683)
                ·
                  refine ⟨45924833397814555589747525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30616555598543037059831683 45924833397814555589747525)
                  ·
                    refine ⟨8610906262090229173077661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45924833397814555589747525 8610906262090229173077661)
                    ·
                      refine ⟨3229089848283835939904123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8610906262090229173077661 3229089848283835939904123)
                      ·
                        rfl

theorem cell23_6288630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_6288630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288630 prefixEnd_6288630 := by exact prefixLift 6288630
  have htrace : WordTrace (prefixWord ++ tailWord_6288630) baseStart_6288630 baseEnd_6288630 := by
    simpa [prefixWord, tailWord_6288630, baseEnd_6288630] using wordTrace_append hprefix tailTrace_6288630
  have hstable : (prefixWord ++ tailWord_6288630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288630).length < 2 ^ (prefixWord ++ tailWord_6288630).sum := by decide
  have hdescent : baseEnd_6288630 < baseStart_6288630 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288633 : List Nat := [1, 2, 1, 3, 1, 1, 3, 5, 6]
def baseStart_6288633 : Nat := 118140960795 + 6288633 * 2 ^ 59
def prefixEnd_6288633 : Nat := 4983230072969 + 3 ^ 40 * 6288633 * 2
def baseEnd_6288633 : Nat := 358787932080644380907401

theorem tailTrace_6288633 : CollatzResearch.WordTrace tailWord_6288633 prefixEnd_6288633 358787932080644380907401 := by
  unfold tailWord_6288633
  simp only [CollatzResearch.WordTrace]
  refine ⟨229365288626364128854966553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152910192417576085903311035 229365288626364128854966553)
  ·
    refine ⟨172023966469773096641224915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229365288626364128854966553 172023966469773096641224915)
    ·
      refine ⟨258035949704659644961837373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172023966469773096641224915 258035949704659644961837373)
      ·
        refine ⟨96763481139247366860689015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258035949704659644961837373 96763481139247366860689015)
        ·
          refine ⟨145145221708871050291033523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96763481139247366860689015 145145221708871050291033523)
          ·
            refine ⟨217717832563306575436550285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145145221708871050291033523 217717832563306575436550285)
            ·
              refine ⟨81644187211239965788706357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217717832563306575436550285 81644187211239965788706357)
              ·
                refine ⟨7654142551053746792691221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81644187211239965788706357 7654142551053746792691221)
                ·
                  refine ⟨358787932080644380907401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7654142551053746792691221 358787932080644380907401)
                  ·
                    rfl

theorem cell23_6288633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 6].length) (baseStart_6288633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288633 prefixEnd_6288633 := by exact prefixLift 6288633
  have htrace : WordTrace (prefixWord ++ tailWord_6288633) baseStart_6288633 baseEnd_6288633 := by
    simpa [prefixWord, tailWord_6288633, baseEnd_6288633] using wordTrace_append hprefix tailTrace_6288633
  have hstable : (prefixWord ++ tailWord_6288633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288633).length < 2 ^ (prefixWord ++ tailWord_6288633).sum := by decide
  have hdescent : baseEnd_6288633 < baseStart_6288633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288654 : List Nat := [4, 1, 1, 2, 1, 4, 2, 3, 1, 4]
def baseStart_6288654 : Nat := 118140960795 + 6288654 * 2 ^ 59
def prefixEnd_6288654 : Nat := 4983230072969 + 3 ^ 40 * 6288654 * 2
def baseEnd_6288654 : Nat := 1076367390606514615334671

theorem tailTrace_6288654 : CollatzResearch.WordTrace tailWord_6288654 prefixEnd_6288654 1076367390606514615334671 := by
  unfold tailWord_6288654
  simp only [CollatzResearch.WordTrace]
  refine ⟨28670756819911006180185127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152910703039525366294320677 28670756819911006180185127)
  ·
    refine ⟨43006135229866509270277691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28670756819911006180185127 43006135229866509270277691)
    ·
      refine ⟨64509202844799763905416537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43006135229866509270277691 64509202844799763905416537)
      ·
        refine ⟨48381902133599822929062403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64509202844799763905416537 48381902133599822929062403)
        ·
          refine ⟨72572853200399734393593605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48381902133599822929062403 72572853200399734393593605)
          ·
            refine ⟨13607409975074950198798801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72572853200399734393593605 13607409975074950198798801)
            ·
              refine ⟨10205557481306212649099101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13607409975074950198798801 10205557481306212649099101)
              ·
                refine ⟨3827084055489829743412163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10205557481306212649099101 3827084055489829743412163)
                ·
                  refine ⟨5740626083234744615118245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3827084055489829743412163 5740626083234744615118245)
                  ·
                    refine ⟨1076367390606514615334671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5740626083234744615118245 1076367390606514615334671)
                    ·
                      rfl

theorem cell23_6288654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_6288654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288654 prefixEnd_6288654 := by exact prefixLift 6288654
  have htrace : WordTrace (prefixWord ++ tailWord_6288654) baseStart_6288654 baseEnd_6288654 := by
    simpa [prefixWord, tailWord_6288654, baseEnd_6288654] using wordTrace_append hprefix tailTrace_6288654
  have hstable : (prefixWord ++ tailWord_6288654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288654).length < 2 ^ (prefixWord ++ tailWord_6288654).sum := by decide
  have hdescent : baseEnd_6288654 < baseStart_6288654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288677 : List Nat := [1, 3, 1, 2, 4, 1, 1, 3, 3, 1, 3]
def baseStart_6288677 : Nat := 118140960795 + 6288677 * 2 ^ 59
def prefixEnd_6288677 : Nat := 4983230072969 + 3 ^ 40 * 6288677 * 2
def baseEnd_6288677 : Nat := 3229113981874597256016407

theorem tailTrace_6288677 : CollatzResearch.WordTrace tailWord_6288677 prefixEnd_6288677 3229113981874597256016407 := by
  unfold tailWord_6288677
  simp only [CollatzResearch.WordTrace]
  refine ⟨229366893438204724369568285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152911262292136482913045523 229366893438204724369568285)
  ·
    refine ⟨86012585039326771638588107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229366893438204724369568285 86012585039326771638588107)
    ·
      refine ⟨129018877558990157457882161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86012585039326771638588107 129018877558990157457882161)
      ·
        refine ⟨96764158169242618093411621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129018877558990157457882161 96764158169242618093411621)
        ·
          refine ⟨18143279656732990892514679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96764158169242618093411621 18143279656732990892514679)
          ·
            refine ⟨27214919485099486338772019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18143279656732990892514679 27214919485099486338772019)
            ·
              refine ⟨40822379227649229508158029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27214919485099486338772019 40822379227649229508158029)
              ·
                refine ⟨15308392210368461065559261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40822379227649229508158029 15308392210368461065559261)
                ·
                  refine ⟨5740647078888172899584723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15308392210368461065559261 5740647078888172899584723)
                  ·
                    refine ⟨8610970618332259349377085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5740647078888172899584723 8610970618332259349377085)
                    ·
                      refine ⟨3229113981874597256016407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8610970618332259349377085 3229113981874597256016407)
                      ·
                        rfl

theorem cell23_6288677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_6288677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288677 prefixEnd_6288677 := by exact prefixLift 6288677
  have htrace : WordTrace (prefixWord ++ tailWord_6288677) baseStart_6288677 baseEnd_6288677 := by
    simpa [prefixWord, tailWord_6288677, baseEnd_6288677] using wordTrace_append hprefix tailTrace_6288677
  have hstable : (prefixWord ++ tailWord_6288677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288677).length < 2 ^ (prefixWord ++ tailWord_6288677).sum := by decide
  have hdescent : baseEnd_6288677 < baseStart_6288677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288711 : List Nat := [1, 1, 4, 1, 2, 5, 1, 3, 1, 1, 3]
def baseStart_6288711 : Nat := 118140960795 + 6288711 * 2 ^ 59
def prefixEnd_6288711 : Nat := 4983230072969 + 3 ^ 40 * 6288711 * 2
def baseEnd_6288711 : Nat := 3229131440216850122991251

theorem tailTrace_6288711 : CollatzResearch.WordTrace tailWord_6288711 prefixEnd_6288711 3229131440216850122991251 := by
  unfold tailWord_6288711
  simp only [CollatzResearch.WordTrace]
  refine ⟨229368133520081548176305987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152912089013387698784203991 229368133520081548176305987)
  ·
    refine ⟨344052200280122322264458981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229368133520081548176305987 344052200280122322264458981)
    ·
      refine ⟨64509787552522935424586059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 344052200280122322264458981 64509787552522935424586059)
      ·
        refine ⟨96764681328784403136879089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64509787552522935424586059 96764681328784403136879089)
        ·
          refine ⟨72573510996588302352659317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96764681328784403136879089 72573510996588302352659317)
          ·
            refine ⟨6803766655930153345561811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72573510996588302352659317 6803766655930153345561811)
            ·
              refine ⟨10205649983895230018342717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6803766655930153345561811 10205649983895230018342717)
              ·
                refine ⟨3827118743960711256878519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10205649983895230018342717 3827118743960711256878519)
                ·
                  refine ⟨5740678115941066885317779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3827118743960711256878519 5740678115941066885317779)
                  ·
                    refine ⟨8611017173911600327976669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5740678115941066885317779 8611017173911600327976669)
                    ·
                      refine ⟨3229131440216850122991251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8611017173911600327976669 3229131440216850122991251)
                      ·
                        rfl

theorem cell23_6288711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 3, 1, 1, 3].length) (baseStart_6288711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288711 prefixEnd_6288711 := by exact prefixLift 6288711
  have htrace : WordTrace (prefixWord ++ tailWord_6288711) baseStart_6288711 baseEnd_6288711 := by
    simpa [prefixWord, tailWord_6288711, baseEnd_6288711] using wordTrace_append hprefix tailTrace_6288711
  have hstable : (prefixWord ++ tailWord_6288711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288711).length < 2 ^ (prefixWord ++ tailWord_6288711).sum := by decide
  have hdescent : baseEnd_6288711 < baseStart_6288711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288720 : List Nat := [2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 5]
def baseStart_6288720 : Nat := 118140960795 + 6288720 * 2 ^ 59
def prefixEnd_6288720 : Nat := 4983230072969 + 3 ^ 40 * 6288720 * 2
def baseEnd_6288720 : Nat := 3229136061542740587778709

theorem tailTrace_6288720 : CollatzResearch.WordTrace tailWord_6288720 prefixEnd_6288720 3229136061542740587778709 := by
  unfold tailWord_6288720
  simp only [CollatzResearch.WordTrace]
  refine ⟨114684230888524471356691807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152912307851365961808922409 114684230888524471356691807)
  ·
    refine ⟨172026346332786707035037711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114684230888524471356691807 172026346332786707035037711)
    ·
      refine ⟨258039519499180060552556567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172026346332786707035037711 258039519499180060552556567)
      ·
        refine ⟨387059279248770090828834851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258039519499180060552556567 387059279248770090828834851)
        ·
          refine ⟨580588918873155136243252277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387059279248770090828834851 580588918873155136243252277)
          ·
            refine ⟨54430211144358294022804901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 580588918873155136243252277 54430211144358294022804901)
            ·
              refine ⟨10205664589567180129275919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54430211144358294022804901 10205664589567180129275919)
              ·
                refine ⟨15308496884350770193913879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10205664589567180129275919 15308496884350770193913879)
                ·
                  refine ⟨22962745326526155290870819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15308496884350770193913879 22962745326526155290870819)
                  ·
                    refine ⟨34444117989789232936306229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22962745326526155290870819 34444117989789232936306229)
                    ·
                      refine ⟨3229136061542740587778709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34444117989789232936306229 3229136061542740587778709)
                      ·
                        rfl

theorem cell23_6288720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 5].length) (baseStart_6288720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288720 prefixEnd_6288720 := by exact prefixLift 6288720
  have htrace : WordTrace (prefixWord ++ tailWord_6288720) baseStart_6288720 baseEnd_6288720 := by
    simpa [prefixWord, tailWord_6288720, baseEnd_6288720] using wordTrace_append hprefix tailTrace_6288720
  have hstable : (prefixWord ++ tailWord_6288720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288720).length < 2 ^ (prefixWord ++ tailWord_6288720).sum := by decide
  have hdescent : baseEnd_6288720 < baseStart_6288720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288740 : List Nat := [2, 3, 1, 1, 3, 3, 2, 8]
def baseStart_6288740 : Nat := 118140960795 + 6288740 * 2 ^ 59
def prefixEnd_6288740 : Nat := 4983230072969 + 3 ^ 40 * 6288740 * 2
def baseEnd_6288740 : Nat := 119598012265030759612171

theorem tailTrace_6288740 : CollatzResearch.WordTrace tailWord_6288740 prefixEnd_6288740 119598012265030759612171 := by
  unfold tailWord_6288740
  simp only [CollatzResearch.WordTrace]
  refine ⟨114684595618488243064555837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152912794157984324086074449 114684595618488243064555837)
  ·
    refine ⟨43006723356933091149208439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114684595618488243064555837 43006723356933091149208439)
    ·
      refine ⟨64510085035399636723812659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43006723356933091149208439 64510085035399636723812659)
      ·
        refine ⟨96765127553099455085718989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64510085035399636723812659 96765127553099455085718989)
        ·
          refine ⟨36286922832412295657144621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96765127553099455085718989 36286922832412295657144621)
          ·
            refine ⟨13607596062154610871429233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36286922832412295657144621 13607596062154610871429233)
            ·
              refine ⟨10205697046615958153571925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13607596062154610871429233 10205697046615958153571925)
              ·
                refine ⟨119598012265030759612171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10205697046615958153571925 119598012265030759612171)
                ·
                  rfl

theorem cell23_6288740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 8].length) (baseStart_6288740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288740 prefixEnd_6288740 := by exact prefixLift 6288740
  have htrace : WordTrace (prefixWord ++ tailWord_6288740) baseStart_6288740 baseEnd_6288740 := by
    simpa [prefixWord, tailWord_6288740, baseEnd_6288740] using wordTrace_append hprefix tailTrace_6288740
  have hstable : (prefixWord ++ tailWord_6288740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288740).length < 2 ^ (prefixWord ++ tailWord_6288740).sum := by decide
  have hdescent : baseEnd_6288740 < baseStart_6288740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288744 : List Nat := [2, 1, 4, 2, 3, 1, 1, 3, 2, 4]
def baseStart_6288744 : Nat := 118140960795 + 6288744 * 2 ^ 59
def prefixEnd_6288744 : Nat := 4983230072969 + 3 ^ 40 * 6288744 * 2
def baseEnd_6288744 : Nat := 1076382795026149497959533

theorem tailTrace_6288744 : CollatzResearch.WordTrace tailWord_6288744 prefixEnd_6288744 1076382795026149497959533 := by
  unfold tailWord_6288744
  simp only [CollatzResearch.WordTrace]
  refine ⟨114684668564480997406128643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152912891419307996541504857 114684668564480997406128643)
  ·
    refine ⟨172027002846721496109192965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114684668564480997406128643 172027002846721496109192965)
    ·
      refine ⟨32255063033760280520473681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172027002846721496109192965 32255063033760280520473681)
      ·
        refine ⟨24191297275320210390355261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32255063033760280520473681 24191297275320210390355261)
        ·
          refine ⟨9071736478245078896383223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24191297275320210390355261 9071736478245078896383223)
          ·
            refine ⟨13607604717367618344574835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9071736478245078896383223 13607604717367618344574835)
            ·
              refine ⟨20411407076051427516862253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13607604717367618344574835 20411407076051427516862253)
              ·
                refine ⟨7654277653519285318823345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20411407076051427516862253 7654277653519285318823345)
                ·
                  refine ⟨5740708240139463989117509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7654277653519285318823345 5740708240139463989117509)
                  ·
                    refine ⟨1076382795026149497959533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5740708240139463989117509 1076382795026149497959533)
                    ·
                      rfl

theorem cell23_6288744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_6288744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288744 prefixEnd_6288744 := by exact prefixLift 6288744
  have htrace : WordTrace (prefixWord ++ tailWord_6288744) baseStart_6288744 baseEnd_6288744 := by
    simpa [prefixWord, tailWord_6288744, baseEnd_6288744] using wordTrace_append hprefix tailTrace_6288744
  have hstable : (prefixWord ++ tailWord_6288744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288744).length < 2 ^ (prefixWord ++ tailWord_6288744).sum := by decide
  have hdescent : baseEnd_6288744 < baseStart_6288744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288800 : List Nat := [2, 1, 1, 4, 1, 2, 3, 1, 2, 6]
def baseStart_6288800 : Nat := 118140960795 + 6288800 * 2 ^ 59
def prefixEnd_6288800 : Nat := 4983230072969 + 3 ^ 40 * 6288800 * 2
def baseEnd_6288800 : Nat := 1076392379998366758259447

theorem tailTrace_6288800 : CollatzResearch.WordTrace tailWord_6288800 prefixEnd_6288800 1076392379998366758259447 := by
  unfold tailWord_6288800
  simp only [CollatzResearch.WordTrace]
  refine ⟨114685689808379558188147927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152914253077839410917530569 114685689808379558188147927)
  ·
    refine ⟨172028534712569337282221891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114685689808379558188147927 172028534712569337282221891)
    ·
      refine ⟨258042802068854005923332837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172028534712569337282221891 258042802068854005923332837)
      ·
        refine ⟨48383025387910126110624907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 258042802068854005923332837 48383025387910126110624907)
        ·
          refine ⟨72574538081865189165937361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48383025387910126110624907 72574538081865189165937361)
          ·
            refine ⟨54430903561398891874453021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72574538081865189165937361 54430903561398891874453021)
            ·
              refine ⟨20411588835524584452919883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54430903561398891874453021 20411588835524584452919883)
              ·
                refine ⟨30617383253286876679379825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20411588835524584452919883 30617383253286876679379825)
                ·
                  refine ⟨22963037439965157509534869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30617383253286876679379825 22963037439965157509534869)
                  ·
                    refine ⟨1076392379998366758259447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22963037439965157509534869 1076392379998366758259447)
                    ·
                      rfl

theorem cell23_6288800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 2, 6].length) (baseStart_6288800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288800 prefixEnd_6288800 := by exact prefixLift 6288800
  have htrace : WordTrace (prefixWord ++ tailWord_6288800) baseStart_6288800 baseEnd_6288800 := by
    simpa [prefixWord, tailWord_6288800, baseEnd_6288800] using wordTrace_append hprefix tailTrace_6288800
  have hstable : (prefixWord ++ tailWord_6288800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288800).length < 2 ^ (prefixWord ++ tailWord_6288800).sum := by decide
  have hdescent : baseEnd_6288800 < baseStart_6288800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288830 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 11]
def baseStart_6288830 : Nat := 118140960795 + 6288830 * 2 ^ 59
def prefixEnd_6288830 : Nat := 4983230072969 + 3 ^ 40 * 6288830 * 2
def baseEnd_6288830 : Nat := 358799171601637239711467

theorem tailTrace_6288830 : CollatzResearch.WordTrace tailWord_6288830 prefixEnd_6288830 358799171601637239711467 := by
  unfold tailWord_6288830
  simp only [CollatzResearch.WordTrace]
  refine ⟨28671559225831303937485993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152914982537766954333258629 28671559225831303937485993)
  ·
    refine ⟨21503669419373477953114495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28671559225831303937485993 21503669419373477953114495)
    ·
      refine ⟨32255504129060216929671743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21503669419373477953114495 32255504129060216929671743)
      ·
        refine ⟨48383256193590325394507615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32255504129060216929671743 48383256193590325394507615)
        ·
          refine ⟨72574884290385488091761423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48383256193590325394507615 72574884290385488091761423)
          ·
            refine ⟨108862326435578232137642135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72574884290385488091761423 108862326435578232137642135)
            ·
              refine ⟨163293489653367348206463203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108862326435578232137642135 163293489653367348206463203)
              ·
                refine ⟨244940234480051022309694805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163293489653367348206463203 244940234480051022309694805)
                ·
                  refine ⟨358799171601637239711467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 244940234480051022309694805 358799171601637239711467)
                  ·
                    rfl

theorem cell23_6288830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_6288830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288830 prefixEnd_6288830 := by exact prefixLift 6288830
  have htrace : WordTrace (prefixWord ++ tailWord_6288830) baseStart_6288830 baseEnd_6288830 := by
    simpa [prefixWord, tailWord_6288830, baseEnd_6288830] using wordTrace_append hprefix tailTrace_6288830
  have hstable : (prefixWord ++ tailWord_6288830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288830).length < 2 ^ (prefixWord ++ tailWord_6288830).sum := by decide
  have hdescent : baseEnd_6288830 < baseStart_6288830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288847 : List Nat := [1, 1, 2, 1, 1, 4, 4, 4, 5]
def baseStart_6288847 : Nat := 118140960795 + 6288847 * 2 ^ 59
def prefixEnd_6288847 : Nat := 4983230072969 + 3 ^ 40 * 6288847 * 2
def baseEnd_6288847 : Nat := 358800141509540176765625

theorem tailTrace_6288847 : CollatzResearch.WordTrace tailWord_6288847 prefixEnd_6288847 358800141509540176765625 := by
  unfold tailWord_6288847
  simp only [CollatzResearch.WordTrace]
  refine ⟨229373093847588843403256795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152915395898392562268837863 229373093847588843403256795)
  ·
    refine ⟨344059640771383265104885193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229373093847588843403256795 344059640771383265104885193)
    ·
      refine ⟨258044730578537448828663895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344059640771383265104885193 258044730578537448828663895)
      ·
        refine ⟨387067095867806173242995843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258044730578537448828663895 387067095867806173242995843)
        ·
          refine ⟨580600643801709259864493765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387067095867806173242995843 580600643801709259864493765)
          ·
            refine ⟨108862620712820486224592581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 580600643801709259864493765 108862620712820486224592581)
            ·
              refine ⟨20411741383653841167111109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108862620712820486224592581 20411741383653841167111109)
              ·
                refine ⟨3827201509435095218833333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20411741383653841167111109 3827201509435095218833333)
                ·
                  refine ⟨358800141509540176765625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3827201509435095218833333 358800141509540176765625)
                  ·
                    rfl

theorem cell23_6288847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 4, 5].length) (baseStart_6288847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288847 prefixEnd_6288847 := by exact prefixLift 6288847
  have htrace : WordTrace (prefixWord ++ tailWord_6288847) baseStart_6288847 baseEnd_6288847 := by
    simpa [prefixWord, tailWord_6288847, baseEnd_6288847] using wordTrace_append hprefix tailTrace_6288847
  have hstable : (prefixWord ++ tailWord_6288847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288847).length < 2 ^ (prefixWord ++ tailWord_6288847).sum := by decide
  have hdescent : baseEnd_6288847 < baseStart_6288847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288854 : List Nat := [5, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_6288854 : Nat := 118140960795 + 6288854 * 2 ^ 59
def prefixEnd_6288854 : Nat := 4983230072969 + 3 ^ 40 * 6288854 * 2
def baseEnd_6288854 : Nat := 3229204867950443063503093

theorem tailTrace_6288854 : CollatzResearch.WordTrace tailWord_6288854 prefixEnd_6288854 3229204867950443063503093 := by
  unfold tailWord_6288854
  simp only [CollatzResearch.WordTrace]
  refine ⟨14335834322410217724922601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152915566105708989065841077 14335834322410217724922601)
  ·
    refine ⟨10751875741807663293691951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14335834322410217724922601 10751875741807663293691951)
    ·
      refine ⟨16127813612711494940537927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10751875741807663293691951 16127813612711494940537927)
      ·
        refine ⟨24191720419067242410806891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16127813612711494940537927 24191720419067242410806891)
        ·
          refine ⟨36287580628600863616210337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24191720419067242410806891 36287580628600863616210337)
          ·
            refine ⟨27215685471450647712157753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36287580628600863616210337 27215685471450647712157753)
            ·
              refine ⟨20411764103587985784118315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27215685471450647712157753 20411764103587985784118315)
              ·
                refine ⟨30617646155381978676177473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20411764103587985784118315 30617646155381978676177473)
                ·
                  refine ⟨22963234616536484007133105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30617646155381978676177473 22963234616536484007133105)
                  ·
                    refine ⟨17222425962402363005349829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22963234616536484007133105 17222425962402363005349829)
                    ·
                      refine ⟨3229204867950443063503093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17222425962402363005349829 3229204867950443063503093)
                      ·
                        rfl

theorem cell23_6288854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_6288854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288854 prefixEnd_6288854 := by exact prefixLift 6288854
  have htrace : WordTrace (prefixWord ++ tailWord_6288854) baseStart_6288854 baseEnd_6288854 := by
    simpa [prefixWord, tailWord_6288854, baseEnd_6288854] using wordTrace_append hprefix tailTrace_6288854
  have hstable : (prefixWord ++ tailWord_6288854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288854).length < 2 ^ (prefixWord ++ tailWord_6288854).sum := by decide
  have hdescent : baseEnd_6288854 < baseStart_6288854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288857 : List Nat := [1, 2, 1, 2, 4, 2, 2, 1, 2, 3, 3]
def baseStart_6288857 : Nat := 118140960795 + 6288857 * 2 ^ 59
def prefixEnd_6288857 : Nat := 4983230072969 + 3 ^ 40 * 6288857 * 2
def baseEnd_6288857 : Nat := 3229206408392406551765579

theorem tailTrace_6288857 : CollatzResearch.WordTrace tailWord_6288857 prefixEnd_6288857 3229206408392406551765579 := by
  unfold tailWord_6288857
  simp only [CollatzResearch.WordTrace]
  refine ⟨229373458577552615111120825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152915639051701743407413883 229373458577552615111120825)
  ·
    refine ⟨172030093933164461333340619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229373458577552615111120825 172030093933164461333340619)
    ·
      refine ⟨258045140899746692000010929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172030093933164461333340619 258045140899746692000010929)
      ·
        refine ⟨193533855674810019000008197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258045140899746692000010929 193533855674810019000008197)
        ·
          refine ⟨36287597939026878562501537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193533855674810019000008197 36287597939026878562501537)
          ·
            refine ⟨27215698454270158921876153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36287597939026878562501537 27215698454270158921876153)
            ·
              refine ⟨20411773840702619191407115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27215698454270158921876153 20411773840702619191407115)
              ·
                refine ⟨30617660761053928787110673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20411773840702619191407115 30617660761053928787110673)
                ·
                  refine ⟨22963245570790446590333005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30617660761053928787110673 22963245570790446590333005)
                  ·
                    refine ⟨8611217089046417471374877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22963245570790446590333005 8611217089046417471374877)
                    ·
                      refine ⟨3229206408392406551765579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8611217089046417471374877 3229206408392406551765579)
                      ·
                        rfl

theorem cell23_6288857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 3, 3].length) (baseStart_6288857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288857 prefixEnd_6288857 := by exact prefixLift 6288857
  have htrace : WordTrace (prefixWord ++ tailWord_6288857) baseStart_6288857 baseEnd_6288857 := by
    simpa [prefixWord, tailWord_6288857, baseEnd_6288857] using wordTrace_append hprefix tailTrace_6288857
  have hstable : (prefixWord ++ tailWord_6288857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288857).length < 2 ^ (prefixWord ++ tailWord_6288857).sum := by decide
  have hdescent : baseEnd_6288857 < baseStart_6288857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288858 : List Nat := [3, 1, 1, 2, 3, 3, 3, 1, 2, 2, 2]
def baseStart_6288858 : Nat := 118140960795 + 6288858 * 2 ^ 59
def prefixEnd_6288858 : Nat := 4983230072969 + 3 ^ 40 * 6288858 * 2
def baseEnd_6288858 : Nat := 3229206921873061047853075

theorem tailTrace_6288858 : CollatzResearch.WordTrace tailWord_6288858 prefixEnd_6288858 3229206921873061047853075 := by
  unfold tailWord_6288858
  simp only [CollatzResearch.WordTrace]
  refine ⟨57343373762637248070476807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152915663367032661521271485 57343373762637248070476807)
  ·
    refine ⟨86015060643955872105715211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57343373762637248070476807 86015060643955872105715211)
    ·
      refine ⟨129022590965933808158572817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86015060643955872105715211 129022590965933808158572817)
      ·
        refine ⟨96766943224450356118929613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129022590965933808158572817 96766943224450356118929613)
        ·
          refine ⟨36287603709168883544598605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96766943224450356118929613 36287603709168883544598605)
          ·
            refine ⟨13607851390938331329224477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36287603709168883544598605 13607851390938331329224477)
            ·
              refine ⟨5102944271601874248459179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13607851390938331329224477 5102944271601874248459179)
              ·
                refine ⟨7654416407402811372688769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5102944271601874248459179 7654416407402811372688769)
                ·
                  refine ⟨5740812305552108529516577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7654416407402811372688769 5740812305552108529516577)
                  ·
                    refine ⟨4305609229164081397137433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5740812305552108529516577 4305609229164081397137433)
                    ·
                      refine ⟨3229206921873061047853075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4305609229164081397137433 3229206921873061047853075)
                      ·
                        rfl

theorem cell23_6288858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 2, 2, 2].length) (baseStart_6288858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288858 prefixEnd_6288858 := by exact prefixLift 6288858
  have htrace : WordTrace (prefixWord ++ tailWord_6288858) baseStart_6288858 baseEnd_6288858 := by
    simpa [prefixWord, tailWord_6288858, baseEnd_6288858] using wordTrace_append hprefix tailTrace_6288858
  have hstable : (prefixWord ++ tailWord_6288858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288858).length < 2 ^ (prefixWord ++ tailWord_6288858).sum := by decide
  have hdescent : baseEnd_6288858 < baseStart_6288858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288898 : List Nat := [3, 4, 1, 2, 1, 2, 3, 2, 5]
def baseStart_6288898 : Nat := 118140960795 + 6288898 * 2 ^ 59
def prefixEnd_6288898 : Nat := 4983230072969 + 3 ^ 40 * 6288898 * 2
def baseEnd_6288898 : Nat := 358803051233248987928099

theorem tailTrace_6288898 : CollatzResearch.WordTrace tailWord_6288898 prefixEnd_6288898 358803051233248987928099 := by
  unfold tailWord_6288898
  simp only [CollatzResearch.WordTrace]
  refine ⟨57343738492601019778340837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152916635980269386075575565 57343738492601019778340837)
  ·
    refine ⟨10751950967362691208438907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57343738492601019778340837 10751950967362691208438907)
    ·
      refine ⟨16127926451044036812658361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10751950967362691208438907 16127926451044036812658361)
      ·
        refine ⟨12095944838283027609493771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16127926451044036812658361 12095944838283027609493771)
        ·
          refine ⟨18143917257424541414240657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12095944838283027609493771 18143917257424541414240657)
          ·
            refine ⟨13607937943068406060680493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18143917257424541414240657 13607937943068406060680493)
            ·
              refine ⟨5102976728650652272755185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13607937943068406060680493 5102976728650652272755185)
              ·
                refine ⟨3827232546487989204566389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5102976728650652272755185 3827232546487989204566389)
                ·
                  refine ⟨358803051233248987928099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3827232546487989204566389 358803051233248987928099)
                  ·
                    rfl

theorem cell23_6288898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_6288898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288898 prefixEnd_6288898 := by exact prefixLift 6288898
  have htrace : WordTrace (prefixWord ++ tailWord_6288898) baseStart_6288898 baseEnd_6288898 := by
    simpa [prefixWord, tailWord_6288898, baseEnd_6288898] using wordTrace_append hprefix tailTrace_6288898
  have hstable : (prefixWord ++ tailWord_6288898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288898).length < 2 ^ (prefixWord ++ tailWord_6288898).sum := by decide
  have hdescent : baseEnd_6288898 < baseStart_6288898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288909 : List Nat := [1, 7, 1, 1, 2, 2, 2, 1, 2, 2, 2]
def baseStart_6288909 : Nat := 118140960795 + 6288909 * 2 ^ 59
def prefixEnd_6288909 : Nat := 4983230072969 + 3 ^ 40 * 6288909 * 2
def baseEnd_6288909 : Nat := 3229233109386440348315341

theorem tailTrace_6288909 : CollatzResearch.WordTrace tailWord_6288909 prefixEnd_6288909 3229233109386440348315341 := by
  unfold tailWord_6288909
  simp only [CollatzResearch.WordTrace]
  refine ⟨229375355173364227992013781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152916903448909485328009187 229375355173364227992013781)
  ·
    refine ⟨5375984886875724093562823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 229375355173364227992013781 5375984886875724093562823)
    ·
      refine ⟨8063977330313586140344235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5375984886875724093562823 8063977330313586140344235)
      ·
        refine ⟨12095965995470379210516353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8063977330313586140344235 12095965995470379210516353)
        ·
          refine ⟨9071974496602784407887265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12095965995470379210516353 9071974496602784407887265)
          ·
            refine ⟨6803980872452088305915449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9071974496602784407887265 6803980872452088305915449)
            ·
              refine ⟨5102985654339066229436587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6803980872452088305915449 5102985654339066229436587)
              ·
                refine ⟨7654478481508599344154881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5102985654339066229436587 7654478481508599344154881)
                ·
                  refine ⟨5740858861131449508116161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7654478481508599344154881 5740858861131449508116161)
                  ·
                    refine ⟨4305644145848587131087121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5740858861131449508116161 4305644145848587131087121)
                    ·
                      refine ⟨3229233109386440348315341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4305644145848587131087121 3229233109386440348315341)
                      ·
                        rfl

theorem cell23_6288909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_6288909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288909 prefixEnd_6288909 := by exact prefixLift 6288909
  have htrace : WordTrace (prefixWord ++ tailWord_6288909) baseStart_6288909 baseEnd_6288909 := by
    simpa [prefixWord, tailWord_6288909, baseEnd_6288909] using wordTrace_append hprefix tailTrace_6288909
  have hstable : (prefixWord ++ tailWord_6288909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288909).length < 2 ^ (prefixWord ++ tailWord_6288909).sum := by decide
  have hdescent : baseEnd_6288909 < baseStart_6288909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288940 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 8]
def baseStart_6288940 : Nat := 118140960795 + 6288940 * 2 ^ 59
def prefixEnd_6288940 : Nat := 4983230072969 + 3 ^ 40 * 6288940 * 2
def baseEnd_6288940 : Nat := 3229249027286729727027697

theorem tailTrace_6288940 : CollatzResearch.WordTrace tailWord_6288940 prefixEnd_6288940 3229249027286729727027697 := by
  unfold tailWord_6288940
  simp only [CollatzResearch.WordTrace]
  refine ⟨114688242918125960143196137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152917657224167946857594849 114688242918125960143196137)
  ·
    refine ⟨86016182188594470107397103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114688242918125960143196137 86016182188594470107397103)
    ·
      refine ⟨129024273282891705161095655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86016182188594470107397103 129024273282891705161095655)
      ·
        refine ⟨193536409924337557741643483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129024273282891705161095655 193536409924337557741643483)
        ·
          refine ⟨290304614886506336612465225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193536409924337557741643483 290304614886506336612465225)
          ·
            refine ⟨217728461164879752459348919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290304614886506336612465225 217728461164879752459348919)
            ·
              refine ⟨326592691747319628689023379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217728461164879752459348919 326592691747319628689023379)
              ·
                refine ⟨489889037620979443033535069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 326592691747319628689023379 489889037620979443033535069)
                ·
                  refine ⟨183708389107867291137575651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 489889037620979443033535069 183708389107867291137575651)
                  ·
                    refine ⟨275562583661800936706363477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 183708389107867291137575651 275562583661800936706363477)
                    ·
                      refine ⟨3229249027286729727027697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 275562583661800936706363477 3229249027286729727027697)
                      ·
                        rfl

theorem cell23_6288940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_6288940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288940 prefixEnd_6288940 := by exact prefixLift 6288940
  have htrace : WordTrace (prefixWord ++ tailWord_6288940) baseStart_6288940 baseEnd_6288940 := by
    simpa [prefixWord, tailWord_6288940, baseEnd_6288940] using wordTrace_append hprefix tailTrace_6288940
  have hstable : (prefixWord ++ tailWord_6288940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288940).length < 2 ^ (prefixWord ++ tailWord_6288940).sum := by decide
  have hdescent : baseEnd_6288940 < baseStart_6288940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288974 : List Nat := [4, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2]
def baseStart_6288974 : Nat := 118140960795 + 6288974 * 2 ^ 59
def prefixEnd_6288974 : Nat := 4983230072969 + 3 ^ 40 * 6288974 * 2
def baseEnd_6288974 : Nat := 3229266485628982594002541

theorem tailTrace_6288974 : CollatzResearch.WordTrace tailWord_6288974 prefixEnd_6288974 3229266485628982594002541 := by
  unfold tailWord_6288974
  simp only [CollatzResearch.WordTrace]
  refine ⟨28672215739766093011641247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152918483945419162728753317 28672215739766093011641247)
  ·
    refine ⟨43008323609649139517461871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28672215739766093011641247 43008323609649139517461871)
    ·
      refine ⟨64512485414473709276192807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43008323609649139517461871 64512485414473709276192807)
      ·
        refine ⟨96768728121710563914289211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64512485414473709276192807 96768728121710563914289211)
        ·
          refine ⟨145153092182565845871433817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96768728121710563914289211 145153092182565845871433817)
          ·
            refine ⟨108864819136924384403575363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145153092182565845871433817 108864819136924384403575363)
            ·
              refine ⟨163297228705386576605363045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108864819136924384403575363 163297228705386576605363045)
              ·
                refine ⟨30618230382259983113505571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163297228705386576605363045 30618230382259983113505571)
                ·
                  refine ⟨45927345573389974670258357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30618230382259983113505571 45927345573389974670258357)
                  ·
                    refine ⟨4305688647505310125336721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45927345573389974670258357 4305688647505310125336721)
                    ·
                      refine ⟨3229266485628982594002541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4305688647505310125336721 3229266485628982594002541)
                      ·
                        rfl

theorem cell23_6288974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2].length) (baseStart_6288974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288974 prefixEnd_6288974 := by exact prefixLift 6288974
  have htrace : WordTrace (prefixWord ++ tailWord_6288974) baseStart_6288974 baseEnd_6288974 := by
    simpa [prefixWord, tailWord_6288974, baseEnd_6288974] using wordTrace_append hprefix tailTrace_6288974
  have hstable : (prefixWord ++ tailWord_6288974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288974).length < 2 ^ (prefixWord ++ tailWord_6288974).sum := by decide
  have hdescent : baseEnd_6288974 < baseStart_6288974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6288982 : List Nat := [5, 2, 2, 2, 2, 1, 1, 1, 2, 1, 4]
def baseStart_6288982 : Nat := 118140960795 + 6288982 * 2 ^ 59
def prefixEnd_6288982 : Nat := 4983230072969 + 3 ^ 40 * 6288982 * 2
def baseEnd_6288982 : Nat := 3229270593474218562702505

theorem tailTrace_6288982 : CollatzResearch.WordTrace tailWord_6288982 prefixEnd_6288982 3229270593474218562702505 := by
  unfold tailWord_6288982
  simp only [CollatzResearch.WordTrace]
  refine ⟨14336126106381235091213825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152918678468066507639614133 14336126106381235091213825)
  ·
    refine ⟨10752094579785926318410369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14336126106381235091213825 10752094579785926318410369)
    ·
      refine ⟨8064070934839444738807777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10752094579785926318410369 8064070934839444738807777)
      ·
        refine ⟨6048053201129583554105833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8064070934839444738807777 6048053201129583554105833)
        ·
          refine ⟨4536039900847187665579375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6048053201129583554105833 4536039900847187665579375)
          ·
            refine ⟨6804059851270781498369063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4536039900847187665579375 6804059851270781498369063)
            ·
              refine ⟨10206089776906172247553595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6804059851270781498369063 10206089776906172247553595)
              ·
                refine ⟨15309134665359258371330393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10206089776906172247553595 15309134665359258371330393)
                ·
                  refine ⟨11481850999019443778497795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15309134665359258371330393 11481850999019443778497795)
                  ·
                    refine ⟨17222776498529165667746693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11481850999019443778497795 17222776498529165667746693)
                    ·
                      refine ⟨3229270593474218562702505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17222776498529165667746693 3229270593474218562702505)
                      ·
                        rfl

theorem cell23_6288982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_6288982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6288982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6288982 prefixEnd_6288982 := by exact prefixLift 6288982
  have htrace : WordTrace (prefixWord ++ tailWord_6288982) baseStart_6288982 baseEnd_6288982 := by
    simpa [prefixWord, tailWord_6288982, baseEnd_6288982] using wordTrace_append hprefix tailTrace_6288982
  have hstable : (prefixWord ++ tailWord_6288982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6288982).length < 2 ^ (prefixWord ++ tailWord_6288982).sum := by decide
  have hdescent : baseEnd_6288982 < baseStart_6288982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6288982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289007 : List Nat := [1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 5]
def baseStart_6289007 : Nat := 118140960795 + 6289007 * 2 ^ 59
def prefixEnd_6289007 : Nat := 4983230072969 + 3 ^ 40 * 6289007 * 2
def baseEnd_6289007 : Nat := 3229283430490580964889889

theorem tailTrace_6289007 : CollatzResearch.WordTrace tailWord_6289007 prefixEnd_6289007 3229283430490580964889889 := by
  unfold tailWord_6289007
  simp only [CollatzResearch.WordTrace]
  refine ⟨229378929527009190729081275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152919286351339460486054183 229378929527009190729081275)
  ·
    refine ⟨344068394290513786093621913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229378929527009190729081275 344068394290513786093621913)
    ·
      refine ⟨258051295717885339570216435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344068394290513786093621913 258051295717885339570216435)
      ·
        refine ⟨387076943576828009355324653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258051295717885339570216435 387076943576828009355324653)
        ·
          refine ⟨145153853841310503508246745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 387076943576828009355324653 145153853841310503508246745)
          ·
            refine ⟨108865390380982877631185059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145153853841310503508246745 108865390380982877631185059)
            ·
              refine ⟨163298085571474316446777589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108865390380982877631185059 163298085571474316446777589)
              ·
                refine ⟨15309195522325717166885399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 163298085571474316446777589 15309195522325717166885399)
                ·
                  refine ⟨22963793283488575750328099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15309195522325717166885399 22963793283488575750328099)
                  ·
                    refine ⟨34445689925232863625492149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22963793283488575750328099 34445689925232863625492149)
                    ·
                      refine ⟨3229283430490580964889889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34445689925232863625492149 3229283430490580964889889)
                      ·
                        rfl

theorem cell23_6289007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 5].length) (baseStart_6289007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289007 prefixEnd_6289007 := by exact prefixLift 6289007
  have htrace : WordTrace (prefixWord ++ tailWord_6289007) baseStart_6289007 baseEnd_6289007 := by
    simpa [prefixWord, tailWord_6289007, baseEnd_6289007] using wordTrace_append hprefix tailTrace_6289007
  have hstable : (prefixWord ++ tailWord_6289007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289007).length < 2 ^ (prefixWord ++ tailWord_6289007).sum := by decide
  have hdescent : baseEnd_6289007 < baseStart_6289007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289017 : List Nat := [1, 2, 1, 3, 3, 1, 2, 2, 1, 1, 6]
def baseStart_6289017 : Nat := 118140960795 + 6289017 * 2 ^ 59
def prefixEnd_6289017 : Nat := 4983230072969 + 3 ^ 40 * 6289017 * 2
def baseEnd_6289017 : Nat := 3229288565297125925764843

theorem tailTrace_6289017 : CollatzResearch.WordTrace tailWord_6289017 prefixEnd_6289017 3229288565297125925764843 := by
  unfold tailWord_6289017
  simp only [CollatzResearch.WordTrace]
  refine ⟨229379294256972962436945305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152919529504648641624630203 229379294256972962436945305)
  ·
    refine ⟨172034470692729721827708979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229379294256972962436945305 172034470692729721827708979)
    ·
      refine ⟨258051706039094582741563469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172034470692729721827708979 258051706039094582741563469)
      ·
        refine ⟨96769389764660468528086301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258051706039094582741563469 96769389764660468528086301)
        ·
          refine ⟨36288521161747675698032363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96769389764660468528086301 36288521161747675698032363)
          ·
            refine ⟨54432781742621513547048545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36288521161747675698032363 54432781742621513547048545)
            ·
              refine ⟨40824586306966135160286409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54432781742621513547048545 40824586306966135160286409)
              ·
                refine ⟨30618439730224601370214807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40824586306966135160286409 30618439730224601370214807)
                ·
                  refine ⟨45927659595336902055322211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30618439730224601370214807 45927659595336902055322211)
                  ·
                    refine ⟨68891489393005353082983317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45927659595336902055322211 68891489393005353082983317)
                    ·
                      refine ⟨3229288565297125925764843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68891489393005353082983317 3229288565297125925764843)
                      ·
                        rfl

theorem cell23_6289017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_6289017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289017 prefixEnd_6289017 := by exact prefixLift 6289017
  have htrace : WordTrace (prefixWord ++ tailWord_6289017) baseStart_6289017 baseEnd_6289017 := by
    simpa [prefixWord, tailWord_6289017, baseEnd_6289017] using wordTrace_append hprefix tailTrace_6289017
  have hstable : (prefixWord ++ tailWord_6289017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289017).length < 2 ^ (prefixWord ++ tailWord_6289017).sum := by decide
  have hdescent : baseEnd_6289017 < baseStart_6289017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289034 : List Nat := [3, 1, 2, 3, 2, 2, 1, 1, 1, 1, 6]
def baseStart_6289034 : Nat := 118140960795 + 6289034 * 2 ^ 59
def prefixEnd_6289034 : Nat := 4983230072969 + 3 ^ 40 * 6289034 * 2
def baseEnd_6289034 : Nat := 3229297294468252359252265

theorem tailTrace_6289034 : CollatzResearch.WordTrace tailWord_6289034 prefixEnd_6289034 3229297294468252359252265 := by
  unfold tailWord_6289034
  simp only [CollatzResearch.WordTrace]
  refine ⟨57344978574477843585078539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152919942865274249560209437 57344978574477843585078539)
  ·
    refine ⟨86017467861716765377617809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57344978574477843585078539 86017467861716765377617809)
    ·
      refine ⟨64513100896287574033213357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86017467861716765377617809 64513100896287574033213357)
      ·
        refine ⟨24192412836107840262455009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64513100896287574033213357 24192412836107840262455009)
        ·
          refine ⟨18144309627080880196841257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24192412836107840262455009 18144309627080880196841257)
          ·
            refine ⟨13608232220310660147630943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18144309627080880196841257 13608232220310660147630943)
            ·
              refine ⟨20412348330465990221446415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13608232220310660147630943 20412348330465990221446415)
              ·
                refine ⟨30618522495698985332169623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20412348330465990221446415 30618522495698985332169623)
                ·
                  refine ⟨45927783743548477998254435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30618522495698985332169623 45927783743548477998254435)
                  ·
                    refine ⟨68891675615322716997381653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45927783743548477998254435 68891675615322716997381653)
                    ·
                      refine ⟨3229297294468252359252265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68891675615322716997381653 3229297294468252359252265)
                      ·
                        rfl

theorem cell23_6289034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_6289034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289034 prefixEnd_6289034 := by exact prefixLift 6289034
  have htrace : WordTrace (prefixWord ++ tailWord_6289034) baseStart_6289034 baseEnd_6289034 := by
    simpa [prefixWord, tailWord_6289034, baseEnd_6289034] using wordTrace_append hprefix tailTrace_6289034
  have hstable : (prefixWord ++ tailWord_6289034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289034).length < 2 ^ (prefixWord ++ tailWord_6289034).sum := by decide
  have hdescent : baseEnd_6289034 < baseStart_6289034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289038 : List Nat := [4, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2]
def baseStart_6289038 : Nat := 118140960795 + 6289038 * 2 ^ 59
def prefixEnd_6289038 : Nat := 4983230072969 + 3 ^ 40 * 6289038 * 2
def baseEnd_6289038 : Nat := 3229299348390870343602247

theorem tailTrace_6289038 : CollatzResearch.WordTrace tailWord_6289038 prefixEnd_6289038 3229299348390870343602247 := by
  unfold tailWord_6289038
  simp only [CollatzResearch.WordTrace]
  refine ⟨28672507523737110377932471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152920040126597922015639845 28672507523737110377932471)
  ·
    refine ⟨43008761285605665566898707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28672507523737110377932471 43008761285605665566898707)
    ·
      refine ⟨64513141928408498350348061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43008761285605665566898707 64513141928408498350348061)
      ·
        refine ⟨24192428223153186881380523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64513141928408498350348061 24192428223153186881380523)
        ·
          refine ⟨36288642334729780322070785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24192428223153186881380523 36288642334729780322070785)
          ·
            refine ⟨27216481751047335241553089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36288642334729780322070785 27216481751047335241553089)
            ·
              refine ⟨20412361313285501431164817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27216481751047335241553089 20412361313285501431164817)
              ·
                refine ⟨15309270984964126073373613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20412361313285501431164817 15309270984964126073373613)
                ·
                  refine ⟨5740976619361547277515105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15309270984964126073373613 5740976619361547277515105)
                  ·
                    refine ⟨4305732464521160458136329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5740976619361547277515105 4305732464521160458136329)
                    ·
                      refine ⟨3229299348390870343602247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4305732464521160458136329 3229299348390870343602247)
                      ·
                        rfl

theorem cell23_6289038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_6289038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289038 prefixEnd_6289038 := by exact prefixLift 6289038
  have htrace : WordTrace (prefixWord ++ tailWord_6289038) baseStart_6289038 baseEnd_6289038 := by
    simpa [prefixWord, tailWord_6289038, baseEnd_6289038] using wordTrace_append hprefix tailTrace_6289038
  have hstable : (prefixWord ++ tailWord_6289038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289038).length < 2 ^ (prefixWord ++ tailWord_6289038).sum := by decide
  have hdescent : baseEnd_6289038 < baseStart_6289038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289058 : List Nat := [3, 3, 1, 4, 1, 1, 2, 1, 1, 1, 5]
def baseStart_6289058 : Nat := 118140960795 + 6289058 * 2 ^ 59
def prefixEnd_6289058 : Nat := 4983230072969 + 3 ^ 40 * 6289058 * 2
def baseEnd_6289058 : Nat := 3229309618003960265352155

theorem tailTrace_6289058 : CollatzResearch.WordTrace tailWord_6289058 prefixEnd_6289058 3229309618003960265352155 := by
  unfold tailWord_6289058
  simp only [CollatzResearch.WordTrace]
  refine ⟨57345197412456106609796957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152920526433216284292791885 57345197412456106609796957)
  ·
    refine ⟨21504449029671039978673859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57345197412456106609796957 21504449029671039978673859)
    ·
      refine ⟨32256673544506559968010789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21504449029671039978673859 32256673544506559968010789)
      ·
        refine ⟨6048126289594979994002023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32256673544506559968010789 6048126289594979994002023)
        ·
          refine ⟨9072189434392469991003035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6048126289594979994002023 9072189434392469991003035)
          ·
            refine ⟨13608284151588704986504553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9072189434392469991003035 13608284151588704986504553)
            ·
              refine ⟨10206213113691528739878415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13608284151588704986504553 10206213113691528739878415)
              ·
                refine ⟨15309319670537293109817623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10206213113691528739878415 15309319670537293109817623)
                ·
                  refine ⟨22963979505805939664726435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15309319670537293109817623 22963979505805939664726435)
                  ·
                    refine ⟨34445969258708909497089653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22963979505805939664726435 34445969258708909497089653)
                    ·
                      refine ⟨3229309618003960265352155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34445969258708909497089653 3229309618003960265352155)
                      ·
                        rfl

theorem cell23_6289058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_6289058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289058 prefixEnd_6289058 := by exact prefixLift 6289058
  have htrace : WordTrace (prefixWord ++ tailWord_6289058) baseStart_6289058 baseEnd_6289058 := by
    simpa [prefixWord, tailWord_6289058, baseEnd_6289058] using wordTrace_append hprefix tailTrace_6289058
  have hstable : (prefixWord ++ tailWord_6289058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289058).length < 2 ^ (prefixWord ++ tailWord_6289058).sum := by decide
  have hdescent : baseEnd_6289058 < baseStart_6289058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289071 : List Nat := [1, 1, 2, 1, 2, 4, 2, 4, 2, 1, 3]
def baseStart_6289071 : Nat := 118140960795 + 6289071 * 2 ^ 59
def prefixEnd_6289071 : Nat := 4983230072969 + 3 ^ 40 * 6289071 * 2
def baseEnd_6289071 : Nat := 3229316293252468714489595

theorem tailTrace_6289071 : CollatzResearch.WordTrace tailWord_6289071 prefixEnd_6289071 3229316293252468714489595 := by
  unfold tailWord_6289071
  simp only [CollatzResearch.WordTrace]
  refine ⟨229381263798777329659411067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152920842532518219772940711 229381263798777329659411067)
  ·
    refine ⟨344071895698165994489116601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229381263798777329659411067 344071895698165994489116601)
    ·
      refine ⟨258053921773624495866837451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344071895698165994489116601 258053921773624495866837451)
      ·
        refine ⟨387080882660436743800256177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258053921773624495866837451 387080882660436743800256177)
        ·
          refine ⟨290310661995327557850192133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387080882660436743800256177 290310661995327557850192133)
          ·
            refine ⟨54433249124123917096911025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 290310661995327557850192133 54433249124123917096911025)
            ·
              refine ⟨40824936843092937822683269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54433249124123917096911025 40824936843092937822683269)
              ·
                refine ⟨7654675658079925841753113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40824936843092937822683269 7654675658079925841753113)
                ·
                  refine ⟨5741006743559944381314835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7654675658079925841753113 5741006743559944381314835)
                  ·
                    refine ⟨8611510115339916571972253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5741006743559944381314835 8611510115339916571972253)
                    ·
                      refine ⟨3229316293252468714489595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8611510115339916571972253 3229316293252468714489595)
                      ·
                        rfl

theorem cell23_6289071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 2, 1, 3].length) (baseStart_6289071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289071 prefixEnd_6289071 := by exact prefixLift 6289071
  have htrace : WordTrace (prefixWord ++ tailWord_6289071) baseStart_6289071 baseEnd_6289071 := by
    simpa [prefixWord, tailWord_6289071, baseEnd_6289071] using wordTrace_append hprefix tailTrace_6289071
  have hstable : (prefixWord ++ tailWord_6289071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289071).length < 2 ^ (prefixWord ++ tailWord_6289071).sum := by decide
  have hdescent : baseEnd_6289071 < baseStart_6289071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289087 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 1, 8]
def baseStart_6289087 : Nat := 118140960795 + 6289087 * 2 ^ 59
def prefixEnd_6289087 : Nat := 4983230072969 + 3 ^ 40 * 6289087 * 2
def baseEnd_6289087 : Nat := 1076441502980980217296507

theorem tailTrace_6289087 : CollatzResearch.WordTrace tailWord_6289087 prefixEnd_6289087 1076441502980980217296507 := by
  unfold tailWord_6289087
  simp only [CollatzResearch.WordTrace]
  refine ⟨229381847366719364391993515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152921231577812909594662343 229381847366719364391993515)
  ·
    refine ⟨344072771050079046587990273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229381847366719364391993515 344072771050079046587990273)
    ·
      refine ⟨258054578287559284940992705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344072771050079046587990273 258054578287559284940992705)
      ·
        refine ⟨193540933715669463705744529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258054578287559284940992705 193540933715669463705744529)
        ·
          refine ⟨145155700286752097779308397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193540933715669463705744529 145155700286752097779308397)
          ·
            refine ⟨54433387607532036667240649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145155700286752097779308397 54433387607532036667240649)
            ·
              refine ⟨40825040705649027500430487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54433387607532036667240649 40825040705649027500430487)
              ·
                refine ⟨61237561058473541250645731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40825040705649027500430487 61237561058473541250645731)
                ·
                  refine ⟨91856341587710311875968597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61237561058473541250645731 91856341587710311875968597)
                  ·
                    refine ⟨1076441502980980217296507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 91856341587710311875968597 1076441502980980217296507)
                    ·
                      rfl

theorem cell23_6289087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 8].length) (baseStart_6289087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289087 prefixEnd_6289087 := by exact prefixLift 6289087
  have htrace : WordTrace (prefixWord ++ tailWord_6289087) baseStart_6289087 baseEnd_6289087 := by
    simpa [prefixWord, tailWord_6289087, baseEnd_6289087] using wordTrace_append hprefix tailTrace_6289087
  have hstable : (prefixWord ++ tailWord_6289087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289087).length < 2 ^ (prefixWord ++ tailWord_6289087).sum := by decide
  have hdescent : baseEnd_6289087 < baseStart_6289087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289098 : List Nat := [3, 1, 2, 1, 5, 1, 1, 1, 3, 3, 2]
def baseStart_6289098 : Nat := 118140960795 + 6289098 * 2 ^ 59
def prefixEnd_6289098 : Nat := 4983230072969 + 3 ^ 40 * 6289098 * 2
def baseEnd_6289098 : Nat := 3229330157230140108851971

theorem tailTrace_6289098 : CollatzResearch.WordTrace tailWord_6289098 prefixEnd_6289098 3229330157230140108851971 := by
  unfold tailWord_6289098
  simp only [CollatzResearch.WordTrace]
  refine ⟨57345562142419878317660987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152921499046453008847095965 57345562142419878317660987)
  ·
    refine ⟨86018343213629817476491481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57345562142419878317660987 86018343213629817476491481)
    ·
      refine ⟨64513757410222363107368611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86018343213629817476491481 64513757410222363107368611)
      ·
        refine ⟨96770636115333544661052917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64513757410222363107368611 96770636115333544661052917)
        ·
          refine ⟨9072247135812519811973711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96770636115333544661052917 9072247135812519811973711)
          ·
            refine ⟨13608370703718779717960567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9072247135812519811973711 13608370703718779717960567)
            ·
              refine ⟨20412556055578169576940851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13608370703718779717960567 20412556055578169576940851)
              ·
                refine ⟨30618834083367254365411277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20412556055578169576940851 30618834083367254365411277)
                ·
                  refine ⟨11482062781262720387029229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30618834083367254365411277 11482062781262720387029229)
                  ·
                    refine ⟨4305773542973520145135961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11482062781262720387029229 4305773542973520145135961)
                    ·
                      refine ⟨3229330157230140108851971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4305773542973520145135961 3229330157230140108851971)
                      ·
                        rfl

theorem cell23_6289098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 3, 3, 2].length) (baseStart_6289098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289098 prefixEnd_6289098 := by exact prefixLift 6289098
  have htrace : WordTrace (prefixWord ++ tailWord_6289098) baseStart_6289098 baseEnd_6289098 := by
    simpa [prefixWord, tailWord_6289098, baseEnd_6289098] using wordTrace_append hprefix tailTrace_6289098
  have hstable : (prefixWord ++ tailWord_6289098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289098).length < 2 ^ (prefixWord ++ tailWord_6289098).sum := by decide
  have hdescent : baseEnd_6289098 < baseStart_6289098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289111 : List Nat := [1, 1, 3, 2, 1, 3, 3, 2, 1, 4, 2]
def baseStart_6289111 : Nat := 118140960795 + 6289111 * 2 ^ 59
def prefixEnd_6289111 : Nat := 4983230072969 + 3 ^ 40 * 6289111 * 2
def baseEnd_6289111 : Nat := 3229336832478648557989411

theorem tailTrace_6289111 : CollatzResearch.WordTrace tailWord_6289111 prefixEnd_6289111 3229336832478648557989411 := by
  unfold tailWord_6289111
  simp only [CollatzResearch.WordTrace]
  refine ⟨229382722718632416490867187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152921815145754944327244791 229382722718632416490867187)
  ·
    refine ⟨344074084077948624736300781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229382722718632416490867187 344074084077948624736300781)
    ·
      refine ⟨129027781529230734276112793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344074084077948624736300781 129027781529230734276112793)
      ·
        refine ⟨96770836146923050707084595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129027781529230734276112793 96770836146923050707084595)
        ·
          refine ⟨145156254220384576060626893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96770836146923050707084595 145156254220384576060626893)
          ·
            refine ⟨54433595332644216022735085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145156254220384576060626893 54433595332644216022735085)
            ·
              refine ⟨20412598249741581008525657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54433595332644216022735085 20412598249741581008525657)
              ·
                refine ⟨15309448687306185756394243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20412598249741581008525657 15309448687306185756394243)
                ·
                  refine ⟨22964173030959278634591365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15309448687306185756394243 22964173030959278634591365)
                  ·
                    refine ⟨4305782443304864743985881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22964173030959278634591365 4305782443304864743985881)
                    ·
                      refine ⟨3229336832478648557989411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4305782443304864743985881 3229336832478648557989411)
                      ·
                        rfl

theorem cell23_6289111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 4, 2].length) (baseStart_6289111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289111 prefixEnd_6289111 := by exact prefixLift 6289111
  have htrace : WordTrace (prefixWord ++ tailWord_6289111) baseStart_6289111 baseEnd_6289111 := by
    simpa [prefixWord, tailWord_6289111, baseEnd_6289111] using wordTrace_append hprefix tailTrace_6289111
  have hstable : (prefixWord ++ tailWord_6289111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289111).length < 2 ^ (prefixWord ++ tailWord_6289111).sum := by decide
  have hdescent : baseEnd_6289111 < baseStart_6289111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289114 : List Nat := [3, 1, 1, 2, 2, 3, 2, 1, 2, 1, 5]
def baseStart_6289114 : Nat := 118140960795 + 6289114 * 2 ^ 59
def prefixEnd_6289114 : Nat := 4983230072969 + 3 ^ 40 * 6289114 * 2
def baseEnd_6289114 : Nat := 3229338372920612046251897

theorem tailTrace_6289114 : CollatzResearch.WordTrace tailWord_6289114 prefixEnd_6289114 3229338372920612046251897 := by
  unfold tailWord_6289114
  simp only [CollatzResearch.WordTrace]
  refine ⟨57345708034405387000806599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152921888091747698668817597 57345708034405387000806599)
  ·
    refine ⟨86018562051608080501209899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57345708034405387000806599 86018562051608080501209899)
    ·
      refine ⟨129027843077412120751814849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86018562051608080501209899 129027843077412120751814849)
      ·
        refine ⟨96770882308059090563861137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129027843077412120751814849 96770882308059090563861137)
        ·
          refine ⟨72578161731044317922895853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96770882308059090563861137 72578161731044317922895853)
          ·
            refine ⟨27216810649141619221085945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72578161731044317922895853 27216810649141619221085945)
            ·
              refine ⟨20412607986856214415814459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27216810649141619221085945 20412607986856214415814459)
              ·
                refine ⟨30618911980284321623721689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20412607986856214415814459 30618911980284321623721689)
                ·
                  refine ⟨22964183985213241217791267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30618911980284321623721689 22964183985213241217791267)
                  ·
                    refine ⟨34446275977819861826686901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22964183985213241217791267 34446275977819861826686901)
                    ·
                      refine ⟨3229338372920612046251897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34446275977819861826686901 3229338372920612046251897)
                      ·
                        rfl

theorem cell23_6289114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_6289114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289114 prefixEnd_6289114 := by exact prefixLift 6289114
  have htrace : WordTrace (prefixWord ++ tailWord_6289114) baseStart_6289114 baseEnd_6289114 := by
    simpa [prefixWord, tailWord_6289114, baseEnd_6289114] using wordTrace_append hprefix tailTrace_6289114
  have hstable : (prefixWord ++ tailWord_6289114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289114).length < 2 ^ (prefixWord ++ tailWord_6289114).sum := by decide
  have hdescent : baseEnd_6289114 < baseStart_6289114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289124 : List Nat := [2, 3, 1, 1, 1, 3, 2, 2, 2, 2, 4]
def baseStart_6289124 : Nat := 118140960795 + 6289124 * 2 ^ 59
def prefixEnd_6289124 : Nat := 4983230072969 + 3 ^ 40 * 6289124 * 2
def baseEnd_6289124 : Nat := 3229343507727157007126851

theorem tailTrace_6289124 : CollatzResearch.WordTrace tailWord_6289124 prefixEnd_6289124 3229343507727157007126851 := by
  unfold tailWord_6289124
  simp only [CollatzResearch.WordTrace]
  refine ⟨114691598433792659855545213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152922131245056879807393617 114691598433792659855545213)
  ·
    refine ⟨43009349412672247445829455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114691598433792659855545213 43009349412672247445829455)
    ·
      refine ⟨64514024119008371168744183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43009349412672247445829455 64514024119008371168744183)
      ·
        refine ⟨96771036178512556753116275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64514024119008371168744183 96771036178512556753116275)
        ·
          refine ⟨145156554267768835129674413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96771036178512556753116275 145156554267768835129674413)
          ·
            refine ⟨54433707850413313173627905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145156554267768835129674413 54433707850413313173627905)
            ·
              refine ⟨40825280887809984880220929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54433707850413313173627905 40825280887809984880220929)
              ·
                refine ⟨30618960665857488660165697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40825280887809984880220929 30618960665857488660165697)
                ·
                  refine ⟨22964220499393116495124273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30618960665857488660165697 22964220499393116495124273)
                  ·
                    refine ⟨17223165374544837371343205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22964220499393116495124273 17223165374544837371343205)
                    ·
                      refine ⟨3229343507727157007126851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17223165374544837371343205 3229343507727157007126851)
                      ·
                        rfl

theorem cell23_6289124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_6289124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289124 prefixEnd_6289124 := by exact prefixLift 6289124
  have htrace : WordTrace (prefixWord ++ tailWord_6289124) baseStart_6289124 baseEnd_6289124 := by
    simpa [prefixWord, tailWord_6289124, baseEnd_6289124] using wordTrace_append hprefix tailTrace_6289124
  have hstable : (prefixWord ++ tailWord_6289124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289124).length < 2 ^ (prefixWord ++ tailWord_6289124).sum := by decide
  have hdescent : baseEnd_6289124 < baseStart_6289124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289134 : List Nat := [4, 1, 2, 1, 1, 2, 2, 3, 7]
def baseStart_6289134 : Nat := 118140960795 + 6289134 * 2 ^ 59
def prefixEnd_6289134 : Nat := 4983230072969 + 3 ^ 40 * 6289134 * 2
def baseEnd_6289134 : Nat := 358816515837077996444645

theorem tailTrace_6289134 : CollatzResearch.WordTrace tailWord_6289134 prefixEnd_6289134 358816515837077996444645 := by
  unfold tailWord_6289134
  simp only [CollatzResearch.WordTrace]
  refine ⟨28672945199693636427369307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152922374398366060945969637 28672945199693636427369307)
  ·
    refine ⟨43009417799540454641053961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28672945199693636427369307 43009417799540454641053961)
    ·
      refine ⟨32257063349655340980790471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43009417799540454641053961 32257063349655340980790471)
      ·
        refine ⟨48385595024483011471185707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32257063349655340980790471 48385595024483011471185707)
        ·
          refine ⟨72578392536724517206778561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48385595024483011471185707 72578392536724517206778561)
          ·
            refine ⟨54433794402543387905083921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72578392536724517206778561 54433794402543387905083921)
            ·
              refine ⟨40825345801907540928812941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54433794402543387905083921 40825345801907540928812941)
              ·
                refine ⟨15309504675715327848304853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40825345801907540928812941 15309504675715327848304853)
                ·
                  refine ⟨358816515837077996444645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15309504675715327848304853 358816515837077996444645)
                  ·
                    rfl

theorem cell23_6289134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 7].length) (baseStart_6289134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289134 prefixEnd_6289134 := by exact prefixLift 6289134
  have htrace : WordTrace (prefixWord ++ tailWord_6289134) baseStart_6289134 baseEnd_6289134 := by
    simpa [prefixWord, tailWord_6289134, baseEnd_6289134] using wordTrace_append hprefix tailTrace_6289134
  have hstable : (prefixWord ++ tailWord_6289134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289134).length < 2 ^ (prefixWord ++ tailWord_6289134).sum := by decide
  have hdescent : baseEnd_6289134 < baseStart_6289134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289221 : List Nat := [1, 3, 1, 1, 1, 2, 4, 3, 2, 2, 3]
def baseStart_6289221 : Nat := 118140960795 + 6289221 * 2 ^ 59
def prefixEnd_6289221 : Nat := 4983230072969 + 3 ^ 40 * 6289221 * 2
def baseEnd_6289221 : Nat := 3229393315350643127613905

theorem tailTrace_6289221 : CollatzResearch.WordTrace tailWord_6289221 prefixEnd_6289221 3229393315350643127613905 := by
  unfold tailWord_6289221
  simp only [CollatzResearch.WordTrace]
  refine ⟨229386734748233905277371517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152924489832155936851581011 229386734748233905277371517)
  ·
    refine ⟨86020025530587714479014319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229386734748233905277371517 86020025530587714479014319)
    ·
      refine ⟨129030038295881571718521479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86020025530587714479014319 129030038295881571718521479)
      ·
        refine ⟨193545057443822357577782219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129030038295881571718521479 193545057443822357577782219)
        ·
          refine ⟨290317586165733536366673329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193545057443822357577782219 290317586165733536366673329)
          ·
            refine ⟨217738189624300152275004997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290317586165733536366673329 217738189624300152275004997)
            ·
              refine ⟨40825910554556278551563437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 217738189624300152275004997 40825910554556278551563437)
              ·
                refine ⟨15309716457958604456836289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40825910554556278551563437 15309716457958604456836289)
                ·
                  refine ⟨11482287343468953342627217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15309716457958604456836289 11482287343468953342627217)
                  ·
                    refine ⟨8611715507601715006970413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11482287343468953342627217 8611715507601715006970413)
                    ·
                      refine ⟨3229393315350643127613905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8611715507601715006970413 3229393315350643127613905)
                      ·
                        rfl

theorem cell23_6289221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 2, 3].length) (baseStart_6289221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289221 prefixEnd_6289221 := by exact prefixLift 6289221
  have htrace : WordTrace (prefixWord ++ tailWord_6289221) baseStart_6289221 baseEnd_6289221 := by
    simpa [prefixWord, tailWord_6289221, baseEnd_6289221] using wordTrace_append hprefix tailTrace_6289221
  have hstable : (prefixWord ++ tailWord_6289221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289221).length < 2 ^ (prefixWord ++ tailWord_6289221).sum := by decide
  have hdescent : baseEnd_6289221 < baseStart_6289221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289224 : List Nat := [2, 1, 3, 1, 1, 4, 1, 2, 8]
def baseStart_6289224 : Nat := 118140960795 + 6289224 * 2 ^ 59
def prefixEnd_6289224 : Nat := 4983230072969 + 3 ^ 40 * 6289224 * 2
def baseEnd_6289224 : Nat := 358821650643622957319599

theorem tailTrace_6289224 : CollatzResearch.WordTrace tailWord_6289224 prefixEnd_6289224 358821650643622957319599 := by
  unfold tailWord_6289224
  simp only [CollatzResearch.WordTrace]
  refine ⟨114693422083611518394865363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152924562778148691193153817 114693422083611518394865363)
  ·
    refine ⟨172040133125417277592298045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114693422083611518394865363 172040133125417277592298045)
    ·
      refine ⟨64515049922031479097111767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172040133125417277592298045 64515049922031479097111767)
      ·
        refine ⟨96772574883047218645667651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64515049922031479097111767 96772574883047218645667651)
        ·
          refine ⟨145158862324570827968501477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96772574883047218645667651 145158862324570827968501477)
          ·
            refine ⟨27217286685857030244094027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145158862324570827968501477 27217286685857030244094027)
            ·
              refine ⟨40825930028785545366141041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27217286685857030244094027 40825930028785545366141041)
              ·
                refine ⟨30619447521589159024605781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40825930028785545366141041 30619447521589159024605781)
                ·
                  refine ⟨358821650643622957319599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30619447521589159024605781 358821650643622957319599)
                  ·
                    rfl

theorem cell23_6289224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 8].length) (baseStart_6289224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289224 prefixEnd_6289224 := by exact prefixLift 6289224
  have htrace : WordTrace (prefixWord ++ tailWord_6289224) baseStart_6289224 baseEnd_6289224 := by
    simpa [prefixWord, tailWord_6289224, baseEnd_6289224] using wordTrace_append hprefix tailTrace_6289224
  have hstable : (prefixWord ++ tailWord_6289224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289224).length < 2 ^ (prefixWord ++ tailWord_6289224).sum := by decide
  have hdescent : baseEnd_6289224 < baseStart_6289224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289285 : List Nat := [1, 3, 1, 1, 3, 2, 2, 5, 1, 1, 3]
def baseStart_6289285 : Nat := 118140960795 + 6289285 * 2 ^ 59
def prefixEnd_6289285 : Nat := 4983230072969 + 3 ^ 40 * 6289285 * 2
def baseEnd_6289285 : Nat := 3229426178112530877213611

theorem tailTrace_6289285 : CollatzResearch.WordTrace tailWord_6289285 prefixEnd_6289285 3229426178112530877213611 := by
  unfold tailWord_6289285
  simp only [CollatzResearch.WordTrace]
  refine ⟨229389069020002044207701309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152926046013334696138467539 229389069020002044207701309)
  ·
    refine ⟨86020900882500766577887991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229389069020002044207701309 86020900882500766577887991)
    ·
      refine ⟨129031351323751149866831987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86020900882500766577887991 129031351323751149866831987)
      ·
        refine ⟨193547026985626724800247981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129031351323751149866831987 193547026985626724800247981)
        ·
          refine ⟨72580135119610021800092993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193547026985626724800247981 72580135119610021800092993)
          ·
            refine ⟨54435101339707516350069745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72580135119610021800092993 54435101339707516350069745)
            ·
              refine ⟨40826326004780637262552309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54435101339707516350069745 40826326004780637262552309)
              ·
                refine ⟨3827468062948184743364279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40826326004780637262552309 3827468062948184743364279)
                ·
                  refine ⟨5741202094422277115046419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3827468062948184743364279 5741202094422277115046419)
                  ·
                    refine ⟨8611803141633415672569629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5741202094422277115046419 8611803141633415672569629)
                    ·
                      refine ⟨3229426178112530877213611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8611803141633415672569629 3229426178112530877213611)
                      ·
                        rfl

theorem cell23_6289285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 5, 1, 1, 3].length) (baseStart_6289285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289285 prefixEnd_6289285 := by exact prefixLift 6289285
  have htrace : WordTrace (prefixWord ++ tailWord_6289285) baseStart_6289285 baseEnd_6289285 := by
    simpa [prefixWord, tailWord_6289285, baseEnd_6289285] using wordTrace_append hprefix tailTrace_6289285
  have hstable : (prefixWord ++ tailWord_6289285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289285).length < 2 ^ (prefixWord ++ tailWord_6289285).sum := by decide
  have hdescent : baseEnd_6289285 < baseStart_6289285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289308 : List Nat := [2, 2, 3, 3, 1, 1, 1, 2, 3, 1, 4]
def baseStart_6289308 : Nat := 118140960795 + 6289308 * 2 ^ 59
def prefixEnd_6289308 : Nat := 4983230072969 + 3 ^ 40 * 6289308 * 2
def baseEnd_6289308 : Nat := 3229437988167584287226005

theorem tailTrace_6289308 : CollatzResearch.WordTrace tailWord_6289308 prefixEnd_6289308 3229437988167584287226005 := by
  unfold tailWord_6289308
  simp only [CollatzResearch.WordTrace]
  refine ⟨114694953949459359567894289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152926605265945812757192385 114694953949459359567894289)
  ·
    refine ⟨86021215462094519675920717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114694953949459359567894289 86021215462094519675920717)
    ·
      refine ⟨32257955798285444878470269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86021215462094519675920717 32257955798285444878470269)
      ·
        refine ⟨12096733424357041829426351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32257955798285444878470269 12096733424357041829426351)
        ·
          refine ⟨18145100136535562744139527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12096733424357041829426351 18145100136535562744139527)
          ·
            refine ⟨27217650204803344116209291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18145100136535562744139527 27217650204803344116209291)
            ·
              refine ⟨40826475307205016174313937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27217650204803344116209291 40826475307205016174313937)
              ·
                refine ⟨30619856480403762130735453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40826475307205016174313937 30619856480403762130735453)
                ·
                  refine ⟨11482446180151410799025795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30619856480403762130735453 11482446180151410799025795)
                  ·
                    refine ⟨17223669270227116198538693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11482446180151410799025795 17223669270227116198538693)
                    ·
                      refine ⟨3229437988167584287226005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17223669270227116198538693 3229437988167584287226005)
                      ·
                        rfl

theorem cell23_6289308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_6289308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289308 prefixEnd_6289308 := by exact prefixLift 6289308
  have htrace : WordTrace (prefixWord ++ tailWord_6289308) baseStart_6289308 baseEnd_6289308 := by
    simpa [prefixWord, tailWord_6289308, baseEnd_6289308] using wordTrace_append hprefix tailTrace_6289308
  have hstable : (prefixWord ++ tailWord_6289308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289308).length < 2 ^ (prefixWord ++ tailWord_6289308).sum := by decide
  have hdescent : baseEnd_6289308 < baseStart_6289308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289331 : List Nat := [1, 1, 1, 2, 3, 1, 7, 7]
def baseStart_6289331 : Nat := 118140960795 + 6289331 * 2 ^ 59
def prefixEnd_6289331 : Nat := 4983230072969 + 3 ^ 40 * 6289331 * 2
def baseEnd_6289331 : Nat := 119609251786023618416237

theorem tailTrace_6289331 : CollatzResearch.WordTrace tailWord_6289331 prefixEnd_6289331 119609251786023618416237 := by
  unfold tailWord_6289331
  simp only [CollatzResearch.WordTrace]
  refine ⟨229390746777835394063875847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152927164518556929375917231 229390746777835394063875847)
  ·
    refine ⟨344086120166753091095813771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229390746777835394063875847 344086120166753091095813771)
    ·
      refine ⟨516129180250129636643720657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344086120166753091095813771 516129180250129636643720657)
      ·
        refine ⟨387096885187597227482790493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 516129180250129636643720657 387096885187597227482790493)
        ·
          refine ⟨145161331945348960306046435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 387096885187597227482790493 145161331945348960306046435)
          ·
            refine ⟨217741997918023440459069653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145161331945348960306046435 217741997918023440459069653)
            ·
              refine ⟨5103328076203674385759445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 217741997918023440459069653 5103328076203674385759445)
              ·
                refine ⟨119609251786023618416237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5103328076203674385759445 119609251786023618416237)
                ·
                  rfl

theorem cell23_6289331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 7].length) (baseStart_6289331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289331 prefixEnd_6289331 := by exact prefixLift 6289331
  have htrace : WordTrace (prefixWord ++ tailWord_6289331) baseStart_6289331 baseEnd_6289331 := by
    simpa [prefixWord, tailWord_6289331, baseEnd_6289331] using wordTrace_append hprefix tailTrace_6289331
  have hstable : (prefixWord ++ tailWord_6289331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289331).length < 2 ^ (prefixWord ++ tailWord_6289331).sum := by decide
  have hdescent : baseEnd_6289331 < baseStart_6289331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289342 : List Nat := [4, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4]
def baseStart_6289342 : Nat := 118140960795 + 6289342 * 2 ^ 59
def prefixEnd_6289342 : Nat := 4983230072969 + 3 ^ 40 * 6289342 * 2
def baseEnd_6289342 : Nat := 3229455446509837154200849

theorem tailTrace_6289342 : CollatzResearch.WordTrace tailWord_6289342 prefixEnd_6289342 3229455446509837154200849 := by
  unfold tailWord_6289342
  simp only [CollatzResearch.WordTrace]
  refine ⟨28673893497599442867815785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152927431987197028628350853 28673893497599442867815785)
  ·
    refine ⟨21505420123199582150861839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28673893497599442867815785 21505420123199582150861839)
    ·
      refine ⟨32258130184799373226292759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21505420123199582150861839 32258130184799373226292759)
      ·
        refine ⟨48387195277199059839439139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32258130184799373226292759 48387195277199059839439139)
        ·
          refine ⟨72580792915798589759158709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48387195277199059839439139 72580792915798589759158709)
          ·
            refine ⟨6804449335856117789921129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72580792915798589759158709 6804449335856117789921129)
            ·
              refine ⟨5103337001892088342440847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6804449335856117789921129 5103337001892088342440847)
              ·
                refine ⟨7655005502838132513661271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5103337001892088342440847 7655005502838132513661271)
                ·
                  refine ⟨11482508254257198770491907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7655005502838132513661271 11482508254257198770491907)
                  ·
                    refine ⟨17223762381385798155737861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11482508254257198770491907 17223762381385798155737861)
                    ·
                      refine ⟨3229455446509837154200849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17223762381385798155737861 3229455446509837154200849)
                      ·
                        rfl

theorem cell23_6289342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_6289342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289342 prefixEnd_6289342 := by exact prefixLift 6289342
  have htrace : WordTrace (prefixWord ++ tailWord_6289342) baseStart_6289342 baseEnd_6289342 := by
    simpa [prefixWord, tailWord_6289342, baseEnd_6289342] using wordTrace_append hprefix tailTrace_6289342
  have hstable : (prefixWord ++ tailWord_6289342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289342).length < 2 ^ (prefixWord ++ tailWord_6289342).sum := by decide
  have hdescent : baseEnd_6289342 < baseStart_6289342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289372 : List Nat := [2, 2, 6, 1, 1, 1, 1, 1, 1, 1, 6]
def baseStart_6289372 : Nat := 118140960795 + 6289372 * 2 ^ 59
def prefixEnd_6289372 : Nat := 4983230072969 + 3 ^ 40 * 6289372 * 2
def baseEnd_6289372 : Nat := 3229470850929472036825711

theorem tailTrace_6289372 : CollatzResearch.WordTrace tailWord_6289372 prefixEnd_6289372 3229470850929472036825711 := by
  unfold tailWord_6289372
  simp only [CollatzResearch.WordTrace]
  refine ⟨114696121085343429033059185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152928161447124572044078913 114696121085343429033059185)
  ·
    refine ⟨86022090814007571774794389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114696121085343429033059185 86022090814007571774794389)
    ·
      refine ⟨4032285506906604926943487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86022090814007571774794389 4032285506906604926943487)
      ·
        refine ⟨6048428260359907390415231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4032285506906604926943487 6048428260359907390415231)
        ·
          refine ⟨9072642390539861085622847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6048428260359907390415231 9072642390539861085622847)
          ·
            refine ⟨13608963585809791628434271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9072642390539861085622847 13608963585809791628434271)
            ·
              refine ⟨20413445378714687442651407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13608963585809791628434271 20413445378714687442651407)
              ·
                refine ⟨30620168068072031163977111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20413445378714687442651407 30620168068072031163977111)
                ·
                  refine ⟨45930252102108046745965667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30620168068072031163977111 45930252102108046745965667)
                  ·
                    refine ⟨68895378153162070118948501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45930252102108046745965667 68895378153162070118948501)
                    ·
                      refine ⟨3229470850929472036825711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68895378153162070118948501 3229470850929472036825711)
                      ·
                        rfl

theorem cell23_6289372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_6289372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289372 prefixEnd_6289372 := by exact prefixLift 6289372
  have htrace : WordTrace (prefixWord ++ tailWord_6289372) baseStart_6289372 baseEnd_6289372 := by
    simpa [prefixWord, tailWord_6289372, baseEnd_6289372] using wordTrace_append hprefix tailTrace_6289372
  have hstable : (prefixWord ++ tailWord_6289372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289372).length < 2 ^ (prefixWord ++ tailWord_6289372).sum := by decide
  have hdescent : baseEnd_6289372 < baseStart_6289372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289375 : List Nat := [1, 1, 2, 3, 4, 3, 1, 1, 1, 3, 3]
def baseStart_6289375 : Nat := 118140960795 + 6289375 * 2 ^ 59
def prefixEnd_6289375 : Nat := 4983230072969 + 3 ^ 40 * 6289375 * 2
def baseEnd_6289375 : Nat := 3229472391371435525088197

theorem tailTrace_6289375 : CollatzResearch.WordTrace tailWord_6289375 prefixEnd_6289375 3229472391371435525088197 := by
  unfold tailWord_6289375
  simp only [CollatzResearch.WordTrace]
  refine ⟨229392351589675989578477579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152928234393117326385651719 229392351589675989578477579)
  ·
    refine ⟨344088527384513984367716369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229392351589675989578477579 344088527384513984367716369)
    ·
      refine ⟨258066395538385488275787277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344088527384513984367716369 258066395538385488275787277)
      ·
        refine ⟨96774898326894558103420229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258066395538385488275787277 96774898326894558103420229)
        ·
          refine ⟨18145293436292729644391293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96774898326894558103420229 18145293436292729644391293)
          ·
            refine ⟨6804485038609773616646735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18145293436292729644391293 6804485038609773616646735)
            ·
              refine ⟨10206727557914660424970103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6804485038609773616646735 10206727557914660424970103)
              ·
                refine ⟨15310091336871990637455155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10206727557914660424970103 15310091336871990637455155)
                ·
                  refine ⟨22965137005307985956182733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15310091336871990637455155 22965137005307985956182733)
                  ·
                    refine ⟨8611926376990494733568525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22965137005307985956182733 8611926376990494733568525)
                    ·
                      refine ⟨3229472391371435525088197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8611926376990494733568525 3229472391371435525088197)
                      ·
                        rfl

theorem cell23_6289375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_6289375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289375 prefixEnd_6289375 := by exact prefixLift 6289375
  have htrace : WordTrace (prefixWord ++ tailWord_6289375) baseStart_6289375 baseEnd_6289375 := by
    simpa [prefixWord, tailWord_6289375, baseEnd_6289375] using wordTrace_append hprefix tailTrace_6289375
  have hstable : (prefixWord ++ tailWord_6289375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289375).length < 2 ^ (prefixWord ++ tailWord_6289375).sum := by decide
  have hdescent : baseEnd_6289375 < baseStart_6289375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289401 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 1, 3, 5]
def baseStart_6289401 : Nat := 118140960795 + 6289401 * 2 ^ 59
def prefixEnd_6289401 : Nat := 4983230072969 + 3 ^ 40 * 6289401 * 2
def baseEnd_6289401 : Nat := 3229485741868452423363077

theorem tailTrace_6289401 : CollatzResearch.WordTrace tailWord_6289401 prefixEnd_6289401 3229485741868452423363077 := by
  unfold tailWord_6289401
  simp only [CollatzResearch.WordTrace]
  refine ⟨229393299887581796018924057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152928866591721197345949371 229393299887581796018924057)
  ·
    refine ⟨172044974915686347014193043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229393299887581796018924057 172044974915686347014193043)
    ·
      refine ⟨258067462373529520521289565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172044974915686347014193043 258067462373529520521289565)
      ·
        refine ⟨96775298390073570195483587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258067462373529520521289565 96775298390073570195483587)
        ·
          refine ⟨145162947585110355293225381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96775298390073570195483587 145162947585110355293225381)
          ·
            refine ⟨27218052672208191617479759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145162947585110355293225381 27218052672208191617479759)
            ·
              refine ⟨40827079008312287426219639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27218052672208191617479759 40827079008312287426219639)
              ·
                refine ⟨61240618512468431139329459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40827079008312287426219639 61240618512468431139329459)
                ·
                  refine ⟨91860927768702646708994189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61240618512468431139329459 91860927768702646708994189)
                  ·
                    refine ⟨34447847913263492515872821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91860927768702646708994189 34447847913263492515872821)
                    ·
                      refine ⟨3229485741868452423363077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34447847913263492515872821 3229485741868452423363077)
                      ·
                        rfl

theorem cell23_6289401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_6289401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289401 prefixEnd_6289401 := by exact prefixLift 6289401
  have htrace : WordTrace (prefixWord ++ tailWord_6289401) baseStart_6289401 baseEnd_6289401 := by
    simpa [prefixWord, tailWord_6289401, baseEnd_6289401] using wordTrace_append hprefix tailTrace_6289401
  have hstable : (prefixWord ++ tailWord_6289401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289401).length < 2 ^ (prefixWord ++ tailWord_6289401).sum := by decide
  have hdescent : baseEnd_6289401 < baseStart_6289401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289411 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 4]
def baseStart_6289411 : Nat := 118140960795 + 6289411 * 2 ^ 59
def prefixEnd_6289411 : Nat := 4983230072969 + 3 ^ 40 * 6289411 * 2
def baseEnd_6289411 : Nat := 3229490876674997384238031

theorem tailTrace_6289411 : CollatzResearch.WordTrace tailWord_6289411 prefixEnd_6289411 3229490876674997384238031 := by
  unfold tailWord_6289411
  simp only [CollatzResearch.WordTrace]
  refine ⟨229393664617545567726788087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152929109745030378484525391 229393664617545567726788087)
  ·
    refine ⟨344090496926318351590182131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229393664617545567726788087 344090496926318351590182131)
    ·
      refine ⟨516135745389477527385273197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344090496926318351590182131 516135745389477527385273197)
      ·
        refine ⟨193550904521054072769477449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 516135745389477527385273197 193550904521054072769477449)
        ·
          refine ⟨145163178390790554577108087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193550904521054072769477449 145163178390790554577108087)
          ·
            refine ⟨217744767586185831865662131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145163178390790554577108087 217744767586185831865662131)
            ·
              refine ⟨326617151379278747798493197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217744767586185831865662131 326617151379278747798493197)
              ·
                refine ⟨122481431767229530424434949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 326617151379278747798493197 122481431767229530424434949)
                ·
                  refine ⟨22965268456355536954581553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122481431767229530424434949 22965268456355536954581553)
                  ·
                    refine ⟨17223951342266652715936165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22965268456355536954581553 17223951342266652715936165)
                    ·
                      refine ⟨3229490876674997384238031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17223951342266652715936165 3229490876674997384238031)
                      ·
                        rfl

theorem cell23_6289411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_6289411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289411 prefixEnd_6289411 := by exact prefixLift 6289411
  have htrace : WordTrace (prefixWord ++ tailWord_6289411) baseStart_6289411 baseEnd_6289411 := by
    simpa [prefixWord, tailWord_6289411, baseEnd_6289411] using wordTrace_append hprefix tailTrace_6289411
  have hstable : (prefixWord ++ tailWord_6289411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289411).length < 2 ^ (prefixWord ++ tailWord_6289411).sum := by decide
  have hdescent : baseEnd_6289411 < baseStart_6289411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289432 : List Nat := [2, 1, 2, 3, 2, 1, 3, 3, 2, 2, 2]
def baseStart_6289432 : Nat := 118140960795 + 6289432 * 2 ^ 59
def prefixEnd_6289432 : Nat := 4983230072969 + 3 ^ 40 * 6289432 * 2
def baseEnd_6289432 : Nat := 3229501659768741802075435

theorem tailTrace_6289432 : CollatzResearch.WordTrace tailWord_6289432 prefixEnd_6289432 3229501659768741802075435 := by
  unfold tailWord_6289432
  simp only [CollatzResearch.WordTrace]
  refine ⟨114697215275234744156651275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152929620366979658875535033 114697215275234744156651275)
  ·
    refine ⟨172045822912852116234976913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114697215275234744156651275 172045822912852116234976913)
    ·
      refine ⟨129034367184639087176232685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172045822912852116234976913 129034367184639087176232685)
      ·
        refine ⟨48387887694239657691087257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129034367184639087176232685 48387887694239657691087257)
        ·
          refine ⟨36290915770679743268315443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48387887694239657691087257 36290915770679743268315443)
          ·
            refine ⟨54436373656019614902473165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36290915770679743268315443 54436373656019614902473165)
            ·
              refine ⟨20413640121007355588427437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54436373656019614902473165 20413640121007355588427437)
              ·
                refine ⟨7655115045377758345660289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20413640121007355588427437 7655115045377758345660289)
                ·
                  refine ⟨5741336284033318759245217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7655115045377758345660289 5741336284033318759245217)
                  ·
                    refine ⟨4306002213024989069433913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5741336284033318759245217 4306002213024989069433913)
                    ·
                      refine ⟨3229501659768741802075435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4306002213024989069433913 3229501659768741802075435)
                      ·
                        rfl

theorem cell23_6289432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_6289432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289432 prefixEnd_6289432 := by exact prefixLift 6289432
  have htrace : WordTrace (prefixWord ++ tailWord_6289432) baseStart_6289432 baseEnd_6289432 := by
    simpa [prefixWord, tailWord_6289432, baseEnd_6289432] using wordTrace_append hprefix tailTrace_6289432
  have hstable : (prefixWord ++ tailWord_6289432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289432).length < 2 ^ (prefixWord ++ tailWord_6289432).sum := by decide
  have hdescent : baseEnd_6289432 < baseStart_6289432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289468 : List Nat := [2, 2, 2, 2, 2, 1, 1, 4, 2, 5]
def baseStart_6289468 : Nat := 118140960795 + 6289468 * 2 ^ 59
def prefixEnd_6289468 : Nat := 4983230072969 + 3 ^ 40 * 6289468 * 2
def baseEnd_6289468 : Nat := 1076506715024101220408423

theorem tailTrace_6289468 : CollatzResearch.WordTrace tailWord_6289468 prefixEnd_6289468 1076506715024101220408423 := by
  unfold tailWord_6289468
  simp only [CollatzResearch.WordTrace]
  refine ⟨114697871789169533230806529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152930495718892710974408705 114697871789169533230806529)
  ·
    refine ⟨86023403841877149923104897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114697871789169533230806529 86023403841877149923104897)
    ·
      refine ⟨64517552881407862442328673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86023403841877149923104897 64517552881407862442328673)
      ·
        refine ⟨48388164661055896831746505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64517552881407862442328673 48388164661055896831746505)
        ·
          refine ⟨36291123495791922623809879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48388164661055896831746505 36291123495791922623809879)
          ·
            refine ⟨54436685243687883935714819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36291123495791922623809879 54436685243687883935714819)
            ·
              refine ⟨81655027865531825903572229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54436685243687883935714819 81655027865531825903572229)
              ·
                refine ⟨15310317724787217356919793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81655027865531825903572229 15310317724787217356919793)
                ·
                  refine ⟨11482738293590413017689845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15310317724787217356919793 11482738293590413017689845)
                  ·
                    refine ⟨1076506715024101220408423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11482738293590413017689845 1076506715024101220408423)
                    ·
                      rfl

theorem cell23_6289468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_6289468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289468 prefixEnd_6289468 := by exact prefixLift 6289468
  have htrace : WordTrace (prefixWord ++ tailWord_6289468) baseStart_6289468 baseEnd_6289468 := by
    simpa [prefixWord, tailWord_6289468, baseEnd_6289468] using wordTrace_append hprefix tailTrace_6289468
  have hstable : (prefixWord ++ tailWord_6289468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289468).length < 2 ^ (prefixWord ++ tailWord_6289468).sum := by decide
  have hdescent : baseEnd_6289468 < baseStart_6289468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289472 : List Nat := [2, 1, 1, 2, 2, 6, 2, 2, 5]
def baseStart_6289472 : Nat := 118140960795 + 6289472 * 2 ^ 59
def prefixEnd_6289472 : Nat := 4983230072969 + 3 ^ 40 * 6289472 * 2
def baseEnd_6289472 : Nat := 358835799888324627286139

theorem tailTrace_6289472 : CollatzResearch.WordTrace tailWord_6289472 prefixEnd_6289472 358835799888324627286139 := by
  unfold tailWord_6289472
  simp only [CollatzResearch.WordTrace]
  refine ⟨114697944735162287572379335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152930592980216383429839113 114697944735162287572379335)
  ·
    refine ⟨172046917102743431358569003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114697944735162287572379335 172046917102743431358569003)
    ·
      refine ⟨258070375654115147037853505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172046917102743431358569003 258070375654115147037853505)
      ·
        refine ⟨193552781740586360278390129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258070375654115147037853505 193552781740586360278390129)
        ·
          refine ⟨145164586305439770208792597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193552781740586360278390129 145164586305439770208792597)
          ·
            refine ⟨6804589983067489228537153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 145164586305439770208792597 6804589983067489228537153)
            ·
              refine ⟨5103442487300616921402865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6804589983067489228537153 5103442487300616921402865)
              ·
                refine ⟨3827581865475462691052149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5103442487300616921402865 3827581865475462691052149)
                ·
                  refine ⟨358835799888324627286139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3827581865475462691052149 358835799888324627286139)
                  ·
                    rfl

theorem cell23_6289472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 2, 5].length) (baseStart_6289472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289472 prefixEnd_6289472 := by exact prefixLift 6289472
  have htrace : WordTrace (prefixWord ++ tailWord_6289472) baseStart_6289472 baseEnd_6289472 := by
    simpa [prefixWord, tailWord_6289472, baseEnd_6289472] using wordTrace_append hprefix tailTrace_6289472
  have hstable : (prefixWord ++ tailWord_6289472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289472).length < 2 ^ (prefixWord ++ tailWord_6289472).sum := by decide
  have hdescent : baseEnd_6289472 < baseStart_6289472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289491 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 5]
def baseStart_6289491 : Nat := 118140960795 + 6289491 * 2 ^ 59
def prefixEnd_6289491 : Nat := 4983230072969 + 3 ^ 40 * 6289491 * 2
def baseEnd_6289491 : Nat := 3229531955127357071237663

theorem tailTrace_6289491 : CollatzResearch.WordTrace tailWord_6289491 prefixEnd_6289491 3229531955127357071237663 := by
  unfold tailWord_6289491
  simp only [CollatzResearch.WordTrace]
  refine ⟨229396582457255741389700327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152931054971503827593133551 229396582457255741389700327)
  ·
    refine ⟨344094873685883612084550491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229396582457255741389700327 344094873685883612084550491)
    ·
      refine ⟨516142310528825418126825737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344094873685883612084550491 516142310528825418126825737)
      ·
        refine ⟨387106732896619063595119303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 516142310528825418126825737 387106732896619063595119303)
        ·
          refine ⟨580660099344928595392678955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387106732896619063595119303 580660099344928595392678955)
          ·
            refine ⟨870990149017392893089018433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580660099344928595392678955 870990149017392893089018433)
            ·
              refine ⟨653242611763044669816763825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 870990149017392893089018433 653242611763044669816763825)
              ·
                refine ⟨489931958822283502362572869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 653242611763044669816763825 489931958822283502362572869)
                ·
                  refine ⟨91862242279178156692982413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 489931958822283502362572869 91862242279178156692982413)
                  ·
                    refine ⟨34448340854691808759868405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91862242279178156692982413 34448340854691808759868405)
                    ·
                      refine ⟨3229531955127357071237663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34448340854691808759868405 3229531955127357071237663)
                      ·
                        rfl

theorem cell23_6289491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 5].length) (baseStart_6289491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289491 prefixEnd_6289491 := by exact prefixLift 6289491
  have htrace : WordTrace (prefixWord ++ tailWord_6289491) baseStart_6289491 baseEnd_6289491 := by
    simpa [prefixWord, tailWord_6289491, baseEnd_6289491] using wordTrace_append hprefix tailTrace_6289491
  have hstable : (prefixWord ++ tailWord_6289491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289491).length < 2 ^ (prefixWord ++ tailWord_6289491).sum := by decide
  have hdescent : baseEnd_6289491 < baseStart_6289491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289518 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6]
def baseStart_6289518 : Nat := 118140960795 + 6289518 * 2 ^ 59
def prefixEnd_6289518 : Nat := 4983230072969 + 3 ^ 40 * 6289518 * 2
def baseEnd_6289518 : Nat := 3229545819105028465600039

theorem tailTrace_6289518 : CollatzResearch.WordTrace tailWord_6289518 prefixEnd_6289518 3229545819105028465600039 := by
  unfold tailWord_6289518
  simp only [CollatzResearch.WordTrace]
  refine ⟨28674695903519740625116651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152931711485438616667288805 28674695903519740625116651)
  ·
    refine ⟨43012043855279610937674977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28674695903519740625116651 43012043855279610937674977)
    ·
      refine ⟨32259032891459708203256233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43012043855279610937674977 32259032891459708203256233)
      ·
        refine ⟨24194274668594781152442175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32259032891459708203256233 24194274668594781152442175)
        ·
          refine ⟨36291412002892171728663263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24194274668594781152442175 36291412002892171728663263)
          ·
            refine ⟨54437118004338257592994895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36291412002892171728663263 54437118004338257592994895)
            ·
              refine ⟨81655677006507386389492343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54437118004338257592994895 81655677006507386389492343)
              ·
                refine ⟨122483515509761079584238515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81655677006507386389492343 122483515509761079584238515)
                ·
                  refine ⟨183725273264641619376357773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122483515509761079584238515 183725273264641619376357773)
                  ·
                    refine ⟨68896977474240607266134165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 183725273264641619376357773 68896977474240607266134165)
                    ·
                      refine ⟨3229545819105028465600039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68896977474240607266134165 3229545819105028465600039)
                      ·
                        rfl

theorem cell23_6289518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_6289518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289518 prefixEnd_6289518 := by exact prefixLift 6289518
  have htrace : WordTrace (prefixWord ++ tailWord_6289518) baseStart_6289518 baseEnd_6289518 := by
    simpa [prefixWord, tailWord_6289518, baseEnd_6289518] using wordTrace_append hprefix tailTrace_6289518
  have hstable : (prefixWord ++ tailWord_6289518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289518).length < 2 ^ (prefixWord ++ tailWord_6289518).sum := by decide
  have hdescent : baseEnd_6289518 < baseStart_6289518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289532 : List Nat := [2, 2, 2, 1, 1, 4, 2, 4, 1, 4]
def baseStart_6289532 : Nat := 118140960795 + 6289532 * 2 ^ 59
def prefixEnd_6289532 : Nat := 4983230072969 + 3 ^ 40 * 6289532 * 2
def baseEnd_6289532 : Nat := 1076517669278063803608325

theorem tailTrace_6289532 : CollatzResearch.WordTrace tailWord_6289532 prefixEnd_6289532 1076517669278063803608325 := by
  unfold tailWord_6289532
  simp only [CollatzResearch.WordTrace]
  refine ⟨114699038925053602695971425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152932051900071470261295233 114699038925053602695971425)
  ·
    refine ⟨86024279193790202021978569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114699038925053602695971425 86024279193790202021978569)
    ·
      refine ⟨64518209395342651516483927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86024279193790202021978569 64518209395342651516483927)
      ·
        refine ⟨96777314093013977274725891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64518209395342651516483927 96777314093013977274725891)
        ·
          refine ⟨145165971139520965912088837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96777314093013977274725891 145165971139520965912088837)
          ·
            refine ⟨27218619588660181108516657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145165971139520965912088837 27218619588660181108516657)
            ·
              refine ⟨20413964691495135831387493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27218619588660181108516657 20413964691495135831387493)
              ·
                refine ⟨3827618379655337968385155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20413964691495135831387493 3827618379655337968385155)
                ·
                  refine ⟨5741427569483006952577733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3827618379655337968385155 5741427569483006952577733)
                  ·
                    refine ⟨1076517669278063803608325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5741427569483006952577733 1076517669278063803608325)
                    ·
                      rfl

theorem cell23_6289532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_6289532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289532 prefixEnd_6289532 := by exact prefixLift 6289532
  have htrace : WordTrace (prefixWord ++ tailWord_6289532) baseStart_6289532 baseEnd_6289532 := by
    simpa [prefixWord, tailWord_6289532, baseEnd_6289532] using wordTrace_append hprefix tailTrace_6289532
  have hstable : (prefixWord ++ tailWord_6289532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289532).length < 2 ^ (prefixWord ++ tailWord_6289532).sum := by decide
  have hdescent : baseEnd_6289532 < baseStart_6289532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289545 : List Nat := [1, 2, 1, 1, 4, 2, 5, 1, 6]
def baseStart_6289545 : Nat := 118140960795 + 6289545 * 2 ^ 59
def prefixEnd_6289545 : Nat := 4983230072969 + 3 ^ 40 * 6289545 * 2
def baseEnd_6289545 : Nat := 358839964786966651106935

theorem tailTrace_6289545 : CollatzResearch.WordTrace tailWord_6289545 prefixEnd_6289545 358839964786966651106935 := by
  unfold tailWord_6289545
  simp only [CollatzResearch.WordTrace]
  refine ⟨229398551999060108612166089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152932367999373405741444059 229398551999060108612166089)
  ·
    refine ⟨172048913999295081459124567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229398551999060108612166089 172048913999295081459124567)
    ·
      refine ⟨258073370998942622188686851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172048913999295081459124567 258073370998942622188686851)
      ·
        refine ⟨387110056498413933283030277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258073370998942622188686851 387110056498413933283030277)
        ·
          refine ⟨72583135593452612490568177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 387110056498413933283030277 72583135593452612490568177)
          ·
            refine ⟨54437351695089459367926133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72583135593452612490568177 54437351695089459367926133)
            ·
              refine ⟨5103501721414636815743075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54437351695089459367926133 5103501721414636815743075)
              ·
                refine ⟨7655252582121955223614613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5103501721414636815743075 7655252582121955223614613)
                ·
                  refine ⟨358839964786966651106935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7655252582121955223614613 358839964786966651106935)
                  ·
                    rfl

theorem cell23_6289545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 6].length) (baseStart_6289545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289545 prefixEnd_6289545 := by exact prefixLift 6289545
  have htrace : WordTrace (prefixWord ++ tailWord_6289545) baseStart_6289545 baseEnd_6289545 := by
    simpa [prefixWord, tailWord_6289545, baseEnd_6289545] using wordTrace_append hprefix tailTrace_6289545
  have hstable : (prefixWord ++ tailWord_6289545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289545).length < 2 ^ (prefixWord ++ tailWord_6289545).sum := by decide
  have hdescent : baseEnd_6289545 < baseStart_6289545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289615 : List Nat := [1, 1, 2, 1, 1, 3, 5, 1, 3, 2, 3]
def baseStart_6289615 : Nat := 118140960795 + 6289615 * 2 ^ 59
def prefixEnd_6289615 : Nat := 4983230072969 + 3 ^ 40 * 6289615 * 2
def baseEnd_6289615 : Nat := 3229595626728514586087093

theorem tailTrace_6289615 : CollatzResearch.WordTrace tailWord_6289615 prefixEnd_6289615 3229595626728514586087093 := by
  unfold tailWord_6289615
  simp only [CollatzResearch.WordTrace]
  refine ⟨229401105108806510567214299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152934070072537673711476199 229401105108806510567214299)
  ·
    refine ⟨344101657663209765850821449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229401105108806510567214299 344101657663209765850821449)
    ·
      refine ⟨258076243247407324388116087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344101657663209765850821449 258076243247407324388116087)
      ·
        refine ⟨387114364871110986582174131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258076243247407324388116087 387114364871110986582174131)
        ·
          refine ⟨580671547306666479873261197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387114364871110986582174131 580671547306666479873261197)
          ·
            refine ⟨217751830239999929952472949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 580671547306666479873261197 217751830239999929952472949)
            ·
              refine ⟨20414234084999993433044339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 217751830239999929952472949 20414234084999993433044339)
              ·
                refine ⟨30621351127499990149566509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20414234084999993433044339 30621351127499990149566509)
                ·
                  refine ⟨11483006672812496306087441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30621351127499990149566509 11483006672812496306087441)
                  ·
                    refine ⟨8612255004609372229565581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11483006672812496306087441 8612255004609372229565581)
                    ·
                      refine ⟨3229595626728514586087093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8612255004609372229565581 3229595626728514586087093)
                      ·
                        rfl

theorem cell23_6289615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 2, 3].length) (baseStart_6289615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289615 prefixEnd_6289615 := by exact prefixLift 6289615
  have htrace : WordTrace (prefixWord ++ tailWord_6289615) baseStart_6289615 baseEnd_6289615 := by
    simpa [prefixWord, tailWord_6289615, baseEnd_6289615] using wordTrace_append hprefix tailTrace_6289615
  have hstable : (prefixWord ++ tailWord_6289615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289615).length < 2 ^ (prefixWord ++ tailWord_6289615).sum := by decide
  have hdescent : baseEnd_6289615 < baseStart_6289615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289622 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 3, 6]
def baseStart_6289622 : Nat := 118140960795 + 6289622 * 2 ^ 59
def prefixEnd_6289622 : Nat := 4983230072969 + 3 ^ 40 * 6289622 * 2
def baseEnd_6289622 : Nat := 1076533073697698686233187

theorem tailTrace_6289622 : CollatzResearch.WordTrace tailWord_6289622 prefixEnd_6289622 1076533073697698686233187 := by
  unfold tailWord_6289622
  simp only [CollatzResearch.WordTrace]
  refine ⟨14337585026236321922669945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152934240279854100508479413 14337585026236321922669945)
  ·
    refine ⟨10753188769677241442002459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14337585026236321922669945 10753188769677241442002459)
    ·
      refine ⟨16129783154515862163003689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10753188769677241442002459 16129783154515862163003689)
      ·
        refine ⟨12097337365886896622252767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16129783154515862163003689 12097337365886896622252767)
        ·
          refine ⟨18146006048830344933379151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12097337365886896622252767 18146006048830344933379151)
          ·
            refine ⟨27219009073245517400068727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18146006048830344933379151 27219009073245517400068727)
            ·
              refine ⟨40828513609868276100103091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27219009073245517400068727 40828513609868276100103091)
              ·
                refine ⟨61242770414802414150154637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40828513609868276100103091 61242770414802414150154637)
                ·
                  refine ⟨22966038905550905306307989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61242770414802414150154637 22966038905550905306307989)
                  ·
                    refine ⟨1076533073697698686233187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22966038905550905306307989 1076533073697698686233187)
                    ·
                      rfl

theorem cell23_6289622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_6289622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289622 prefixEnd_6289622 := by exact prefixLift 6289622
  have htrace : WordTrace (prefixWord ++ tailWord_6289622) baseStart_6289622 baseEnd_6289622 := by
    simpa [prefixWord, tailWord_6289622, baseEnd_6289622] using wordTrace_append hprefix tailTrace_6289622
  have hstable : (prefixWord ++ tailWord_6289622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289622).length < 2 ^ (prefixWord ++ tailWord_6289622).sum := by decide
  have hdescent : baseEnd_6289622 < baseStart_6289622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289635 : List Nat := [1, 1, 1, 8, 1, 11]
def baseStart_6289635 : Nat := 118140960795 + 6289635 * 2 ^ 59
def prefixEnd_6289635 : Nat := 4983230072969 + 3 ^ 40 * 6289635 * 2
def baseEnd_6289635 : Nat := 13290559244204133777107

theorem tailTrace_6289635 : CollatzResearch.WordTrace tailWord_6289635 prefixEnd_6289635 13290559244204133777107 := by
  unfold tailWord_6289635
  simp only [CollatzResearch.WordTrace]
  refine ⟨229401834568734053982942359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152934556379156035988628239 229401834568734053982942359)
  ·
    refine ⟨344102751853101080974413539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229401834568734053982942359 344102751853101080974413539)
    ·
      refine ⟨516154127779651621461620309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344102751853101080974413539 516154127779651621461620309)
      ·
        refine ⟨6048681184917792439003363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 516154127779651621461620309 6048681184917792439003363)
        ·
          refine ⟨9073021777376688658505045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6048681184917792439003363 9073021777376688658505045)
          ·
            refine ⟨13290559244204133777107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9073021777376688658505045 13290559244204133777107)
            ·
              rfl

theorem cell23_6289635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 11].length) (baseStart_6289635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289635 prefixEnd_6289635 := by exact prefixLift 6289635
  have htrace : WordTrace (prefixWord ++ tailWord_6289635) baseStart_6289635 baseEnd_6289635 := by
    simpa [prefixWord, tailWord_6289635, baseEnd_6289635] using wordTrace_append hprefix tailTrace_6289635
  have hstable : (prefixWord ++ tailWord_6289635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289635).length < 2 ^ (prefixWord ++ tailWord_6289635).sum := by decide
  have hdescent : baseEnd_6289635 < baseStart_6289635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289639 : List Nat := [1, 1, 5, 3, 1, 2, 2, 2, 2, 4]
def baseStart_6289639 : Nat := 118140960795 + 6289639 * 2 ^ 59
def prefixEnd_6289639 : Nat := 4983230072969 + 3 ^ 40 * 6289639 * 2
def baseEnd_6289639 : Nat := 1076535983421407497395661

theorem tailTrace_6289639 : CollatzResearch.WordTrace tailWord_6289639 prefixEnd_6289639 1076535983421407497395661 := by
  unfold tailWord_6289639
  simp only [CollatzResearch.WordTrace]
  refine ⟨229401980460719562666087971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152934653640479708444058647 229401980460719562666087971)
  ·
    refine ⟨344102970691079343999131957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229401980460719562666087971 344102970691079343999131957)
    ·
      refine ⟨32259653502288688499918621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 344102970691079343999131957 32259653502288688499918621)
      ·
        refine ⟨12097370063358258187469483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32259653502288688499918621 12097370063358258187469483)
        ·
          refine ⟨18146055095037387281204225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12097370063358258187469483 18146055095037387281204225)
          ·
            refine ⟨13609541321278040460903169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18146055095037387281204225 13609541321278040460903169)
            ·
              refine ⟨10207155990958530345677377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13609541321278040460903169 10207155990958530345677377)
              ·
                refine ⟨7655366993218897759258033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10207155990958530345677377 7655366993218897759258033)
                ·
                  refine ⟨5741525244914173319443525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7655366993218897759258033 5741525244914173319443525)
                  ·
                    refine ⟨1076535983421407497395661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5741525244914173319443525 1076535983421407497395661)
                    ·
                      rfl

theorem cell23_6289639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_6289639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289639 prefixEnd_6289639 := by exact prefixLift 6289639
  have htrace : WordTrace (prefixWord ++ tailWord_6289639) baseStart_6289639 baseEnd_6289639 := by
    simpa [prefixWord, tailWord_6289639, baseEnd_6289639] using wordTrace_append hprefix tailTrace_6289639
  have hstable : (prefixWord ++ tailWord_6289639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289639).length < 2 ^ (prefixWord ++ tailWord_6289639).sum := by decide
  have hdescent : baseEnd_6289639 < baseStart_6289639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289655 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 1, 9, 2]
def baseStart_6289655 : Nat := 118140960795 + 6289655 * 2 ^ 59
def prefixEnd_6289655 : Nat := 4983230072969 + 3 ^ 40 * 6289655 * 2
def baseEnd_6289655 : Nat := 3229616165954694429586909

theorem tailTrace_6289655 : CollatzResearch.WordTrace tailWord_6289655 prefixEnd_6289655 3229616165954694429586909 := by
  unfold tailWord_6289655
  simp only [CollatzResearch.WordTrace]
  refine ⟨229402564028661597398670419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152935042685774398265780279 229402564028661597398670419)
  ·
    refine ⟨344103846042992396098005629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229402564028661597398670419 344103846042992396098005629)
    ·
      refine ⟨129038942266122148536752111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344103846042992396098005629 129038942266122148536752111)
      ·
        refine ⟨193558413399183222805128167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129038942266122148536752111 193558413399183222805128167)
        ·
          refine ⟨290337620098774834207692251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193558413399183222805128167 290337620098774834207692251)
          ·
            refine ⟨435506430148162251311538377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290337620098774834207692251 435506430148162251311538377)
            ·
              refine ⟨326629822611121688483653783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435506430148162251311538377 326629822611121688483653783)
              ·
                refine ⟨489944733916682532725480675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 326629822611121688483653783 489944733916682532725480675)
                ·
                  refine ⟨734917100875023799088221013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 489944733916682532725480675 734917100875023799088221013)
                  ·
                    refine ⟨4306154887939592572782545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 734917100875023799088221013 4306154887939592572782545)
                    ·
                      refine ⟨3229616165954694429586909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4306154887939592572782545 3229616165954694429586909)
                      ·
                        rfl

theorem cell23_6289655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 9, 2].length) (baseStart_6289655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289655 prefixEnd_6289655 := by exact prefixLift 6289655
  have htrace : WordTrace (prefixWord ++ tailWord_6289655) baseStart_6289655 baseEnd_6289655 := by
    simpa [prefixWord, tailWord_6289655, baseEnd_6289655] using wordTrace_append hprefix tailTrace_6289655
  have hstable : (prefixWord ++ tailWord_6289655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289655).length < 2 ^ (prefixWord ++ tailWord_6289655).sum := by decide
  have hdescent : baseEnd_6289655 < baseStart_6289655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289695 : List Nat := [1, 1, 2, 4, 3, 1, 1, 2, 2, 6]
def baseStart_6289695 : Nat := 118140960795 + 6289695 * 2 ^ 59
def prefixEnd_6289695 : Nat := 4983230072969 + 3 ^ 40 * 6289695 * 2
def baseEnd_6289695 : Nat := 1076545568393624757695575

theorem tailTrace_6289695 : CollatzResearch.WordTrace tailWord_6289695 prefixEnd_6289695 1076545568393624757695575 := by
  unfold tailWord_6289695
  simp only [CollatzResearch.WordTrace]
  refine ⟨229404022948516684230126539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152936015299011122820084359 229404022948516684230126539)
  ·
    refine ⟨344106034422775026345189809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229404022948516684230126539 344106034422775026345189809)
    ·
      refine ⟨258079525817081269758892357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344106034422775026345189809 258079525817081269758892357)
      ·
        refine ⟨48389911090702738079792317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 258079525817081269758892357 48389911090702738079792317)
        ·
          refine ⟨18146216659013526779922119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48389911090702738079792317 18146216659013526779922119)
          ·
            refine ⟨27219324988520290169883179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18146216659013526779922119 27219324988520290169883179)
            ·
              refine ⟨40828987482780435254824769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27219324988520290169883179 40828987482780435254824769)
              ·
                refine ⟨30621740612085326441118577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40828987482780435254824769 30621740612085326441118577)
                ·
                  refine ⟨22966305459063994830838933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30621740612085326441118577 22966305459063994830838933)
                  ·
                    refine ⟨1076545568393624757695575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22966305459063994830838933 1076545568393624757695575)
                    ·
                      rfl

theorem cell23_6289695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 6].length) (baseStart_6289695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289695 prefixEnd_6289695 := by exact prefixLift 6289695
  have htrace : WordTrace (prefixWord ++ tailWord_6289695) baseStart_6289695 baseEnd_6289695 := by
    simpa [prefixWord, tailWord_6289695, baseEnd_6289695] using wordTrace_append hprefix tailTrace_6289695
  have hstable : (prefixWord ++ tailWord_6289695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289695).length < 2 ^ (prefixWord ++ tailWord_6289695).sum := by decide
  have hdescent : baseEnd_6289695 < baseStart_6289695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289696 : List Nat := [2, 1, 1, 5, 2, 3, 1, 2, 2, 1, 3]
def baseStart_6289696 : Nat := 118140960795 + 6289696 * 2 ^ 59
def prefixEnd_6289696 : Nat := 4983230072969 + 3 ^ 40 * 6289696 * 2
def baseEnd_6289696 : Nat := 3229637218661528769174221

theorem tailTrace_6289696 : CollatzResearch.WordTrace tailWord_6289696 prefixEnd_6289696 3229637218661528769174221 := by
  unfold tailWord_6289696
  simp only [CollatzResearch.WordTrace]
  refine ⟨114702029710756530700456471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152936039614342040933941961 114702029710756530700456471)
  ·
    refine ⟨172053044566134796050684707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114702029710756530700456471 172053044566134796050684707)
    ·
      refine ⟨258079566849202194076027061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172053044566134796050684707 258079566849202194076027061)
      ·
        refine ⟨24194959392112705694627537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 258079566849202194076027061 24194959392112705694627537)
        ·
          refine ⟨18146219544084529270970653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24194959392112705694627537 18146219544084529270970653)
          ·
            refine ⟨6804832329031698476613995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18146219544084529270970653 6804832329031698476613995)
            ·
              refine ⟨10207248493547547714920993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6804832329031698476613995 10207248493547547714920993)
              ·
                refine ⟨7655436370160660786190745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10207248493547547714920993 7655436370160660786190745)
                ·
                  refine ⟨5741577277620495589643059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7655436370160660786190745 5741577277620495589643059)
                  ·
                    refine ⟨8612365916430743384464589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5741577277620495589643059 8612365916430743384464589)
                    ·
                      refine ⟨3229637218661528769174221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8612365916430743384464589 3229637218661528769174221)
                      ·
                        rfl

theorem cell23_6289696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_6289696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289696 prefixEnd_6289696 := by exact prefixLift 6289696
  have htrace : WordTrace (prefixWord ++ tailWord_6289696) baseStart_6289696 baseEnd_6289696 := by
    simpa [prefixWord, tailWord_6289696, baseEnd_6289696] using wordTrace_append hprefix tailTrace_6289696
  have hstable : (prefixWord ++ tailWord_6289696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289696).length < 2 ^ (prefixWord ++ tailWord_6289696).sum := by decide
  have hdescent : baseEnd_6289696 < baseStart_6289696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289715 : List Nat := [1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 4]
def baseStart_6289715 : Nat := 118140960795 + 6289715 * 2 ^ 59
def prefixEnd_6289715 : Nat := 4983230072969 + 3 ^ 40 * 6289715 * 2
def baseEnd_6289715 : Nat := 3229646974793964194836633

theorem tailTrace_6289715 : CollatzResearch.WordTrace tailWord_6289715 prefixEnd_6289715 3229646974793964194836633 := by
  unfold tailWord_6289715
  simp only [CollatzResearch.WordTrace]
  refine ⟨229404752408444227645854599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152936501605629485097236399 229404752408444227645854599)
  ·
    refine ⟨344107128612666341468781899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229404752408444227645854599 344107128612666341468781899)
    ·
      refine ⟨516160692918999512203172849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344107128612666341468781899 516160692918999512203172849)
      ·
        refine ⟨387120519689249634152379637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 516160692918999512203172849 387120519689249634152379637)
        ·
          refine ⟨36292548720867153201785591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 387120519689249634152379637 36292548720867153201785591)
          ·
            refine ⟨54438823081300729802678387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36292548720867153201785591 54438823081300729802678387)
            ·
              refine ⟨81658234621951094704017581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54438823081300729802678387 81658234621951094704017581)
              ·
                refine ⟨30621837983231660514006593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81658234621951094704017581 30621837983231660514006593)
                ·
                  refine ⟨22966378487423745385504945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30621837983231660514006593 22966378487423745385504945)
                  ·
                    refine ⟨17224783865567809039128709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22966378487423745385504945 17224783865567809039128709)
                    ·
                      refine ⟨3229646974793964194836633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17224783865567809039128709 3229646974793964194836633)
                      ·
                        rfl

theorem cell23_6289715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 4].length) (baseStart_6289715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289715 prefixEnd_6289715 := by exact prefixLift 6289715
  have htrace : WordTrace (prefixWord ++ tailWord_6289715) baseStart_6289715 baseEnd_6289715 := by
    simpa [prefixWord, tailWord_6289715, baseEnd_6289715] using wordTrace_append hprefix tailTrace_6289715
  have hstable : (prefixWord ++ tailWord_6289715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289715).length < 2 ^ (prefixWord ++ tailWord_6289715).sum := by decide
  have hdescent : baseEnd_6289715 < baseStart_6289715 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289719 : List Nat := [1, 1, 3, 1, 2, 1, 1, 7, 2, 2, 2]
def baseStart_6289719 : Nat := 118140960795 + 6289719 * 2 ^ 59
def prefixEnd_6289719 : Nat := 4983230072969 + 3 ^ 40 * 6289719 * 2
def baseEnd_6289719 : Nat := 3229649028716582179186615

theorem tailTrace_6289719 : CollatzResearch.WordTrace tailWord_6289719 prefixEnd_6289719 3229649028716582179186615 := by
  unfold tailWord_6289719
  simp only [CollatzResearch.WordTrace]
  refine ⟨229404898300429736329000211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152936598866953157552666807 229404898300429736329000211)
  ·
    refine ⟨344107347450644604493500317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229404898300429736329000211 344107347450644604493500317)
    ·
      refine ⟨129040255293991726685062619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344107347450644604493500317 129040255293991726685062619)
      ·
        refine ⟨193560382940987590027593929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129040255293991726685062619 193560382940987590027593929)
        ·
          refine ⟨145170287205740692520695447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193560382940987590027593929 145170287205740692520695447)
          ·
            refine ⟨217755430808611038781043171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145170287205740692520695447 217755430808611038781043171)
            ·
              refine ⟨326633146212916558171564757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217755430808611038781043171 326633146212916558171564757)
              ·
                refine ⟨7655464364365231832146049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 326633146212916558171564757 7655464364365231832146049)
                ·
                  refine ⟨5741598273273923874109537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7655464364365231832146049 5741598273273923874109537)
                  ·
                    refine ⟨4306198704955442905582153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5741598273273923874109537 4306198704955442905582153)
                    ·
                      refine ⟨3229649028716582179186615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4306198704955442905582153 3229649028716582179186615)
                      ·
                        rfl

theorem cell23_6289719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 2, 2, 2].length) (baseStart_6289719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289719 prefixEnd_6289719 := by exact prefixLift 6289719
  have htrace : WordTrace (prefixWord ++ tailWord_6289719) baseStart_6289719 baseEnd_6289719 := by
    simpa [prefixWord, tailWord_6289719, baseEnd_6289719] using wordTrace_append hprefix tailTrace_6289719
  have hstable : (prefixWord ++ tailWord_6289719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289719).length < 2 ^ (prefixWord ++ tailWord_6289719).sum := by decide
  have hdescent : baseEnd_6289719 < baseStart_6289719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289742 : List Nat := [4, 1, 1, 1, 1, 1, 2, 7, 5]
def baseStart_6289742 : Nat := 118140960795 + 6289742 * 2 ^ 59
def prefixEnd_6289742 : Nat := 4983230072969 + 3 ^ 40 * 6289742 * 2
def baseEnd_6289742 : Nat := 358851204307959509911001

theorem tailTrace_6289742 : CollatzResearch.WordTrace tailWord_6289742 prefixEnd_6289742 358851204307959509911001 := by
  unfold tailWord_6289742
  simp only [CollatzResearch.WordTrace]
  refine ⟨28675717147418301407135935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152937158119564274171391653 28675717147418301407135935)
  ·
    refine ⟨43013575721127452110703903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28675717147418301407135935 43013575721127452110703903)
    ·
      refine ⟨64520363581691178166055855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43013575721127452110703903 64520363581691178166055855)
      ·
        refine ⟨96780545372536767249083783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64520363581691178166055855 96780545372536767249083783)
        ·
          refine ⟨145170818058805150873625675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96780545372536767249083783 145170818058805150873625675)
          ·
            refine ⟨217756227088207726310438513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145170818058805150873625675 217756227088207726310438513)
            ·
              refine ⟨163317170316155794732828885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217756227088207726310438513 163317170316155794732828885)
              ·
                refine ⟨3827746179284901439050677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 163317170316155794732828885 3827746179284901439050677)
                ·
                  refine ⟨358851204307959509911001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3827746179284901439050677 358851204307959509911001)
                  ·
                    rfl

theorem cell23_6289742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 7, 5].length) (baseStart_6289742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289742 prefixEnd_6289742 := by exact prefixLift 6289742
  have htrace : WordTrace (prefixWord ++ tailWord_6289742) baseStart_6289742 baseEnd_6289742 := by
    simpa [prefixWord, tailWord_6289742, baseEnd_6289742] using wordTrace_append hprefix tailTrace_6289742
  have hstable : (prefixWord ++ tailWord_6289742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289742).length < 2 ^ (prefixWord ++ tailWord_6289742).sum := by decide
  have hdescent : baseEnd_6289742 < baseStart_6289742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289765 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 7]
def baseStart_6289765 : Nat := 118140960795 + 6289765 * 2 ^ 59
def prefixEnd_6289765 : Nat := 4983230072969 + 3 ^ 40 * 6289765 * 2
def baseEnd_6289765 : Nat := 3229672648826688999211403

theorem tailTrace_6289765 : CollatzResearch.WordTrace tailWord_6289765 prefixEnd_6289765 3229672648826688999211403 := by
  unfold tailWord_6289765
  simp only [CollatzResearch.WordTrace]
  refine ⟨229406576058263086185174749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152937717372175390790116499 229406576058263086185174749)
  ·
    refine ⟨86027466021848657319440531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229406576058263086185174749 86027466021848657319440531)
    ·
      refine ⟨129041199032772985979160797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86027466021848657319440531 129041199032772985979160797)
      ·
        refine ⟨48390449637289869742185299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129041199032772985979160797 48390449637289869742185299)
        ·
          refine ⟨72585674455934804613277949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48390449637289869742185299 72585674455934804613277949)
          ·
            refine ⟨27219627920975551729979231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72585674455934804613277949 27219627920975551729979231)
            ·
              refine ⟨40829441881463327594968847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27219627920975551729979231 40829441881463327594968847)
              ·
                refine ⟨61244162822194991392453271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40829441881463327594968847 61244162822194991392453271)
                ·
                  refine ⟨91866244233292487088679907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61244162822194991392453271 91866244233292487088679907)
                  ·
                    refine ⟨137799366349938730633019861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91866244233292487088679907 137799366349938730633019861)
                    ·
                      refine ⟨3229672648826688999211403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 137799366349938730633019861 3229672648826688999211403)
                      ·
                        rfl

theorem cell23_6289765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_6289765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289765 prefixEnd_6289765 := by exact prefixLift 6289765
  have htrace : WordTrace (prefixWord ++ tailWord_6289765) baseStart_6289765 baseEnd_6289765 := by
    simpa [prefixWord, tailWord_6289765, baseEnd_6289765] using wordTrace_append hprefix tailTrace_6289765
  have hstable : (prefixWord ++ tailWord_6289765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289765).length < 2 ^ (prefixWord ++ tailWord_6289765).sum := by decide
  have hdescent : baseEnd_6289765 < baseStart_6289765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289770 : List Nat := [3, 1, 3, 3, 1, 3, 2, 1, 2, 2, 2]
def baseStart_6289770 : Nat := 118140960795 + 6289770 * 2 ^ 59
def prefixEnd_6289770 : Nat := 4983230072969 + 3 ^ 40 * 6289770 * 2
def baseEnd_6289770 : Nat := 3229675216229961479648881

theorem tailTrace_6289770 : CollatzResearch.WordTrace tailWord_6289770 prefixEnd_6289770 3229675216229961479648881 := by
  unfold tailWord_6289770
  simp only [CollatzResearch.WordTrace]
  refine ⟨57351689605811243009776691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152937838948829981359404509 57351689605811243009776691)
  ·
    refine ⟨86027534408716864514665037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57351689605811243009776691 86027534408716864514665037)
    ·
      refine ⟨32260325403268824192999389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86027534408716864514665037 32260325403268824192999389)
      ·
        refine ⟨12097622026225809072374771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32260325403268824192999389 12097622026225809072374771)
        ·
          refine ⟨18146433039338713608562157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12097622026225809072374771 18146433039338713608562157)
          ·
            refine ⟨6804912389752017603210809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18146433039338713608562157 6804912389752017603210809)
            ·
              refine ⟨5103684292314013202408107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6804912389752017603210809 5103684292314013202408107)
              ·
                refine ⟨7655526438471019803612161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5103684292314013202408107 7655526438471019803612161)
                ·
                  refine ⟨5741644828853264852709121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7655526438471019803612161 5741644828853264852709121)
                  ·
                    refine ⟨4306233621639948639531841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5741644828853264852709121 4306233621639948639531841)
                    ·
                      refine ⟨3229675216229961479648881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4306233621639948639531841 3229675216229961479648881)
                      ·
                        rfl

theorem cell23_6289770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_6289770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289770 prefixEnd_6289770 := by exact prefixLift 6289770
  have htrace : WordTrace (prefixWord ++ tailWord_6289770) baseStart_6289770 baseEnd_6289770 := by
    simpa [prefixWord, tailWord_6289770, baseEnd_6289770] using wordTrace_append hprefix tailTrace_6289770
  have hstable : (prefixWord ++ tailWord_6289770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289770).length < 2 ^ (prefixWord ++ tailWord_6289770).sum := by decide
  have hdescent : baseEnd_6289770 < baseStart_6289770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289775 : List Nat := [1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 4]
def baseStart_6289775 : Nat := 118140960795 + 6289775 * 2 ^ 59
def prefixEnd_6289775 : Nat := 4983230072969 + 3 ^ 40 * 6289775 * 2
def baseEnd_6289775 : Nat := 3229677783633233960086357

theorem tailTrace_6289775 : CollatzResearch.WordTrace tailWord_6289775 prefixEnd_6289775 3229677783633233960086357 := by
  unfold tailWord_6289775
  simp only [CollatzResearch.WordTrace]
  refine ⟨229406940788226857893038779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152937960525484571928692519 229406940788226857893038779)
  ·
    refine ⟨344110411182340286839558169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229406940788226857893038779 344110411182340286839558169)
    ·
      refine ⟨258082808386755215129668627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344110411182340286839558169 258082808386755215129668627)
      ·
        refine ⟨387124212580132822694502941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258082808386755215129668627 387124212580132822694502941)
        ·
          refine ⟨145171579717549808510438603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 387124212580132822694502941 145171579717549808510438603)
          ·
            refine ⟨217757369576324712765657905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145171579717549808510438603 217757369576324712765657905)
            ·
              refine ⟨163318027182243534574243429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217757369576324712765657905 163318027182243534574243429)
              ·
                refine ⟨30622130096670662732670643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163318027182243534574243429 30622130096670662732670643)
                ·
                  refine ⟨45933195145005994099005965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30622130096670662732670643 45933195145005994099005965)
                  ·
                    refine ⟨17224948179377247787127237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45933195145005994099005965 17224948179377247787127237)
                    ·
                      refine ⟨3229677783633233960086357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17224948179377247787127237 3229677783633233960086357)
                      ·
                        rfl

theorem cell23_6289775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 4].length) (baseStart_6289775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289775 prefixEnd_6289775 := by exact prefixLift 6289775
  have htrace : WordTrace (prefixWord ++ tailWord_6289775) baseStart_6289775 baseEnd_6289775 := by
    simpa [prefixWord, tailWord_6289775, baseEnd_6289775] using wordTrace_append hprefix tailTrace_6289775
  have hstable : (prefixWord ++ tailWord_6289775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289775).length < 2 ^ (prefixWord ++ tailWord_6289775).sum := by decide
  have hdescent : baseEnd_6289775 < baseStart_6289775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289792 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 6, 4, 2]
def baseStart_6289792 : Nat := 118140960795 + 6289792 * 2 ^ 59
def prefixEnd_6289792 : Nat := 4983230072969 + 3 ^ 40 * 6289792 * 2
def baseEnd_6289792 : Nat := 3229686512804360393573779

theorem tailTrace_6289792 : CollatzResearch.WordTrace tailWord_6289792 prefixEnd_6289792 3229686512804360393573779 := by
  unfold tailWord_6289792
  simp only [CollatzResearch.WordTrace]
  refine ⟨114703780414582634898203815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152938373886110179864271753 114703780414582634898203815)
  ·
    refine ⟨172055670621873952347305723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114703780414582634898203815 172055670621873952347305723)
    ·
      refine ⟨258083505932810928520958585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172055670621873952347305723 258083505932810928520958585)
      ·
        refine ⟨193562629449608196390718939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258083505932810928520958585 193562629449608196390718939)
        ·
          refine ⟨290343944174412294586078409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193562629449608196390718939 290343944174412294586078409)
          ·
            refine ⟨217757958130809220939558807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290343944174412294586078409 217757958130809220939558807)
            ·
              refine ⟨326636937196213831409338211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217757958130809220939558807 326636937196213831409338211)
              ·
                refine ⟨489955405794320747114007317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 326636937196213831409338211 489955405794320747114007317)
                ·
                  refine ⟨22966659646608785020969093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 489955405794320747114007317 22966659646608785020969093)
                  ·
                    refine ⟨4306248683739147191431705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22966659646608785020969093 4306248683739147191431705)
                    ·
                      refine ⟨3229686512804360393573779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4306248683739147191431705 3229686512804360393573779)
                      ·
                        rfl

theorem cell23_6289792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 6, 4, 2].length) (baseStart_6289792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289792 prefixEnd_6289792 := by exact prefixLift 6289792
  have htrace : WordTrace (prefixWord ++ tailWord_6289792) baseStart_6289792 baseEnd_6289792 := by
    simpa [prefixWord, tailWord_6289792, baseEnd_6289792] using wordTrace_append hprefix tailTrace_6289792
  have hstable : (prefixWord ++ tailWord_6289792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289792).length < 2 ^ (prefixWord ++ tailWord_6289792).sum := by decide
  have hdescent : baseEnd_6289792 < baseStart_6289792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289815 : List Nat := [1, 1, 3, 3, 1, 1, 2, 3, 8]
def baseStart_6289815 : Nat := 118140960795 + 6289815 * 2 ^ 59
def prefixEnd_6289815 : Nat := 4983230072969 + 3 ^ 40 * 6289815 * 2
def baseEnd_6289815 : Nat := 358855369206601533731797

theorem tailTrace_6289815 : CollatzResearch.WordTrace tailWord_6289815 prefixEnd_6289815 358855369206601533731797 := by
  unfold tailWord_6289815
  simp only [CollatzResearch.WordTrace]
  refine ⟨229408399708081944724494899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152938933138721296482996599 229408399708081944724494899)
  ·
    refine ⟨344112599562122917086742349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229408399708081944724494899 344112599562122917086742349)
    ·
      refine ⟨129042224835796093907528381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344112599562122917086742349 129042224835796093907528381)
      ·
        refine ⟨48390834313423535215323143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129042224835796093907528381 48390834313423535215323143)
        ·
          refine ⟨72586251470135302822984715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48390834313423535215323143 72586251470135302822984715)
          ·
            refine ⟨108879377205202954234477073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72586251470135302822984715 108879377205202954234477073)
            ·
              refine ⟨81659532903902215675857805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108879377205202954234477073 81659532903902215675857805)
              ·
                refine ⟨30622324838963330878446677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81659532903902215675857805 30622324838963330878446677)
                ·
                  refine ⟨358855369206601533731797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30622324838963330878446677 358855369206601533731797)
                  ·
                    rfl

theorem cell23_6289815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 8].length) (baseStart_6289815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289815 prefixEnd_6289815 := by exact prefixLift 6289815
  have htrace : WordTrace (prefixWord ++ tailWord_6289815) baseStart_6289815 baseEnd_6289815 := by
    simpa [prefixWord, tailWord_6289815, baseEnd_6289815] using wordTrace_append hprefix tailTrace_6289815
  have hstable : (prefixWord ++ tailWord_6289815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289815).length < 2 ^ (prefixWord ++ tailWord_6289815).sum := by decide
  have hdescent : baseEnd_6289815 < baseStart_6289815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289855 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 5]
def baseStart_6289855 : Nat := 118140960795 + 6289855 * 2 ^ 59
def prefixEnd_6289855 : Nat := 4983230072969 + 3 ^ 40 * 6289855 * 2
def baseEnd_6289855 : Nat := 3229718862085593647085989

theorem tailTrace_6289855 : CollatzResearch.WordTrace tailWord_6289855 prefixEnd_6289855 3229718862085593647085989 := by
  unfold tailWord_6289855
  simp only [CollatzResearch.WordTrace]
  refine ⟨229409858627937031555951019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152939905751958021037300679 229409858627937031555951019)
  ·
    refine ⟨344114787941905547333926529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229409858627937031555951019 344114787941905547333926529)
    ·
      refine ⟨258086090956429160500444897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344114787941905547333926529 258086090956429160500444897)
      ·
        refine ⟨193564568217321870375333673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258086090956429160500444897 193564568217321870375333673)
        ·
          refine ⟨145173426162991402781500255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193564568217321870375333673 145173426162991402781500255)
          ·
            refine ⟨217760139244487104172250383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145173426162991402781500255 217760139244487104172250383)
            ·
              refine ⟨326640208866730656258375575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217760139244487104172250383 326640208866730656258375575)
              ·
                refine ⟨489960313300095984387563363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 326640208866730656258375575 489960313300095984387563363)
                ·
                  refine ⟨734940469950143976581345045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 489960313300095984387563363 734940469950143976581345045)
                  ·
                    refine ⟨34450334528912998902250549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 734940469950143976581345045 34450334528912998902250549)
                    ·
                      refine ⟨3229718862085593647085989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34450334528912998902250549 3229718862085593647085989)
                      ·
                        rfl

theorem cell23_6289855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_6289855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289855 prefixEnd_6289855 := by exact prefixLift 6289855
  have htrace : WordTrace (prefixWord ++ tailWord_6289855) baseStart_6289855 baseEnd_6289855 := by
    simpa [prefixWord, tailWord_6289855, baseEnd_6289855] using wordTrace_append hprefix tailTrace_6289855
  have hstable : (prefixWord ++ tailWord_6289855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289855).length < 2 ^ (prefixWord ++ tailWord_6289855).sum := by decide
  have hdescent : baseEnd_6289855 < baseStart_6289855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289876 : List Nat := [2, 4, 1, 2, 2, 1, 1, 3, 3, 1, 3]
def baseStart_6289876 : Nat := 118140960795 + 6289876 * 2 ^ 59
def prefixEnd_6289876 : Nat := 4983230072969 + 3 ^ 40 * 6289876 * 2
def baseEnd_6289876 : Nat := 3229729645179338064923393

theorem tailTrace_6289876 : CollatzResearch.WordTrace tailWord_6289876 prefixEnd_6289876 3229729645179338064923393 := by
  unfold tailWord_6289876
  simp only [CollatzResearch.WordTrace]
  refine ⟨114705312280430476071232741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152940416373907301428310321 114705312280430476071232741)
  ·
    refine ⟨21507246052580714263356139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114705312280430476071232741 21507246052580714263356139)
    ·
      refine ⟨32260869078871071395034209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21507246052580714263356139 32260869078871071395034209)
      ·
        refine ⟨24195651809153303546275657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32260869078871071395034209 24195651809153303546275657)
        ·
          refine ⟨18146738856864977659706743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24195651809153303546275657 18146738856864977659706743)
          ·
            refine ⟨27220108285297466489560115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18146738856864977659706743 27220108285297466489560115)
            ·
              refine ⟨40830162427946199734340173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27220108285297466489560115 40830162427946199734340173)
              ·
                refine ⟨15311310910479824900377565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40830162427946199734340173 15311310910479824900377565)
                ·
                  refine ⟨5741741591429934337641587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15311310910479824900377565 5741741591429934337641587)
                  ·
                    refine ⟨8612612387144901506462381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5741741591429934337641587 8612612387144901506462381)
                    ·
                      refine ⟨3229729645179338064923393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8612612387144901506462381 3229729645179338064923393)
                      ·
                        rfl

theorem cell23_6289876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_6289876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289876 prefixEnd_6289876 := by exact prefixLift 6289876
  have htrace : WordTrace (prefixWord ++ tailWord_6289876) baseStart_6289876 baseEnd_6289876 := by
    simpa [prefixWord, tailWord_6289876, baseEnd_6289876] using wordTrace_append hprefix tailTrace_6289876
  have hstable : (prefixWord ++ tailWord_6289876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289876).length < 2 ^ (prefixWord ++ tailWord_6289876).sum := by decide
  have hdescent : baseEnd_6289876 < baseStart_6289876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289899 : List Nat := [1, 1, 1, 1, 2, 3, 6, 2, 1, 1, 4]
def baseStart_6289899 : Nat := 118140960795 + 6289899 * 2 ^ 59
def prefixEnd_6289899 : Nat := 4983230072969 + 3 ^ 40 * 6289899 * 2
def baseEnd_6289899 : Nat := 3229741455234391474935787

theorem tailTrace_6289899 : CollatzResearch.WordTrace tailWord_6289899 prefixEnd_6289899 3229741455234391474935787 := by
  unfold tailWord_6289899
  simp only [CollatzResearch.WordTrace]
  refine ⟨229411463439777627070552751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152940975626518418047035167 229411463439777627070552751)
  ·
    refine ⟨344117195159666440605829127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229411463439777627070552751 344117195159666440605829127)
    ·
      refine ⟨516175792739499660908743691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344117195159666440605829127 516175792739499660908743691)
      ·
        refine ⟨774263689109249491363115537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516175792739499660908743691 774263689109249491363115537)
        ·
          refine ⟨580697766831937118522336653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 774263689109249491363115537 580697766831937118522336653)
          ·
            refine ⟨217761662561976419445876245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 580697766831937118522336653 217761662561976419445876245)
            ·
              refine ⟨10207577932592644661525449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 217761662561976419445876245 10207577932592644661525449)
              ·
                refine ⟨7655683449444483496144087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10207577932592644661525449 7655683449444483496144087)
                ·
                  refine ⟨11483525174166725244216131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7655683449444483496144087 11483525174166725244216131)
                  ·
                    refine ⟨17225287761250087866324197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11483525174166725244216131 17225287761250087866324197)
                    ·
                      refine ⟨3229741455234391474935787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17225287761250087866324197 3229741455234391474935787)
                      ·
                        rfl

theorem cell23_6289899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 1, 4].length) (baseStart_6289899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289899 prefixEnd_6289899 := by exact prefixLift 6289899
  have htrace : WordTrace (prefixWord ++ tailWord_6289899) baseStart_6289899 baseEnd_6289899 := by
    simpa [prefixWord, tailWord_6289899, baseEnd_6289899] using wordTrace_append hprefix tailTrace_6289899
  have hstable : (prefixWord ++ tailWord_6289899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289899).length < 2 ^ (prefixWord ++ tailWord_6289899).sum := by decide
  have hdescent : baseEnd_6289899 < baseStart_6289899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289912 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 3, 2, 4]
def baseStart_6289912 : Nat := 118140960795 + 6289912 * 2 ^ 59
def prefixEnd_6289912 : Nat := 4983230072969 + 3 ^ 40 * 6289912 * 2
def baseEnd_6289912 : Nat := 3229748130482899924073227

theorem tailTrace_6289912 : CollatzResearch.WordTrace tailWord_6289912 prefixEnd_6289912 3229748130482899924073227 := by
  unfold tailWord_6289912
  simp only [CollatzResearch.WordTrace]
  refine ⟨114705968794365265145387995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152941291725820353527183993 114705968794365265145387995)
  ·
    refine ⟨172058953191547897718081993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114705968794365265145387995 172058953191547897718081993)
    ·
      refine ⟨129044214893660923288561495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172058953191547897718081993 129044214893660923288561495)
      ·
        refine ⟨193566322340491384932842243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129044214893660923288561495 193566322340491384932842243)
        ·
          refine ⟨290349483510737077399263365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193566322340491384932842243 290349483510737077399263365)
          ·
            refine ⟨54440528158263202012361881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 290349483510737077399263365 54440528158263202012361881)
            ·
              refine ⟨40830396118697401509271411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54440528158263202012361881 40830396118697401509271411)
              ·
                refine ⟨61245594178046102263907117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40830396118697401509271411 61245594178046102263907117)
                ·
                  refine ⟨22967097816767288348965169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61245594178046102263907117 22967097816767288348965169)
                  ·
                    refine ⟨17225323362575466261723877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22967097816767288348965169 17225323362575466261723877)
                    ·
                      refine ⟨3229748130482899924073227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17225323362575466261723877 3229748130482899924073227)
                      ·
                        rfl

theorem cell23_6289912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_6289912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289912 prefixEnd_6289912 := by exact prefixLift 6289912
  have htrace : WordTrace (prefixWord ++ tailWord_6289912) baseStart_6289912 baseEnd_6289912 := by
    simpa [prefixWord, tailWord_6289912, baseEnd_6289912] using wordTrace_append hprefix tailTrace_6289912
  have hstable : (prefixWord ++ tailWord_6289912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289912).length < 2 ^ (prefixWord ++ tailWord_6289912).sum := by decide
  have hdescent : baseEnd_6289912 < baseStart_6289912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289919 : List Nat := [1, 1, 2, 2, 1, 2, 3, 5, 1, 2, 3]
def baseStart_6289919 : Nat := 118140960795 + 6289919 * 2 ^ 59
def prefixEnd_6289919 : Nat := 4983230072969 + 3 ^ 40 * 6289919 * 2
def baseEnd_6289919 : Nat := 3229751724847481396685695

theorem tailTrace_6289919 : CollatzResearch.WordTrace tailWord_6289919 prefixEnd_6289919 3229751724847481396685695 := by
  unfold tailWord_6289919
  simp only [CollatzResearch.WordTrace]
  refine ⟨229412192899705170486280811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152941461933136780324187207 229412192899705170486280811)
  ·
    refine ⟨344118289349557755729421217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229412192899705170486280811 344118289349557755729421217)
    ·
      refine ⟨258088717012168316797065913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344118289349557755729421217 258088717012168316797065913)
      ·
        refine ⟨193566537759126237597799435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258088717012168316797065913 193566537759126237597799435)
        ·
          refine ⟨290349806638689356396699153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193566537759126237597799435 290349806638689356396699153)
          ·
            refine ⟨217762354979017017297524365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290349806638689356396699153 217762354979017017297524365)
            ·
              refine ⟨81660883117131381486571637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217762354979017017297524365 81660883117131381486571637)
              ·
                refine ⟨7655707792231067014366091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81660883117131381486571637 7655707792231067014366091)
                ·
                  refine ⟨11483561688346600521549137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7655707792231067014366091 11483561688346600521549137)
                  ·
                    refine ⟨8612671266259950391161853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11483561688346600521549137 8612671266259950391161853)
                    ·
                      refine ⟨3229751724847481396685695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8612671266259950391161853 3229751724847481396685695)
                      ·
                        rfl

theorem cell23_6289919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 2, 3].length) (baseStart_6289919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289919 prefixEnd_6289919 := by exact prefixLift 6289919
  have htrace : WordTrace (prefixWord ++ tailWord_6289919) baseStart_6289919 baseEnd_6289919 := by
    simpa [prefixWord, tailWord_6289919, baseEnd_6289919] using wordTrace_append hprefix tailTrace_6289919
  have hstable : (prefixWord ++ tailWord_6289919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289919).length < 2 ^ (prefixWord ++ tailWord_6289919).sum := by decide
  have hdescent : baseEnd_6289919 < baseStart_6289919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289943 : List Nat := [1, 1, 3, 6, 1, 1, 1, 3, 2, 4]
def baseStart_6289943 : Nat := 118140960795 + 6289943 * 2 ^ 59
def prefixEnd_6289943 : Nat := 4983230072969 + 3 ^ 40 * 6289943 * 2
def baseEnd_6289943 : Nat := 1076588016127729767595195

theorem tailTrace_6289943 : CollatzResearch.WordTrace tailWord_6289943 prefixEnd_6289943 1076588016127729767595195 := by
  unfold tailWord_6289943
  simp only [CollatzResearch.WordTrace]
  refine ⟨229413068251618222585154483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152942045501078815056769655 229413068251618222585154483)
  ·
    refine ⟨344119602377427333877731725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229413068251618222585154483 344119602377427333877731725)
    ·
      refine ⟨129044850891535250204149397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344119602377427333877731725 129044850891535250204149397)
      ·
        refine ⟨6048977385540714853319503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 129044850891535250204149397 6048977385540714853319503)
        ·
          refine ⟨9073466078311072279979255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6048977385540714853319503 9073466078311072279979255)
          ·
            refine ⟨13610199117466608419968883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9073466078311072279979255 13610199117466608419968883)
            ·
              refine ⟨20415298676199912629953325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13610199117466608419968883 20415298676199912629953325)
              ·
                refine ⟨7655737003574967236232497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20415298676199912629953325 7655737003574967236232497)
                ·
                  refine ⟨5741802752681225427174373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7655737003574967236232497 5741802752681225427174373)
                  ·
                    refine ⟨1076588016127729767595195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5741802752681225427174373 1076588016127729767595195)
                    ·
                      rfl

theorem cell23_6289943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 2, 4].length) (baseStart_6289943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289943 prefixEnd_6289943 := by exact prefixLift 6289943
  have htrace : WordTrace (prefixWord ++ tailWord_6289943) baseStart_6289943 baseEnd_6289943 := by
    simpa [prefixWord, tailWord_6289943, baseEnd_6289943] using wordTrace_append hprefix tailTrace_6289943
  have hstable : (prefixWord ++ tailWord_6289943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289943).length < 2 ^ (prefixWord ++ tailWord_6289943).sum := by decide
  have hdescent : baseEnd_6289943 < baseStart_6289943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6289992 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 1, 3, 5]
def baseStart_6289992 : Nat := 118140960795 + 6289992 * 2 ^ 59
def prefixEnd_6289992 : Nat := 4983230072969 + 3 ^ 40 * 6289992 * 2
def baseEnd_6289992 : Nat := 3229789208935259611072859

theorem tailTrace_6289992 : CollatzResearch.WordTrace tailWord_6289992 prefixEnd_6289992 3229789208935259611072859 := by
  unfold tailWord_6289992
  simp only [CollatzResearch.WordTrace]
  refine ⟨114707427714220351976844115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152943236952293802635792153 114707427714220351976844115)
  ·
    refine ⟨172061141571330527965266173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114707427714220351976844115 172061141571330527965266173)
    ·
      refine ⟨64522928089248947986974815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172061141571330527965266173 64522928089248947986974815)
      ·
        refine ⟨96784392133873421980462223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64522928089248947986974815 96784392133873421980462223)
        ·
          refine ⟨145176588200810132970693335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96784392133873421980462223 145176588200810132970693335)
          ·
            refine ⟨217764882301215199456040003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145176588200810132970693335 217764882301215199456040003)
            ·
              refine ⟨326647323451822799184060005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217764882301215199456040003 326647323451822799184060005)
              ·
                refine ⟨61246373147216774847011251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 326647323451822799184060005 61246373147216774847011251)
                ·
                  refine ⟨91869559720825162270516877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61246373147216774847011251 91869559720825162270516877)
                  ·
                    refine ⟨34451084895309435851443829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91869559720825162270516877 34451084895309435851443829)
                    ·
                      refine ⟨3229789208935259611072859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34451084895309435851443829 3229789208935259611072859)
                      ·
                        rfl

theorem cell23_6289992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_6289992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6289992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6289992 prefixEnd_6289992 := by exact prefixLift 6289992
  have htrace : WordTrace (prefixWord ++ tailWord_6289992) baseStart_6289992 baseEnd_6289992 := by
    simpa [prefixWord, tailWord_6289992, baseEnd_6289992] using wordTrace_append hprefix tailTrace_6289992
  have hstable : (prefixWord ++ tailWord_6289992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6289992).length < 2 ^ (prefixWord ++ tailWord_6289992).sum := by decide
  have hdescent : baseEnd_6289992 < baseStart_6289992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6289992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290039 : List Nat := [1, 1, 3, 1, 1, 3, 3, 2, 2, 3, 3]
def baseStart_6290039 : Nat := 118140960795 + 6290039 * 2 ^ 59
def prefixEnd_6290039 : Nat := 4983230072969 + 3 ^ 40 * 6290039 * 2
def baseEnd_6290039 : Nat := 3229813342526020927185143

theorem tailTrace_6290039 : CollatzResearch.WordTrace tailWord_6290039 prefixEnd_6290039 3229813342526020927185143 := by
  unfold tailWord_6290039
  simp only [CollatzResearch.WordTrace]
  refine ⟨229416569659270430980649171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152944379772846953987099447 229416569659270430980649171)
  ·
    refine ⟨344124854488905646470973757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229416569659270430980649171 344124854488905646470973757)
    ·
      refine ⟨129046820433339617426615159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344124854488905646470973757 129046820433339617426615159)
      ·
        refine ⟨193570230650009426139922739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129046820433339617426615159 193570230650009426139922739)
        ·
          refine ⟨290355345975014139209884109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193570230650009426139922739 290355345975014139209884109)
          ·
            refine ⟨108883254740630302203706541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 290355345975014139209884109 108883254740630302203706541)
            ·
              refine ⟨40831220527736363326389953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108883254740630302203706541 40831220527736363326389953)
              ·
                refine ⟨30623415395802272494792465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40831220527736363326389953 30623415395802272494792465)
                ·
                  refine ⟨22967561546851704371094349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30623415395802272494792465 22967561546851704371094349)
                  ·
                    refine ⟨8612835580069389139160381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22967561546851704371094349 8612835580069389139160381)
                    ·
                      refine ⟨3229813342526020927185143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8612835580069389139160381 3229813342526020927185143)
                      ·
                        rfl

theorem cell23_6290039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 3, 3].length) (baseStart_6290039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290039 prefixEnd_6290039 := by exact prefixLift 6290039
  have htrace : WordTrace (prefixWord ++ tailWord_6290039) baseStart_6290039 baseEnd_6290039 := by
    simpa [prefixWord, tailWord_6290039, baseEnd_6290039] using wordTrace_append hprefix tailTrace_6290039
  have hstable : (prefixWord ++ tailWord_6290039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290039).length < 2 ^ (prefixWord ++ tailWord_6290039).sum := by decide
  have hdescent : baseEnd_6290039 < baseStart_6290039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290080 : List Nat := [2, 1, 1, 4, 5, 1, 1, 3, 5]
def baseStart_6290080 : Nat := 118140960795 + 6290080 * 2 ^ 59
def prefixEnd_6290080 : Nat := 4983230072969 + 3 ^ 40 * 6290080 * 2
def baseEnd_6290080 : Nat := 358870488359206140752495

theorem tailTrace_6290080 : CollatzResearch.WordTrace tailWord_6290080 prefixEnd_6290080 358870488359206140752495 := by
  unfold tailWord_6290080
  simp only [CollatzResearch.WordTrace]
  refine ⟨114709032526060947491445847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152945376701414596655261129 114709032526060947491445847)
  ·
    refine ⟨172063548789091421237168771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114709032526060947491445847 172063548789091421237168771)
    ·
      refine ⟨258095323183637131855753157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172063548789091421237168771 258095323183637131855753157)
      ·
        refine ⟨48392873096931962222953717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 258095323183637131855753157 48392873096931962222953717)
        ·
          refine ⟨4536831852837371458401911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48392873096931962222953717 4536831852837371458401911)
          ·
            refine ⟨6805247779256057187602867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4536831852837371458401911 6805247779256057187602867)
            ·
              refine ⟨10207871668884085781404301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6805247779256057187602867 10207871668884085781404301)
              ·
                refine ⟨3827951875831532168026613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10207871668884085781404301 3827951875831532168026613)
                ·
                  refine ⟨358870488359206140752495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3827951875831532168026613 358870488359206140752495)
                  ·
                    rfl

theorem cell23_6290080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 3, 5].length) (baseStart_6290080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290080 prefixEnd_6290080 := by exact prefixLift 6290080
  have htrace : WordTrace (prefixWord ++ tailWord_6290080) baseStart_6290080 baseEnd_6290080 := by
    simpa [prefixWord, tailWord_6290080, baseEnd_6290080] using wordTrace_append hprefix tailTrace_6290080
  have hstable : (prefixWord ++ tailWord_6290080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290080).length < 2 ^ (prefixWord ++ tailWord_6290080).sum := by decide
  have hdescent : baseEnd_6290080 < baseStart_6290080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290089 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 7, 4]
def baseStart_6290089 : Nat := 118140960795 + 6290089 * 2 ^ 59
def prefixEnd_6290089 : Nat := 4983230072969 + 3 ^ 40 * 6290089 * 2
def baseEnd_6290089 : Nat := 1076613005519581910519971

theorem tailTrace_6290089 : CollatzResearch.WordTrace tailWord_6290089 prefixEnd_6290089 1076613005519581910519971 := by
  unfold tailWord_6290089
  simp only [CollatzResearch.WordTrace]
  refine ⟨229418393309089289519969321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152945595539392859679979547 229418393309089289519969321)
  ·
    refine ⟨172063794981816967139976991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229418393309089289519969321 172063794981816967139976991)
    ·
      refine ⟨258095692472725450709965487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172063794981816967139976991 258095692472725450709965487)
      ·
        refine ⟨387143538709088176064948231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258095692472725450709965487 387143538709088176064948231)
        ·
          refine ⟨580715308063632264097422347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387143538709088176064948231 580715308063632264097422347)
          ·
            refine ⟨871072962095448396146133521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580715308063632264097422347 871072962095448396146133521)
            ·
              refine ⟨653304721571586297109600141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 871072962095448396146133521 653304721571586297109600141)
              ·
                refine ⟨244989270589344861416100053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 653304721571586297109600141 244989270589344861416100053)
                ·
                  refine ⟨5741936029437770189439845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 244989270589344861416100053 5741936029437770189439845)
                  ·
                    refine ⟨1076613005519581910519971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5741936029437770189439845 1076613005519581910519971)
                    ·
                      rfl

theorem cell23_6290089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 7, 4].length) (baseStart_6290089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290089 prefixEnd_6290089 := by exact prefixLift 6290089
  have htrace : WordTrace (prefixWord ++ tailWord_6290089) baseStart_6290089 baseEnd_6290089 := by
    simpa [prefixWord, tailWord_6290089, baseEnd_6290089] using wordTrace_append hprefix tailTrace_6290089
  have hstable : (prefixWord ++ tailWord_6290089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290089).length < 2 ^ (prefixWord ++ tailWord_6290089).sum := by decide
  have hdescent : baseEnd_6290089 < baseStart_6290089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290156 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 3, 5, 2]
def baseStart_6290156 : Nat := 118140960795 + 6290156 * 2 ^ 59
def prefixEnd_6290156 : Nat := 4983230072969 + 3 ^ 40 * 6290156 * 2
def baseEnd_6290156 : Nat := 3229873419762596969422105

theorem tailTrace_6290156 : CollatzResearch.WordTrace tailWord_6290156 prefixEnd_6290156 3229873419762596969422105 := by
  unfold tailWord_6290156
  simp only [CollatzResearch.WordTrace]
  refine ⟨114710418499923279981329161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152947224666564373308438881 114710418499923279981329161)
  ·
    refine ⟨86032813874942459985996871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114710418499923279981329161 86032813874942459985996871)
    ·
      refine ⟨129049220812413689978995307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86032813874942459985996871 129049220812413689978995307)
      ·
        refine ⟨193573831218620534968492961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129049220812413689978995307 193573831218620534968492961)
        ·
          refine ⟨145180373413965401226369721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193573831218620534968492961 145180373413965401226369721)
          ·
            refine ⟨108885280060474050919777291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145180373413965401226369721 108885280060474050919777291)
            ·
              refine ⟨163327920090711076379665937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108885280060474050919777291 163327920090711076379665937)
              ·
                refine ⟨122495940068033307284749453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163327920090711076379665937 122495940068033307284749453)
                ·
                  refine ⟨45935977525512490231781045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122495940068033307284749453 45935977525512490231781045)
                  ·
                    refine ⟨4306497893016795959229473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45935977525512490231781045 4306497893016795959229473)
                    ·
                      refine ⟨3229873419762596969422105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4306497893016795959229473 3229873419762596969422105)
                      ·
                        rfl

theorem cell23_6290156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 5, 2].length) (baseStart_6290156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290156 prefixEnd_6290156 := by exact prefixLift 6290156
  have htrace : WordTrace (prefixWord ++ tailWord_6290156) baseStart_6290156 baseEnd_6290156 := by
    simpa [prefixWord, tailWord_6290156, baseEnd_6290156] using wordTrace_append hprefix tailTrace_6290156
  have hstable : (prefixWord ++ tailWord_6290156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290156).length < 2 ^ (prefixWord ++ tailWord_6290156).sum := by decide
  have hdescent : baseEnd_6290156 < baseStart_6290156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290166 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 5, 5]
def baseStart_6290166 : Nat := 118140960795 + 6290166 * 2 ^ 59
def prefixEnd_6290166 : Nat := 4983230072969 + 3 ^ 40 * 6290166 * 2
def baseEnd_6290166 : Nat := 1076626184856380643432353

theorem tailTrace_6290166 : CollatzResearch.WordTrace tailWord_6290166 prefixEnd_6290166 1076626184856380643432353 := by
  unfold tailWord_6290166
  simp only [CollatzResearch.WordTrace]
  refine ⟨14338825108113145729407647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152947467819873554447014901 14338825108113145729407647)
  ·
    refine ⟨21508237662169718594111471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14338825108113145729407647 21508237662169718594111471)
    ·
      refine ⟨32262356493254577891167207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21508237662169718594111471 32262356493254577891167207)
      ·
        refine ⟨48393534739881866836750811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32262356493254577891167207 48393534739881866836750811)
        ·
          refine ⟨72590302109822800255126217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48393534739881866836750811 72590302109822800255126217)
          ·
            refine ⟨54442726582367100191344663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72590302109822800255126217 54442726582367100191344663)
            ·
              refine ⟨81664089873550650287016995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54442726582367100191344663 81664089873550650287016995)
              ·
                refine ⟨122496134810325975430525493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81664089873550650287016995 122496134810325975430525493)
                ·
                  refine ⟨11484012638468060196611765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122496134810325975430525493 11484012638468060196611765)
                  ·
                    refine ⟨1076626184856380643432353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11484012638468060196611765 1076626184856380643432353)
                    ·
                      rfl

theorem cell23_6290166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_6290166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290166 prefixEnd_6290166 := by exact prefixLift 6290166
  have htrace : WordTrace (prefixWord ++ tailWord_6290166) baseStart_6290166 baseEnd_6290166 := by
    simpa [prefixWord, tailWord_6290166, baseEnd_6290166] using wordTrace_append hprefix tailTrace_6290166
  have hstable : (prefixWord ++ tailWord_6290166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290166).length < 2 ^ (prefixWord ++ tailWord_6290166).sum := by decide
  have hdescent : baseEnd_6290166 < baseStart_6290166 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290186 : List Nat := [3, 1, 2, 2, 1, 2, 1, 3, 3, 1, 4]
def baseStart_6290186 : Nat := 118140960795 + 6290186 * 2 ^ 59
def prefixEnd_6290186 : Nat := 4983230072969 + 3 ^ 40 * 6290186 * 2
def baseEnd_6290186 : Nat := 3229888824182231852046967

theorem tailTrace_6290186 : CollatzResearch.WordTrace tailWord_6290186 prefixEnd_6290186 3229888824182231852046967 := by
  unfold tailWord_6290186
  simp only [CollatzResearch.WordTrace]
  refine ⟨57355482797434468771562603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152947954126491916724166941 57355482797434468771562603)
  ·
    refine ⟨86033224196151703157343905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57355482797434468771562603 86033224196151703157343905)
    ·
      refine ⟨64524918147113777368007929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86033224196151703157343905 64524918147113777368007929)
      ·
        refine ⟨48393688610335333026005947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64524918147113777368007929 48393688610335333026005947)
        ·
          refine ⟨72590532915502999539008921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48393688610335333026005947 72590532915502999539008921)
          ·
            refine ⟨54442899686627249654256691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72590532915502999539008921 54442899686627249654256691)
            ·
              refine ⟨81664349529940874481385037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54442899686627249654256691 81664349529940874481385037)
              ·
                refine ⟨30624131073727827930519389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81664349529940874481385037 30624131073727827930519389)
                ·
                  refine ⟨11484049152647935473944771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30624131073727827930519389 11484049152647935473944771)
                  ·
                    refine ⟨17226073728971903210917157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11484049152647935473944771 17226073728971903210917157)
                    ·
                      refine ⟨3229888824182231852046967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17226073728971903210917157 3229888824182231852046967)
                      ·
                        rfl

theorem cell23_6290186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_6290186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290186 prefixEnd_6290186 := by exact prefixLift 6290186
  have htrace : WordTrace (prefixWord ++ tailWord_6290186) baseStart_6290186 baseEnd_6290186 := by
    simpa [prefixWord, tailWord_6290186, baseEnd_6290186] using wordTrace_append hprefix tailTrace_6290186
  have hstable : (prefixWord ++ tailWord_6290186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290186).length < 2 ^ (prefixWord ++ tailWord_6290186).sum := by decide
  have hdescent : baseEnd_6290186 < baseStart_6290186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290209 : List Nat := [1, 2, 3, 2, 1, 2, 12]
def baseStart_6290209 : Nat := 118140960795 + 6290209 * 2 ^ 59
def prefixEnd_6290209 : Nat := 4983230072969 + 3 ^ 40 * 6290209 * 2
def baseEnd_6290209 : Nat := 39875316472065250148881

theorem tailTrace_6290209 : CollatzResearch.WordTrace tailWord_6290209 prefixEnd_6290209 39875316472065250148881 := by
  unfold tailWord_6290209
  simp only [CollatzResearch.WordTrace]
  refine ⟨229422770068654550014337681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152948513379103033342891787 229422770068654550014337681)
  ·
    refine ⟨172067077551490912510753261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229422770068654550014337681 172067077551490912510753261)
    ·
      refine ⟨64525154081809092191532473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172067077551490912510753261 64525154081809092191532473)
      ·
        refine ⟨48393865561356819143649355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64525154081809092191532473 48393865561356819143649355)
        ·
          refine ⟨72590798342035228715474033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48393865561356819143649355 72590798342035228715474033)
          ·
            refine ⟨54443098756526421536605525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72590798342035228715474033 54443098756526421536605525)
            ·
              refine ⟨39875316472065250148881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 54443098756526421536605525 39875316472065250148881)
              ·
                rfl

theorem cell23_6290209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 12].length) (baseStart_6290209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290209 prefixEnd_6290209 := by exact prefixLift 6290209
  have htrace : WordTrace (prefixWord ++ tailWord_6290209) baseStart_6290209 baseEnd_6290209 := by
    simpa [prefixWord, tailWord_6290209, baseEnd_6290209] using wordTrace_append hprefix tailTrace_6290209
  have hstable : (prefixWord ++ tailWord_6290209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290209).length < 2 ^ (prefixWord ++ tailWord_6290209).sum := by decide
  have hdescent : baseEnd_6290209 < baseStart_6290209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290216 : List Nat := [2, 1, 5, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_6290216 : Nat := 118140960795 + 6290216 * 2 ^ 59
def prefixEnd_6290216 : Nat := 4983230072969 + 3 ^ 40 * 6290216 * 2
def baseEnd_6290216 : Nat := 3229904228601866734671829

theorem tailTrace_6290216 : CollatzResearch.WordTrace tailWord_6290216 prefixEnd_6290216 3229904228601866734671829 := by
  unfold tailWord_6290216
  simp only [CollatzResearch.WordTrace]
  refine ⟨114711512689814595104921251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152948683586419460139895001 114711512689814595104921251)
  ·
    refine ⟨172067269034721892657381877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114711512689814595104921251 172067269034721892657381877)
    ·
      refine ⟨16131306472005177436629551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 172067269034721892657381877 16131306472005177436629551)
      ·
        refine ⟨24196959708007766154944327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16131306472005177436629551 24196959708007766154944327)
        ·
          refine ⟨36295439562011649232416491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24196959708007766154944327 36295439562011649232416491)
          ·
            refine ⟨54443159343017473848624737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36295439562011649232416491 54443159343017473848624737)
            ·
              refine ⟨40832369507263105386468553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54443159343017473848624737 40832369507263105386468553)
              ·
                refine ⟨30624277130447329039851415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40832369507263105386468553 30624277130447329039851415)
                ·
                  refine ⟨45936415695670993559777123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30624277130447329039851415 45936415695670993559777123)
                  ·
                    refine ⟨68904623543506490339665685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45936415695670993559777123 68904623543506490339665685)
                    ·
                      refine ⟨3229904228601866734671829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68904623543506490339665685 3229904228601866734671829)
                      ·
                        rfl

theorem cell23_6290216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_6290216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290216 prefixEnd_6290216 := by exact prefixLift 6290216
  have htrace : WordTrace (prefixWord ++ tailWord_6290216) baseStart_6290216 baseEnd_6290216 := by
    simpa [prefixWord, tailWord_6290216, baseEnd_6290216] using wordTrace_append hprefix tailTrace_6290216
  have hstable : (prefixWord ++ tailWord_6290216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290216).length < 2 ^ (prefixWord ++ tailWord_6290216).sum := by decide
  have hdescent : baseEnd_6290216 < baseStart_6290216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290220 : List Nat := [2, 2, 1, 1, 1, 4, 4, 1, 3, 2, 2]
def baseStart_6290220 : Nat := 118140960795 + 6290220 * 2 ^ 59
def prefixEnd_6290220 : Nat := 4983230072969 + 3 ^ 40 * 6290220 * 2
def baseEnd_6290220 : Nat := 3229906282524484719021811

theorem tailTrace_6290220 : CollatzResearch.WordTrace tailWord_6290220 prefixEnd_6290220 3229906282524484719021811 := by
  unfold tailWord_6290220
  simp only [CollatzResearch.WordTrace]
  refine ⟨114711585635807349446494057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152948780847743132595325409 114711585635807349446494057)
  ·
    refine ⟨86033689226855512084870543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114711585635807349446494057 86033689226855512084870543)
    ·
      refine ⟨129050533840283268127305815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86033689226855512084870543 129050533840283268127305815)
      ·
        refine ⟨193575800760424902190958723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129050533840283268127305815 193575800760424902190958723)
        ·
          refine ⟨290363701140637353286438085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193575800760424902190958723 290363701140637353286438085)
          ·
            refine ⟨54443193963869503741207141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 290363701140637353286438085 54443193963869503741207141)
            ·
              refine ⟨10208098868225531951476339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54443193963869503741207141 10208098868225531951476339)
              ·
                refine ⟨15312148302338297927214509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10208098868225531951476339 15312148302338297927214509)
                ·
                  refine ⟨5742055613376861722705441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15312148302338297927214509 5742055613376861722705441)
                  ·
                    refine ⟨4306541710032646292029081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5742055613376861722705441 4306541710032646292029081)
                    ·
                      refine ⟨3229906282524484719021811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4306541710032646292029081 3229906282524484719021811)
                      ·
                        rfl

theorem cell23_6290220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 2, 2].length) (baseStart_6290220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290220 prefixEnd_6290220 := by exact prefixLift 6290220
  have htrace : WordTrace (prefixWord ++ tailWord_6290220) baseStart_6290220 baseEnd_6290220 := by
    simpa [prefixWord, tailWord_6290220, baseEnd_6290220] using wordTrace_append hprefix tailTrace_6290220
  have hstable : (prefixWord ++ tailWord_6290220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290220).length < 2 ^ (prefixWord ++ tailWord_6290220).sum := by decide
  have hdescent : baseEnd_6290220 < baseStart_6290220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290259 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 8]
def baseStart_6290259 : Nat := 118140960795 + 6290259 * 2 ^ 59
def prefixEnd_6290259 : Nat := 4983230072969 + 3 ^ 40 * 6290259 * 2
def baseEnd_6290259 : Nat := 3229926308270010066434131

theorem tailTrace_6290259 : CollatzResearch.WordTrace tailWord_6290259 prefixEnd_6290259 3229926308270010066434131 := by
  unfold tailWord_6290259
  simp only [CollatzResearch.WordTrace]
  refine ⟨229424593718473408553657831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152949729145648939035771887 229424593718473408553657831)
  ·
    refine ⟨344136890577710112830486747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229424593718473408553657831 344136890577710112830486747)
    ·
      refine ⟨516205335866565169245730121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344136890577710112830486747 516205335866565169245730121)
      ·
        refine ⟨387154001899923876934297591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 516205335866565169245730121 387154001899923876934297591)
        ·
          refine ⟨580731002849885815401446387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387154001899923876934297591 580731002849885815401446387)
          ·
            refine ⟨871096504274828723102169581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580731002849885815401446387 871096504274828723102169581)
            ·
              refine ⟨326661189103060771163313593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 871096504274828723102169581 326661189103060771163313593)
              ·
                refine ⟨244995891827295578372485195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326661189103060771163313593 244995891827295578372485195)
                ·
                  refine ⟨367493837740943367558727793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244995891827295578372485195 367493837740943367558727793)
                  ·
                    refine ⟨275620378305707525669045845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 367493837740943367558727793 275620378305707525669045845)
                    ·
                      refine ⟨3229926308270010066434131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 275620378305707525669045845 3229926308270010066434131)
                      ·
                        rfl

theorem cell23_6290259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 8].length) (baseStart_6290259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290259 prefixEnd_6290259 := by exact prefixLift 6290259
  have htrace : WordTrace (prefixWord ++ tailWord_6290259) baseStart_6290259 baseEnd_6290259 := by
    simpa [prefixWord, tailWord_6290259, baseEnd_6290259] using wordTrace_append hprefix tailTrace_6290259
  have hstable : (prefixWord ++ tailWord_6290259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290259).length < 2 ^ (prefixWord ++ tailWord_6290259).sum := by decide
  have hdescent : baseEnd_6290259 < baseStart_6290259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290296 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 4, 4, 3]
def baseStart_6290296 : Nat := 118140960795 + 6290296 * 2 ^ 59
def prefixEnd_6290296 : Nat := 4983230072969 + 3 ^ 40 * 6290296 * 2
def baseEnd_6290296 : Nat := 3229945307054226421671461

theorem tailTrace_6290296 : CollatzResearch.WordTrace tailWord_6290296 prefixEnd_6290296 3229945307054226421671461 := by
  unfold tailWord_6290296
  simp only [CollatzResearch.WordTrace]
  refine ⟨114712971609669681936377371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152950628812892909248503161 114712971609669681936377371)
  ·
    refine ⟨172069457414504522904566057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114712971609669681936377371 172069457414504522904566057)
    ·
      refine ⟨129052093060878392178424543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172069457414504522904566057 129052093060878392178424543)
      ·
        refine ⟨193578139591317588267636815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129052093060878392178424543 193578139591317588267636815)
        ·
          refine ⟨290367209386976382401455223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193578139591317588267636815 290367209386976382401455223)
          ·
            refine ⟨435550814080464573602182835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290367209386976382401455223 435550814080464573602182835)
            ·
              refine ⟨653326221120696860403274253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 435550814080464573602182835 653326221120696860403274253)
              ·
                refine ⟨244997332920261322651227845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 653326221120696860403274253 244997332920261322651227845)
                ·
                  refine ⟨45936999922548997997105221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 244997332920261322651227845 45936999922548997997105221)
                  ·
                    refine ⟨8613187485477937124457229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45936999922548997997105221 8613187485477937124457229)
                    ·
                      refine ⟨3229945307054226421671461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8613187485477937124457229 3229945307054226421671461)
                      ·
                        rfl

theorem cell23_6290296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 4, 4, 3].length) (baseStart_6290296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290296 prefixEnd_6290296 := by exact prefixLift 6290296
  have htrace : WordTrace (prefixWord ++ tailWord_6290296) baseStart_6290296 baseEnd_6290296 := by
    simpa [prefixWord, tailWord_6290296, baseEnd_6290296] using wordTrace_append hprefix tailTrace_6290296
  have hstable : (prefixWord ++ tailWord_6290296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290296).length < 2 ^ (prefixWord ++ tailWord_6290296).sum := by decide
  have hdescent : baseEnd_6290296 < baseStart_6290296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290297 : List Nat := [1, 2, 1, 3, 2, 5, 1, 2, 1, 3, 2]
def baseStart_6290297 : Nat := 118140960795 + 6290297 * 2 ^ 59
def prefixEnd_6290297 : Nat := 4983230072969 + 3 ^ 40 * 6290297 * 2
def baseEnd_6290297 : Nat := 3229945820534880917758957

theorem tailTrace_6290297 : CollatzResearch.WordTrace tailWord_6290297 prefixEnd_6290297 3229945820534880917758957 := by
  unfold tailWord_6290297
  simp only [CollatzResearch.WordTrace]
  refine ⟨229425979692335741043541145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152950653128223827362360763 229425979692335741043541145)
  ·
    refine ⟨172069484769251805782655859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229425979692335741043541145 172069484769251805782655859)
    ·
      refine ⟨258104227153877708673983789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172069484769251805782655859 258104227153877708673983789)
      ·
        refine ⟨96789085182704140752743921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258104227153877708673983789 96789085182704140752743921)
        ·
          refine ⟨72591813887028105564557941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96789085182704140752743921 72591813887028105564557941)
          ·
            refine ⟨6805482551908884896677307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72591813887028105564557941 6805482551908884896677307)
            ·
              refine ⟨10208223827863327345015961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6805482551908884896677307 10208223827863327345015961)
              ·
                refine ⟨7656167870897495508761971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10208223827863327345015961 7656167870897495508761971)
                ·
                  refine ⟨11484251806346243263142957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7656167870897495508761971 11484251806346243263142957)
                  ·
                    refine ⟨4306594427379841223678609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11484251806346243263142957 4306594427379841223678609)
                    ·
                      refine ⟨3229945820534880917758957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4306594427379841223678609 3229945820534880917758957)
                      ·
                        rfl

theorem cell23_6290297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 3, 2].length) (baseStart_6290297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290297 prefixEnd_6290297 := by exact prefixLift 6290297
  have htrace : WordTrace (prefixWord ++ tailWord_6290297) baseStart_6290297 baseEnd_6290297 := by
    simpa [prefixWord, tailWord_6290297, baseEnd_6290297] using wordTrace_append hprefix tailTrace_6290297
  have hstable : (prefixWord ++ tailWord_6290297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290297).length < 2 ^ (prefixWord ++ tailWord_6290297).sum := by decide
  have hdescent : baseEnd_6290297 < baseStart_6290297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290314 : List Nat := [3, 1, 2, 4, 1, 2, 3, 1, 1, 3, 2]
def baseStart_6290314 : Nat := 118140960795 + 6290314 * 2 ^ 59
def prefixEnd_6290314 : Nat := 4983230072969 + 3 ^ 40 * 6290314 * 2
def baseEnd_6290314 : Nat := 3229954549706007351246379

theorem tailTrace_6290314 : CollatzResearch.WordTrace tailWord_6290314 prefixEnd_6290314 3229954549706007351246379 := by
  unfold tailWord_6290314
  simp only [CollatzResearch.WordTrace]
  refine ⟨57356649933318538236727499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152951066488849435297939997 57356649933318538236727499)
  ·
    refine ⟨86034974899977807355091249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57356649933318538236727499 86034974899977807355091249)
    ·
      refine ⟨64526231174983355516318437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86034974899977807355091249 64526231174983355516318437)
      ·
        refine ⟨12098668345309379159309707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64526231174983355516318437 12098668345309379159309707)
        ·
          refine ⟨18148002517964068738964561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12098668345309379159309707 18148002517964068738964561)
          ·
            refine ⟨13611001888473051554223421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18148002517964068738964561 13611001888473051554223421)
            ·
              refine ⟨5104125708177394332833783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13611001888473051554223421 5104125708177394332833783)
              ·
                refine ⟨7656188562266091499250675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5104125708177394332833783 7656188562266091499250675)
                ·
                  refine ⟨11484282843399137248876013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7656188562266091499250675 11484282843399137248876013)
                  ·
                    refine ⟨4306606066274676468328505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11484282843399137248876013 4306606066274676468328505)
                    ·
                      refine ⟨3229954549706007351246379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4306606066274676468328505 3229954549706007351246379)
                      ·
                        rfl

theorem cell23_6290314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_6290314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290314 prefixEnd_6290314 := by exact prefixLift 6290314
  have htrace : WordTrace (prefixWord ++ tailWord_6290314) baseStart_6290314 baseEnd_6290314 := by
    simpa [prefixWord, tailWord_6290314, baseEnd_6290314] using wordTrace_append hprefix tailTrace_6290314
  have hstable : (prefixWord ++ tailWord_6290314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290314).length < 2 ^ (prefixWord ++ tailWord_6290314).sum := by decide
  have hdescent : baseEnd_6290314 < baseStart_6290314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290327 : List Nat := [1, 1, 3, 3, 1, 2, 4, 2, 2, 2, 2]
def baseStart_6290327 : Nat := 118140960795 + 6290327 * 2 ^ 59
def prefixEnd_6290327 : Nat := 4983230072969 + 3 ^ 40 * 6290327 * 2
def baseEnd_6290327 : Nat := 3229961224954515800383819

theorem tailTrace_6290327 : CollatzResearch.WordTrace tailWord_6290327 prefixEnd_6290327 3229961224954515800383819 := by
  unfold tailWord_6290327
  simp only [CollatzResearch.WordTrace]
  refine ⟨229427073882227056167133235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152951382588151370778088823 229427073882227056167133235)
  ·
    refine ⟨344140610823340584250699853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229427073882227056167133235 344140610823340584250699853)
    ·
      refine ⟨129052729058752719094012445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344140610823340584250699853 129052729058752719094012445)
      ·
        refine ⟨48394773397032269660254667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129052729058752719094012445 48394773397032269660254667)
        ·
          refine ⟨72592160095548404490382001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48394773397032269660254667 72592160095548404490382001)
          ·
            refine ⟨54444120071661303367786501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72592160095548404490382001 54444120071661303367786501)
            ·
              refine ⟨10208272513436494381459969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54444120071661303367786501 10208272513436494381459969)
              ·
                refine ⟨7656204385077370786094977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10208272513436494381459969 7656204385077370786094977)
                ·
                  refine ⟨5742153288808028089571233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7656204385077370786094977 5742153288808028089571233)
                  ·
                    refine ⟨4306614966606021067178425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5742153288808028089571233 4306614966606021067178425)
                    ·
                      refine ⟨3229961224954515800383819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4306614966606021067178425 3229961224954515800383819)
                      ·
                        rfl

theorem cell23_6290327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_6290327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290327 prefixEnd_6290327 := by exact prefixLift 6290327
  have htrace : WordTrace (prefixWord ++ tailWord_6290327) baseStart_6290327 baseEnd_6290327 := by
    simpa [prefixWord, tailWord_6290327, baseEnd_6290327] using wordTrace_append hprefix tailTrace_6290327
  have hstable : (prefixWord ++ tailWord_6290327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290327).length < 2 ^ (prefixWord ++ tailWord_6290327).sum := by decide
  have hdescent : baseEnd_6290327 < baseStart_6290327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290403 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 3, 4, 3]
def baseStart_6290403 : Nat := 118140960795 + 6290403 * 2 ^ 59
def prefixEnd_6290403 : Nat := 4983230072969 + 3 ^ 40 * 6290403 * 2
def baseEnd_6290403 : Nat := 3230000249484257503033469

theorem tailTrace_6290403 : CollatzResearch.WordTrace tailWord_6290403 prefixEnd_6290403 3230000249484257503033469 := by
  unfold tailWord_6290403
  simp only [CollatzResearch.WordTrace]
  refine ⟨229429845829951721146899863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152953230553301147431266575 229429845829951721146899863)
  ·
    refine ⟨344144768744927581720349795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229429845829951721146899863 344144768744927581720349795)
    ·
      refine ⟨516217153117391372580524693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344144768744927581720349795 516217153117391372580524693)
      ·
        refine ⟨24197679052377720589712095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 516217153117391372580524693 24197679052377720589712095)
        ·
          refine ⟨36296518578566580884568143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24197679052377720589712095 36296518578566580884568143)
          ·
            refine ⟨54444777867849871326852215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36296518578566580884568143 54444777867849871326852215)
            ·
              refine ⟨81667166801774806990278323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54444777867849871326852215 81667166801774806990278323)
              ·
                refine ⟨122500750202662210485417485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81667166801774806990278323 122500750202662210485417485)
                ·
                  refine ⟨45937781325998328932031557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122500750202662210485417485 45937781325998328932031557)
                  ·
                    refine ⟨8613333998624686674755917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45937781325998328932031557 8613333998624686674755917)
                    ·
                      refine ⟨3230000249484257503033469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8613333998624686674755917 3230000249484257503033469)
                      ·
                        rfl

theorem cell23_6290403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_6290403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290403 prefixEnd_6290403 := by exact prefixLift 6290403
  have htrace : WordTrace (prefixWord ++ tailWord_6290403) baseStart_6290403 baseEnd_6290403 := by
    simpa [prefixWord, tailWord_6290403, baseEnd_6290403] using wordTrace_append hprefix tailTrace_6290403
  have hstable : (prefixWord ++ tailWord_6290403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290403).length < 2 ^ (prefixWord ++ tailWord_6290403).sum := by decide
  have hdescent : baseEnd_6290403 < baseStart_6290403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290410 : List Nat := [3, 1, 3, 1, 2, 2, 2, 2, 3, 4]
def baseStart_6290410 : Nat := 118140960795 + 6290410 * 2 ^ 59
def prefixEnd_6290410 : Nat := 4983230072969 + 3 ^ 40 * 6290410 * 2
def baseEnd_6290410 : Nat := 1076667947949612991881979

theorem tailTrace_6290410 : CollatzResearch.WordTrace tailWord_6290410 prefixEnd_6290410 1076667947949612991881979 := by
  unfold tailWord_6290410
  simp only [CollatzResearch.WordTrace]
  refine ⟨57357525285231590335601171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152953400760617574228269789 57357525285231590335601171)
  ·
    refine ⟨86036287927847385503401757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57357525285231590335601171 86036287927847385503401757)
    ·
      refine ⟨32263607972942769563775659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86036287927847385503401757 32263607972942769563775659)
      ·
        refine ⟨48395411959414154345663489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32263607972942769563775659 48395411959414154345663489)
        ·
          refine ⟨36296558969560615759247617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48395411959414154345663489 36296558969560615759247617)
          ·
            refine ⟨27222419227170461819435713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36296558969560615759247617 27222419227170461819435713)
            ·
              refine ⟨20416814420377846364576785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27222419227170461819435713 20416814420377846364576785)
              ·
                refine ⟨15312610815283384773432589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20416814420377846364576785 15312610815283384773432589)
                ·
                  refine ⟨5742229055731269290037221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15312610815283384773432589 5742229055731269290037221)
                  ·
                    refine ⟨1076667947949612991881979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5742229055731269290037221 1076667947949612991881979)
                    ·
                      rfl

theorem cell23_6290410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_6290410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290410 prefixEnd_6290410 := by exact prefixLift 6290410
  have htrace : WordTrace (prefixWord ++ tailWord_6290410) baseStart_6290410 baseEnd_6290410 := by
    simpa [prefixWord, tailWord_6290410, baseEnd_6290410] using wordTrace_append hprefix tailTrace_6290410
  have hstable : (prefixWord ++ tailWord_6290410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290410).length < 2 ^ (prefixWord ++ tailWord_6290410).sum := by decide
  have hdescent : baseEnd_6290410 < baseStart_6290410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290434 : List Nat := [3, 4, 1, 3, 1, 1, 1, 2, 2, 1, 4]
def baseStart_6290434 : Nat := 118140960795 + 6290434 * 2 ^ 59
def prefixEnd_6290434 : Nat := 4983230072969 + 3 ^ 40 * 6290434 * 2
def baseEnd_6290434 : Nat := 3230016167384546881745827

theorem tailTrace_6290434 : CollatzResearch.WordTrace tailWord_6290434 prefixEnd_6290434 3230016167384546881745827 := by
  unfold tailWord_6290434
  simp only [CollatzResearch.WordTrace]
  refine ⟨57357744123209853360319589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152953984328559608960852237 57357744123209853360319589)
  ·
    refine ⟨10754577023101847505059923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57357744123209853360319589 10754577023101847505059923)
    ·
      refine ⟨16131865534652771257589885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10754577023101847505059923 16131865534652771257589885)
      ·
        refine ⟨6049449575494789221596207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16131865534652771257589885 6049449575494789221596207)
        ·
          refine ⟨9074174363242183832394311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6049449575494789221596207 9074174363242183832394311)
          ·
            refine ⟨13611261544863275748591467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9074174363242183832394311 13611261544863275748591467)
            ·
              refine ⟨20416892317294913622887201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13611261544863275748591467 20416892317294913622887201)
              ·
                refine ⟨15312669237971185217165401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20416892317294913622887201 15312669237971185217165401)
                ·
                  refine ⟨11484501928478388912874051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15312669237971185217165401 11484501928478388912874051)
                  ·
                    refine ⟨17226752892717583369311077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11484501928478388912874051 17226752892717583369311077)
                    ·
                      refine ⟨3230016167384546881745827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17226752892717583369311077 3230016167384546881745827)
                      ·
                        rfl

theorem cell23_6290434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_6290434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290434 prefixEnd_6290434 := by exact prefixLift 6290434
  have htrace : WordTrace (prefixWord ++ tailWord_6290434) baseStart_6290434 baseEnd_6290434 := by
    simpa [prefixWord, tailWord_6290434, baseEnd_6290434] using wordTrace_append hprefix tailTrace_6290434
  have hstable : (prefixWord ++ tailWord_6290434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290434).length < 2 ^ (prefixWord ++ tailWord_6290434).sum := by decide
  have hdescent : baseEnd_6290434 < baseStart_6290434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290444 : List Nat := [2, 2, 1, 2, 3, 3, 3, 2, 1, 4]
def baseStart_6290444 : Nat := 118140960795 + 6290444 * 2 ^ 59
def prefixEnd_6290444 : Nat := 4983230072969 + 3 ^ 40 * 6290444 * 2
def baseEnd_6290444 : Nat := 1076673767397030614206927

theorem tailTrace_6290444 : CollatzResearch.WordTrace tailWord_6290444 prefixEnd_6290444 1076673767397030614206927 := by
  unfold tailWord_6290444
  simp only [CollatzResearch.WordTrace]
  refine ⟨114715670611401592574571193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152954227481868790099428257 114715670611401592574571193)
  ·
    refine ⟨86036752958551194430928395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114715670611401592574571193 86036752958551194430928395)
    ·
      refine ⟨129055129437826791646392593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86036752958551194430928395 129055129437826791646392593)
      ·
        refine ⟨96791347078370093734794445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129055129437826791646392593 96791347078370093734794445)
        ·
          refine ⟨36296755154388785150547917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96791347078370093734794445 36296755154388785150547917)
          ·
            refine ⟨13611283182895794431455469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36296755154388785150547917 13611283182895794431455469)
            ·
              refine ⟨5104231193585922911795801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13611283182895794431455469 5104231193585922911795801)
              ·
                refine ⟨3828173395189442183846851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5104231193585922911795801 3828173395189442183846851)
                ·
                  refine ⟨5742260092784163275770277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3828173395189442183846851 5742260092784163275770277)
                  ·
                    refine ⟨1076673767397030614206927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5742260092784163275770277 1076673767397030614206927)
                    ·
                      rfl

theorem cell23_6290444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 2, 1, 4].length) (baseStart_6290444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290444 prefixEnd_6290444 := by exact prefixLift 6290444
  have htrace : WordTrace (prefixWord ++ tailWord_6290444) baseStart_6290444 baseEnd_6290444 := by
    simpa [prefixWord, tailWord_6290444, baseEnd_6290444] using wordTrace_append hprefix tailTrace_6290444
  have hstable : (prefixWord ++ tailWord_6290444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290444).length < 2 ^ (prefixWord ++ tailWord_6290444).sum := by decide
  have hdescent : baseEnd_6290444 < baseStart_6290444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290490 : List Nat := [3, 1, 1, 1, 3, 1, 2, 5, 1, 1, 4]
def baseStart_6290490 : Nat := 118140960795 + 6290490 * 2 ^ 59
def prefixEnd_6290490 : Nat := 4983230072969 + 3 ^ 40 * 6290490 * 2
def baseEnd_6290490 : Nat := 3230044922301198662645569

theorem tailTrace_6290490 : CollatzResearch.WordTrace tailWord_6290490 prefixEnd_6290490 3230044922301198662645569 := by
  unfold tailWord_6290490
  simp only [CollatzResearch.WordTrace]
  refine ⟨57358254745159133751329231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152955345987091023336877949 57358254745159133751329231)
  ·
    refine ⟨86037382117738700626993847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57358254745159133751329231 86037382117738700626993847)
    ·
      refine ⟨129056073176608050940490771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86037382117738700626993847 129056073176608050940490771)
      ·
        refine ⟨193584109764912076410736157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129056073176608050940490771 193584109764912076410736157)
        ·
          refine ⟨72594041161842028654026059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193584109764912076410736157 72594041161842028654026059)
          ·
            refine ⟨108891061742763042981039089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72594041161842028654026059 108891061742763042981039089)
            ·
              refine ⟨81668296307072282235779317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108891061742763042981039089 81668296307072282235779317)
              ·
                refine ⟨7656402778788026459604311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81668296307072282235779317 7656402778788026459604311)
                ·
                  refine ⟨11484604168182039689406467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7656402778788026459604311 11484604168182039689406467)
                  ·
                    refine ⟨17226906252273059534109701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11484604168182039689406467 17226906252273059534109701)
                    ·
                      refine ⟨3230044922301198662645569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17226906252273059534109701 3230044922301198662645569)
                      ·
                        rfl

theorem cell23_6290490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 1, 1, 4].length) (baseStart_6290490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290490 prefixEnd_6290490 := by exact prefixLift 6290490
  have htrace : WordTrace (prefixWord ++ tailWord_6290490) baseStart_6290490 baseEnd_6290490 := by
    simpa [prefixWord, tailWord_6290490, baseEnd_6290490] using wordTrace_append hprefix tailTrace_6290490
  have hstable : (prefixWord ++ tailWord_6290490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290490).length < 2 ^ (prefixWord ++ tailWord_6290490).sum := by decide
  have hdescent : baseEnd_6290490 < baseStart_6290490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290494 : List Nat := [4, 2, 1, 3, 1, 1, 2, 2, 2, 3, 2]
def baseStart_6290494 : Nat := 118140960795 + 6290494 * 2 ^ 59
def prefixEnd_6290494 : Nat := 4983230072969 + 3 ^ 40 * 6290494 * 2
def baseEnd_6290494 : Nat := 3230046976223816646995551

theorem tailTrace_6290494 : CollatzResearch.WordTrace tailWord_6290494 prefixEnd_6290494 3230046976223816646995551 := by
  unfold tailWord_6290494
  simp only [CollatzResearch.WordTrace]
  refine ⟨28679145609077755461057817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152955443248414695792308357 28679145609077755461057817)
  ·
    refine ⟨21509359206808316595793363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28679145609077755461057817 21509359206808316595793363)
    ·
      refine ⟨32264038810212474893690045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21509359206808316595793363 32264038810212474893690045)
      ·
        refine ⟨12099014553829678085133767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32264038810212474893690045 12099014553829678085133767)
        ·
          refine ⟨18148521830744517127700651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12099014553829678085133767 18148521830744517127700651)
          ·
            refine ⟨27222782746116775691550977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18148521830744517127700651 27222782746116775691550977)
            ·
              refine ⟨20417087059587581768663233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27222782746116775691550977 20417087059587581768663233)
              ·
                refine ⟨15312815294690686326497425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20417087059587581768663233 15312815294690686326497425)
                ·
                  refine ⟨11484611471018014744873069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15312815294690686326497425 11484611471018014744873069)
                  ·
                    refine ⟨4306729301631755529327401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11484611471018014744873069 4306729301631755529327401)
                    ·
                      refine ⟨3230046976223816646995551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4306729301631755529327401 3230046976223816646995551)
                      ·
                        rfl

theorem cell23_6290494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_6290494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290494 prefixEnd_6290494 := by exact prefixLift 6290494
  have htrace : WordTrace (prefixWord ++ tailWord_6290494) baseStart_6290494 baseEnd_6290494 := by
    simpa [prefixWord, tailWord_6290494, baseEnd_6290494] using wordTrace_append hprefix tailTrace_6290494
  have hstable : (prefixWord ++ tailWord_6290494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290494).length < 2 ^ (prefixWord ++ tailWord_6290494).sum := by decide
  have hdescent : baseEnd_6290494 < baseStart_6290494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290510 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3]
def baseStart_6290510 : Nat := 118140960795 + 6290510 * 2 ^ 59
def prefixEnd_6290510 : Nat := 4983230072969 + 3 ^ 40 * 6290510 * 2
def baseEnd_6290510 : Nat := 3230055191914288584395477

theorem tailTrace_6290510 : CollatzResearch.WordTrace tailWord_6290510 prefixEnd_6290510 3230055191914288584395477 := by
  unfold tailWord_6290510
  simp only [CollatzResearch.WordTrace]
  refine ⟨28679218555070509802630623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152955832293709385614029989 28679218555070509802630623)
  ·
    refine ⟨43018827832605764703945935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28679218555070509802630623 43018827832605764703945935)
    ·
      refine ⟨64528241748908647055918903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43018827832605764703945935 64528241748908647055918903)
      ·
        refine ⟨96792362623362970583878355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64528241748908647055918903 96792362623362970583878355)
        ·
          refine ⟨145188543935044455875817533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96792362623362970583878355 145188543935044455875817533)
          ·
            refine ⟨54445703975641670953431575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145188543935044455875817533 54445703975641670953431575)
            ·
              refine ⟨81668555963462506430147363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54445703975641670953431575 81668555963462506430147363)
              ·
                refine ⟨122502833945193759645221045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81668555963462506430147363 122502833945193759645221045)
                ·
                  refine ⟨11484640682361914966739473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122502833945193759645221045 11484640682361914966739473)
                  ·
                    refine ⟨8613480511771436225054605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11484640682361914966739473 8613480511771436225054605)
                    ·
                      refine ⟨3230055191914288584395477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8613480511771436225054605 3230055191914288584395477)
                      ·
                        rfl

theorem cell23_6290510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_6290510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290510 prefixEnd_6290510 := by exact prefixLift 6290510
  have htrace : WordTrace (prefixWord ++ tailWord_6290510) baseStart_6290510 baseEnd_6290510 := by
    simpa [prefixWord, tailWord_6290510, baseEnd_6290510] using wordTrace_append hprefix tailTrace_6290510
  have hstable : (prefixWord ++ tailWord_6290510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290510).length < 2 ^ (prefixWord ++ tailWord_6290510).sum := by decide
  have hdescent : baseEnd_6290510 < baseStart_6290510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290513 : List Nat := [1, 2, 2, 1, 3, 1, 5, 8]
def baseStart_6290513 : Nat := 118140960795 + 6290513 * 2 ^ 59
def prefixEnd_6290513 : Nat := 4983230072969 + 3 ^ 40 * 6290513 * 2
def baseEnd_6290513 : Nat := 119631730828009336024369

theorem tailTrace_6290513 : CollatzResearch.WordTrace tailWord_6290513 prefixEnd_6290513 119631730828009336024369 := by
  unfold tailWord_6290513
  simp only [CollatzResearch.WordTrace]
  refine ⟨229433857859553209933404193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152955905239702139955602795 229433857859553209933404193)
  ·
    refine ⟨172075393394664907450053145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229433857859553209933404193 172075393394664907450053145)
    ·
      refine ⟨129056545045998680587539859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172075393394664907450053145 129056545045998680587539859)
      ·
        refine ⟨193584817568998020881309789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129056545045998680587539859 193584817568998020881309789)
        ·
          refine ⟨72594306588374257830491171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193584817568998020881309789 72594306588374257830491171)
          ·
            refine ⟨108891459882561386745736757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72594306588374257830491171 108891459882561386745736757)
            ·
              refine ⟨10208574363990130007412821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108891459882561386745736757 10208574363990130007412821)
              ·
                refine ⟨119631730828009336024369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10208574363990130007412821 119631730828009336024369)
                ·
                  rfl

theorem cell23_6290513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 8].length) (baseStart_6290513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290513 prefixEnd_6290513 := by exact prefixLift 6290513
  have htrace : WordTrace (prefixWord ++ tailWord_6290513) baseStart_6290513 baseEnd_6290513 := by
    simpa [prefixWord, tailWord_6290513, baseEnd_6290513] using wordTrace_append hprefix tailTrace_6290513
  have hstable : (prefixWord ++ tailWord_6290513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290513).length < 2 ^ (prefixWord ++ tailWord_6290513).sum := by decide
  have hdescent : baseEnd_6290513 < baseStart_6290513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290520 : List Nat := [2, 1, 2, 2, 1, 3, 4, 1, 1, 2, 4]
def baseStart_6290520 : Nat := 118140960795 + 6290520 * 2 ^ 59
def prefixEnd_6290520 : Nat := 4983230072969 + 3 ^ 40 * 6290520 * 2
def baseEnd_6290520 : Nat := 3230060326720833545270431

theorem tailTrace_6290520 : CollatzResearch.WordTrace tailWord_6290520 prefixEnd_6290520 3230060326720833545270431 := by
  unfold tailWord_6290520
  simp only [CollatzResearch.WordTrace]
  refine ⟨114717056585263925064454507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152956075447018566752606009 114717056585263925064454507)
  ·
    refine ⟨172075584877895887596681761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114717056585263925064454507 172075584877895887596681761)
    ·
      refine ⟨129056688658421915697511321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172075584877895887596681761 129056688658421915697511321)
      ·
        refine ⟨96792516493816436773133491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129056688658421915697511321 96792516493816436773133491)
        ·
          refine ⟨145188774740724655159700237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96792516493816436773133491 145188774740724655159700237)
          ·
            refine ⟨54445790527771745684887589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145188774740724655159700237 54445790527771745684887589)
            ·
              refine ⟨10208585723957202315916423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54445790527771745684887589 10208585723957202315916423)
              ·
                refine ⟨15312878585935803473874635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10208585723957202315916423 15312878585935803473874635)
                ·
                  refine ⟨22969317878903705210811953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15312878585935803473874635 22969317878903705210811953)
                  ·
                    refine ⟨17226988409177778908108965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22969317878903705210811953 17226988409177778908108965)
                    ·
                      refine ⟨3230060326720833545270431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17226988409177778908108965 3230060326720833545270431)
                      ·
                        rfl

theorem cell23_6290520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_6290520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290520 prefixEnd_6290520 := by exact prefixLift 6290520
  have htrace : WordTrace (prefixWord ++ tailWord_6290520) baseStart_6290520 baseEnd_6290520 := by
    simpa [prefixWord, tailWord_6290520, baseEnd_6290520] using wordTrace_append hprefix tailTrace_6290520
  have hstable : (prefixWord ++ tailWord_6290520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290520).length < 2 ^ (prefixWord ++ tailWord_6290520).sum := by decide
  have hdescent : baseEnd_6290520 < baseStart_6290520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290524 : List Nat := [2, 2, 4, 1, 1, 1, 3, 2, 3, 2, 2]
def baseStart_6290524 : Nat := 118140960795 + 6290524 * 2 ^ 59
def prefixEnd_6290524 : Nat := 4983230072969 + 3 ^ 40 * 6290524 * 2
def baseEnd_6290524 : Nat := 3230062380643451529620413

theorem tailTrace_6290524 : CollatzResearch.WordTrace tailWord_6290524 prefixEnd_6290524 3230062380643451529620413 := by
  unfold tailWord_6290524
  simp only [CollatzResearch.WordTrace]
  refine ⟨114717129531256679406027313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152956172708342239208036417 114717129531256679406027313)
  ·
    refine ⟨86037847148442509554520485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114717129531256679406027313 86037847148442509554520485)
    ·
      refine ⟨16132096340332970541472591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86037847148442509554520485 16132096340332970541472591)
      ·
        refine ⟨24198144510499455812208887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16132096340332970541472591 24198144510499455812208887)
        ·
          refine ⟨36297216765749183718313331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24198144510499455812208887 36297216765749183718313331)
          ·
            refine ⟨54445825148623775577469997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36297216765749183718313331 54445825148623775577469997)
            ·
              refine ⟨20417184430733915841551249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54445825148623775577469997 20417184430733915841551249)
              ·
                refine ⟨15312888323050436881163437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20417184430733915841551249 15312888323050436881163437)
                ·
                  refine ⟨5742333121143913830436289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15312888323050436881163437 5742333121143913830436289)
                  ·
                    refine ⟨4306749840857935372827217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5742333121143913830436289 4306749840857935372827217)
                    ·
                      refine ⟨3230062380643451529620413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4306749840857935372827217 3230062380643451529620413)
                      ·
                        rfl

theorem cell23_6290524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_6290524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290524 prefixEnd_6290524 := by exact prefixLift 6290524
  have htrace : WordTrace (prefixWord ++ tailWord_6290524) baseStart_6290524 baseEnd_6290524 := by
    simpa [prefixWord, tailWord_6290524, baseEnd_6290524] using wordTrace_append hprefix tailTrace_6290524
  have hstable : (prefixWord ++ tailWord_6290524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290524).length < 2 ^ (prefixWord ++ tailWord_6290524).sum := by decide
  have hdescent : baseEnd_6290524 < baseStart_6290524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290540 : List Nat := [2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 3]
def baseStart_6290540 : Nat := 118140960795 + 6290540 * 2 ^ 59
def prefixEnd_6290540 : Nat := 4983230072969 + 3 ^ 40 * 6290540 * 2
def baseEnd_6290540 : Nat := 3230070596333923467020339

theorem tailTrace_6290540 : CollatzResearch.WordTrace tailWord_6290540 prefixEnd_6290540 3230070596333923467020339 := by
  unfold tailWord_6290540
  simp only [CollatzResearch.WordTrace]
  refine ⟨114717421315227696772318537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152956561753636929029758049 114717421315227696772318537)
  ·
    refine ⟨86038065986420772579238903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114717421315227696772318537 86038065986420772579238903)
    ·
      refine ⟨129057098979631158868858355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86038065986420772579238903 129057098979631158868858355)
      ·
        refine ⟨193585648469446738303287533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129057098979631158868858355 193585648469446738303287533)
        ·
          refine ⟨72594618176042526863732825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193585648469446738303287533 72594618176042526863732825)
          ·
            refine ⟨54445963632031895147799619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72594618176042526863732825 54445963632031895147799619)
            ·
              refine ⟨81668945448047842721699429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54445963632031895147799619 81668945448047842721699429)
              ·
                refine ⟨15312927271508970510318643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81668945448047842721699429 15312927271508970510318643)
                ·
                  refine ⟨22969390907263455765477965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15312927271508970510318643 22969390907263455765477965)
                  ·
                    refine ⟨8613521590223795912054237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22969390907263455765477965 8613521590223795912054237)
                    ·
                      refine ⟨3230070596333923467020339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8613521590223795912054237 3230070596333923467020339)
                      ·
                        rfl

theorem cell23_6290540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 3].length) (baseStart_6290540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290540 prefixEnd_6290540 := by exact prefixLift 6290540
  have htrace : WordTrace (prefixWord ++ tailWord_6290540) baseStart_6290540 baseEnd_6290540 := by
    simpa [prefixWord, tailWord_6290540, baseEnd_6290540] using wordTrace_append hprefix tailTrace_6290540
  have hstable : (prefixWord ++ tailWord_6290540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290540).length < 2 ^ (prefixWord ++ tailWord_6290540).sum := by decide
  have hdescent : baseEnd_6290540 < baseStart_6290540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290541 : List Nat := [1, 5, 1, 1, 2, 2, 1, 5, 1, 2, 2]
def baseStart_6290541 : Nat := 118140960795 + 6290541 * 2 ^ 59
def prefixEnd_6290541 : Nat := 4983230072969 + 3 ^ 40 * 6290541 * 2
def baseEnd_6290541 : Nat := 3230071109814577963107835

theorem tailTrace_6290541 : CollatzResearch.WordTrace tailWord_6290541 prefixEnd_6290541 3230071109814577963107835 := by
  unfold tailWord_6290541
  simp only [CollatzResearch.WordTrace]
  refine ⟨229434879103451770715423477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152956586068967847143615651 229434879103451770715423477)
  ·
    refine ⟨21509519915948603504570951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 229434879103451770715423477 21509519915948603504570951)
    ·
      refine ⟨32264279873922905256856427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21509519915948603504570951 32264279873922905256856427)
      ·
        refine ⟨48396419810884357885284641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32264279873922905256856427 48396419810884357885284641)
        ·
          refine ⟨36297314858163268413963481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48396419810884357885284641 36297314858163268413963481)
          ·
            refine ⟨27222986143622451310472611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36297314858163268413963481 27222986143622451310472611)
            ·
              refine ⟨40834479215433676965708917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27222986143622451310472611 40834479215433676965708917)
              ·
                refine ⟨3828232426446907215535211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40834479215433676965708917 3828232426446907215535211)
                ·
                  refine ⟨5742348639670360823302817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3828232426446907215535211 5742348639670360823302817)
                  ·
                    refine ⟨4306761479752770617477113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5742348639670360823302817 4306761479752770617477113)
                    ·
                      refine ⟨3230071109814577963107835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4306761479752770617477113 3230071109814577963107835)
                      ·
                        rfl

theorem cell23_6290541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_6290541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290541 prefixEnd_6290541 := by exact prefixLift 6290541
  have htrace : WordTrace (prefixWord ++ tailWord_6290541) baseStart_6290541 baseEnd_6290541 := by
    simpa [prefixWord, tailWord_6290541, baseEnd_6290541] using wordTrace_append hprefix tailTrace_6290541
  have hstable : (prefixWord ++ tailWord_6290541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290541).length < 2 ^ (prefixWord ++ tailWord_6290541).sum := by decide
  have hdescent : baseEnd_6290541 < baseStart_6290541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290557 : List Nat := [1, 4, 1, 1, 3, 1, 3, 1, 4, 1, 3]
def baseStart_6290557 : Nat := 118140960795 + 6290557 * 2 ^ 59
def prefixEnd_6290557 : Nat := 4983230072969 + 3 ^ 40 * 6290557 * 2
def baseEnd_6290557 : Nat := 3230079325505049900507761

theorem tailTrace_6290557 : CollatzResearch.WordTrace tailWord_6290557 prefixEnd_6290557 3230079325505049900507761 := by
  unfold tailWord_6290557
  simp only [CollatzResearch.WordTrace]
  refine ⟨229435462671393805448005925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152956975114262536965337283 229435462671393805448005925)
  ·
    refine ⟨43019149250886338521501111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229435462671393805448005925 43019149250886338521501111)
    ·
      refine ⟨64528723876329507782251667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43019149250886338521501111 64528723876329507782251667)
      ·
        refine ⟨96793085814494261673377501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64528723876329507782251667 96793085814494261673377501)
        ·
          refine ⟨36297407180435348127516563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96793085814494261673377501 36297407180435348127516563)
          ·
            refine ⟨54446110770653022191274845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36297407180435348127516563 54446110770653022191274845)
            ·
              refine ⟨20417291538994883321728067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54446110770653022191274845 20417291538994883321728067)
              ·
                refine ⟨30625937308492324982592101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20417291538994883321728067 30625937308492324982592101)
                ·
                  refine ⟨5742363245342310934236019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30625937308492324982592101 5742363245342310934236019)
                  ·
                    refine ⟨8613544868013466401354029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5742363245342310934236019 8613544868013466401354029)
                    ·
                      refine ⟨3230079325505049900507761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8613544868013466401354029 3230079325505049900507761)
                      ·
                        rfl

theorem cell23_6290557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_6290557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290557 prefixEnd_6290557 := by exact prefixLift 6290557
  have htrace : WordTrace (prefixWord ++ tailWord_6290557) baseStart_6290557 baseEnd_6290557 := by
    simpa [prefixWord, tailWord_6290557, baseEnd_6290557] using wordTrace_append hprefix tailTrace_6290557
  have hstable : (prefixWord ++ tailWord_6290557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290557).length < 2 ^ (prefixWord ++ tailWord_6290557).sum := by decide
  have hdescent : baseEnd_6290557 < baseStart_6290557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290574 : List Nat := [4, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3]
def baseStart_6290574 : Nat := 118140960795 + 6290574 * 2 ^ 59
def prefixEnd_6290574 : Nat := 4983230072969 + 3 ^ 40 * 6290574 * 2
def baseEnd_6290574 : Nat := 3230088054676176333995183

theorem tailTrace_6290574 : CollatzResearch.WordTrace tailWord_6290574 prefixEnd_6290574 3230088054676176333995183 := by
  unfold tailWord_6290574
  simp only [CollatzResearch.WordTrace]
  refine ⟨28679510339041527168921847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152957388474888144900916517 28679510339041527168921847)
  ·
    refine ⟨43019265508562290753382771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28679510339041527168921847 43019265508562290753382771)
    ·
      refine ⟨64528898262843436130074157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43019265508562290753382771 64528898262843436130074157)
      ·
        refine ⟨24198336848566288548777809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64528898262843436130074157 24198336848566288548777809)
        ·
          refine ⟨18148752636424716411583357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24198336848566288548777809 18148752636424716411583357)
          ·
            refine ⟨6805782238659268654343759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18148752636424716411583357 6805782238659268654343759)
            ·
              refine ⟨10208673357988902981515639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6805782238659268654343759 10208673357988902981515639)
              ·
                refine ⟨15313010036983354472273459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10208673357988902981515639 15313010036983354472273459)
                ·
                  refine ⟨22969515055475031708410189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15313010036983354472273459 22969515055475031708410189)
                  ·
                    refine ⟨8613568145803136890653821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22969515055475031708410189 8613568145803136890653821)
                    ·
                      refine ⟨3230088054676176333995183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8613568145803136890653821 3230088054676176333995183)
                      ·
                        rfl

theorem cell23_6290574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_6290574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290574 prefixEnd_6290574 := by exact prefixLift 6290574
  have htrace : WordTrace (prefixWord ++ tailWord_6290574) baseStart_6290574 baseEnd_6290574 := by
    simpa [prefixWord, tailWord_6290574, baseEnd_6290574] using wordTrace_append hprefix tailTrace_6290574
  have hstable : (prefixWord ++ tailWord_6290574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290574).length < 2 ^ (prefixWord ++ tailWord_6290574).sum := by decide
  have hdescent : baseEnd_6290574 < baseStart_6290574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290584 : List Nat := [2, 1, 2, 4, 2, 1, 1, 4, 1, 3, 2]
def baseStart_6290584 : Nat := 118140960795 + 6290584 * 2 ^ 59
def prefixEnd_6290584 : Nat := 4983230072969 + 3 ^ 40 * 6290584 * 2
def baseEnd_6290584 : Nat := 3230093189482721294870137

theorem tailTrace_6290584 : CollatzResearch.WordTrace tailWord_6290584 prefixEnd_6290584 3230093189482721294870137 := by
  unfold tailWord_6290584
  simp only [CollatzResearch.WordTrace]
  refine ⟨114718223721147994529619403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152957631628197326039492537 114718223721147994529619403)
  ·
    refine ⟨172077335581721991794429105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114718223721147994529619403 172077335581721991794429105)
    ·
      refine ⟨129058001686291493845821829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172077335581721991794429105 129058001686291493845821829)
      ·
        refine ⟨24198375316179655096091593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129058001686291493845821829 24198375316179655096091593)
        ·
          refine ⟨18148781487134741322068695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24198375316179655096091593 18148781487134741322068695)
          ·
            refine ⟨27223172230702111983103043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18148781487134741322068695 27223172230702111983103043)
            ·
              refine ⟨40834758346053167974654565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27223172230702111983103043 40834758346053167974654565)
              ·
                refine ⟨7656517189884968995247731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40834758346053167974654565 7656517189884968995247731)
                ·
                  refine ⟨11484775784827453492871597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7656517189884968995247731 11484775784827453492871597)
                  ·
                    refine ⟨4306790919310295059826849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11484775784827453492871597 4306790919310295059826849)
                    ·
                      refine ⟨3230093189482721294870137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4306790919310295059826849 3230093189482721294870137)
                      ·
                        rfl

theorem cell23_6290584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_6290584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290584 prefixEnd_6290584 := by exact prefixLift 6290584
  have htrace : WordTrace (prefixWord ++ tailWord_6290584) baseStart_6290584 baseEnd_6290584 := by
    simpa [prefixWord, tailWord_6290584, baseEnd_6290584] using wordTrace_append hprefix tailTrace_6290584
  have hstable : (prefixWord ++ tailWord_6290584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290584).length < 2 ^ (prefixWord ++ tailWord_6290584).sum := by decide
  have hdescent : baseEnd_6290584 < baseStart_6290584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290660 : List Nat := [2, 3, 1, 1, 1, 2, 3, 2, 1, 2, 5]
def baseStart_6290660 : Nat := 118140960795 + 6290660 * 2 ^ 59
def prefixEnd_6290660 : Nat := 4983230072969 + 3 ^ 40 * 6290660 * 2
def baseEnd_6290660 : Nat := 3230132214012462997519787

theorem tailTrace_6290660 : CollatzResearch.WordTrace tailWord_6290660 prefixEnd_6290660 3230132214012462997519787 := by
  unfold tailWord_6290660
  simp only [CollatzResearch.WordTrace]
  refine ⟨114719609695010327019502717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152959479593347102692670289 114719609695010327019502717)
  ·
    refine ⟨43019853635628872632313519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114719609695010327019502717 43019853635628872632313519)
    ·
      refine ⟨64529780453443308948470279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43019853635628872632313519 64529780453443308948470279)
      ·
        refine ⟨96794670680164963422705419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64529780453443308948470279 96794670680164963422705419)
        ·
          refine ⟨145192006020247445134058129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96794670680164963422705419 145192006020247445134058129)
          ·
            refine ⟨108894004515185583850543597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145192006020247445134058129 108894004515185583850543597)
            ·
              refine ⟨40835251693194593943953849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108894004515185583850543597 40835251693194593943953849)
              ·
                refine ⟨30626438769895945457965387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40835251693194593943953849 30626438769895945457965387)
                ·
                  refine ⟨45939658154843918186948081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30626438769895945457965387 45939658154843918186948081)
                  ·
                    refine ⟨34454743616132938640211061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45939658154843918186948081 34454743616132938640211061)
                    ·
                      refine ⟨3230132214012462997519787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34454743616132938640211061 3230132214012462997519787)
                      ·
                        rfl

theorem cell23_6290660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_6290660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290660 prefixEnd_6290660 := by exact prefixLift 6290660
  have htrace : WordTrace (prefixWord ++ tailWord_6290660) baseStart_6290660 baseEnd_6290660 := by
    simpa [prefixWord, tailWord_6290660, baseEnd_6290660] using wordTrace_append hprefix tailTrace_6290660
  have hstable : (prefixWord ++ tailWord_6290660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290660).length < 2 ^ (prefixWord ++ tailWord_6290660).sum := by decide
  have hdescent : baseEnd_6290660 < baseStart_6290660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290671 : List Nat := [1, 1, 2, 1, 7, 2, 2, 2, 5]
def baseStart_6290671 : Nat := 118140960795 + 6290671 * 2 ^ 59
def prefixEnd_6290671 : Nat := 4983230072969 + 3 ^ 40 * 6290671 * 2
def baseEnd_6290671 : Nat := 358904206922184717164693

theorem tailTrace_6290671 : CollatzResearch.WordTrace tailWord_6290671 prefixEnd_6290671 358904206922184717164693 := by
  unfold tailWord_6290671
  simp only [CollatzResearch.WordTrace]
  refine ⟨229439620592980802917655867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152959747061987201945103911 229439620592980802917655867)
  ·
    refine ⟨344159430889471204376483801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229439620592980802917655867 344159430889471204376483801)
    ·
      refine ⟨258119573167103403282362851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344159430889471204376483801 258119573167103403282362851)
      ·
        refine ⟨387179359750655104923544277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258119573167103403282362851 387179359750655104923544277)
        ·
          refine ⟨9074516244155979021645569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 387179359750655104923544277 9074516244155979021645569)
          ·
            refine ⟨6805887183116984266234177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9074516244155979021645569 6805887183116984266234177)
            ·
              refine ⟨5104415387337738199675633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6805887183116984266234177 5104415387337738199675633)
              ·
                refine ⟨3828311540503303649756725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5104415387337738199675633 3828311540503303649756725)
                ·
                  refine ⟨358904206922184717164693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3828311540503303649756725 358904206922184717164693)
                  ·
                    rfl

theorem cell23_6290671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 2, 5].length) (baseStart_6290671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290671 prefixEnd_6290671 := by exact prefixLift 6290671
  have htrace : WordTrace (prefixWord ++ tailWord_6290671) baseStart_6290671 baseEnd_6290671 := by
    simpa [prefixWord, tailWord_6290671, baseEnd_6290671] using wordTrace_append hprefix tailTrace_6290671
  have hstable : (prefixWord ++ tailWord_6290671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290671).length < 2 ^ (prefixWord ++ tailWord_6290671).sum := by decide
  have hdescent : baseEnd_6290671 < baseStart_6290671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290687 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 1, 6, 2]
def baseStart_6290687 : Nat := 118140960795 + 6290687 * 2 ^ 59
def prefixEnd_6290687 : Nat := 4983230072969 + 3 ^ 40 * 6290687 * 2
def baseEnd_6290687 : Nat := 3230146077990134391882163

theorem tailTrace_6290687 : CollatzResearch.WordTrace tailWord_6290687 prefixEnd_6290687 3230146077990134391882163 := by
  unfold tailWord_6290687
  simp only [CollatzResearch.WordTrace]
  refine ⟨229440204160922837650238315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152960136107281891766825543 229440204160922837650238315)
  ·
    refine ⟨344160306241384256475357473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229440204160922837650238315 344160306241384256475357473)
    ·
      refine ⟨258120229681038192356518105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344160306241384256475357473 258120229681038192356518105)
      ·
        refine ⟨193590172260778644267388579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258120229681038192356518105 193590172260778644267388579)
        ·
          refine ⟨290385258391167966401082869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193590172260778644267388579 290385258391167966401082869)
          ·
            refine ⟨27223617974171996850101519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 290385258391167966401082869 27223617974171996850101519)
            ·
              refine ⟨40835426961257995275152279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27223617974171996850101519 40835426961257995275152279)
              ·
                refine ⟨61253140441886992912728419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40835426961257995275152279 61253140441886992912728419)
                ·
                  refine ⟨91879710662830489369092629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61253140441886992912728419 91879710662830489369092629)
                  ·
                    refine ⟨4306861437320179189176217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 91879710662830489369092629 4306861437320179189176217)
                    ·
                      refine ⟨3230146077990134391882163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4306861437320179189176217 3230146077990134391882163)
                      ·
                        rfl

theorem cell23_6290687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 6, 2].length) (baseStart_6290687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290687 prefixEnd_6290687 := by exact prefixLift 6290687
  have htrace : WordTrace (prefixWord ++ tailWord_6290687) baseStart_6290687 baseEnd_6290687 := by
    simpa [prefixWord, tailWord_6290687, baseEnd_6290687] using wordTrace_append hprefix tailTrace_6290687
  have hstable : (prefixWord ++ tailWord_6290687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290687).length < 2 ^ (prefixWord ++ tailWord_6290687).sum := by decide
  have hdescent : baseEnd_6290687 < baseStart_6290687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290697 : List Nat := [1, 2, 1, 1, 3, 3, 3, 2, 3, 4]
def baseStart_6290697 : Nat := 118140960795 + 6290697 * 2 ^ 59
def prefixEnd_6290697 : Nat := 4983230072969 + 3 ^ 40 * 6290697 * 2
def baseEnd_6290697 : Nat := 1076717070932226450919039

theorem tailTrace_6290697 : CollatzResearch.WordTrace tailWord_6290697 prefixEnd_6290697 1076717070932226450919039 := by
  unfold tailWord_6290697
  simp only [CollatzResearch.WordTrace]
  refine ⟨229440568890886609358102345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152960379260591072905401563 229440568890886609358102345)
  ·
    refine ⟨172080426668164957018576759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229440568890886609358102345 172080426668164957018576759)
    ·
      refine ⟨258120640002247435527865139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172080426668164957018576759 258120640002247435527865139)
      ·
        refine ⟨387180960003371153291797709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258120640002247435527865139 387180960003371153291797709)
        ·
          refine ⟨145192860001264182484424141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 387180960003371153291797709 145192860001264182484424141)
          ·
            refine ⟨54447322500474068431659053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145192860001264182484424141 54447322500474068431659053)
            ·
              refine ⟨20417745937677775661872145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54447322500474068431659053 20417745937677775661872145)
              ·
                refine ⟨15313309453258331746404109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20417745937677775661872145 15313309453258331746404109)
                ·
                  refine ⟨5742491044971874404901541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15313309453258331746404109 5742491044971874404901541)
                  ·
                    refine ⟨1076717070932226450919039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5742491044971874404901541 1076717070932226450919039)
                    ·
                      rfl

theorem cell23_6290697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 3, 4].length) (baseStart_6290697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290697 prefixEnd_6290697 := by exact prefixLift 6290697
  have htrace : WordTrace (prefixWord ++ tailWord_6290697) baseStart_6290697 baseEnd_6290697 := by
    simpa [prefixWord, tailWord_6290697, baseEnd_6290697] using wordTrace_append hprefix tailTrace_6290697
  have hstable : (prefixWord ++ tailWord_6290697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290697).length < 2 ^ (prefixWord ++ tailWord_6290697).sum := by decide
  have hdescent : baseEnd_6290697 < baseStart_6290697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290717 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 2, 1, 6]
def baseStart_6290717 : Nat := 118140960795 + 6290717 * 2 ^ 59
def prefixEnd_6290717 : Nat := 4983230072969 + 3 ^ 40 * 6290717 * 2
def baseEnd_6290717 : Nat := 3230161482409769274507025

theorem tailTrace_6290717 : CollatzResearch.WordTrace tailWord_6290717 prefixEnd_6290717 3230161482409769274507025 := by
  unfold tailWord_6290717
  simp only [CollatzResearch.WordTrace]
  refine ⟨229441298350814152773830405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152960865567209435182553603 229441298350814152773830405)
  ·
    refine ⟨43020243440777653645093201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229441298350814152773830405 43020243440777653645093201)
    ·
      refine ⟨32265182580583240233819901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43020243440777653645093201 32265182580583240233819901)
      ·
        refine ⟨12099443467718715087682463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32265182580583240233819901 12099443467718715087682463)
        ·
          refine ⟨18149165201578072631523695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12099443467718715087682463 18149165201578072631523695)
          ·
            refine ⟨27223747802367108947285543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18149165201578072631523695 27223747802367108947285543)
            ·
              refine ⟨40835621703550663420928315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27223747802367108947285543 40835621703550663420928315)
              ·
                refine ⟨61253432555325995131392473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40835621703550663420928315 61253432555325995131392473)
                ·
                  refine ⟨45940074416494496348544355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61253432555325995131392473 45940074416494496348544355)
                  ·
                    refine ⟨68910111624741744522816533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45940074416494496348544355 68910111624741744522816533)
                    ·
                      refine ⟨3230161482409769274507025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68910111624741744522816533 3230161482409769274507025)
                      ·
                        rfl

theorem cell23_6290717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_6290717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290717 prefixEnd_6290717 := by exact prefixLift 6290717
  have htrace : WordTrace (prefixWord ++ tailWord_6290717) baseStart_6290717 baseEnd_6290717 := by
    simpa [prefixWord, tailWord_6290717, baseEnd_6290717] using wordTrace_append hprefix tailTrace_6290717
  have hstable : (prefixWord ++ tailWord_6290717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290717).length < 2 ^ (prefixWord ++ tailWord_6290717).sum := by decide
  have hdescent : baseEnd_6290717 < baseStart_6290717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290764 : List Nat := [2, 2, 1, 3, 2, 2, 2, 1, 1, 5, 2]
def baseStart_6290764 : Nat := 118140960795 + 6290764 * 2 ^ 59
def prefixEnd_6290764 : Nat := 4983230072969 + 3 ^ 40 * 6290764 * 2
def baseEnd_6290764 : Nat := 3230185616000530590619309

theorem tailTrace_6290764 : CollatzResearch.WordTrace tailWord_6290764 prefixEnd_6290764 3230185616000530590619309 := by
  unfold tailWord_6290764
  simp only [CollatzResearch.WordTrace]
  refine ⟨114721506290821939900395673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152962008387762586533860897 114721506290821939900395673)
  ·
    refine ⟨86041129718116454925296755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114721506290821939900395673 86041129718116454925296755)
    ·
      refine ⟨129061694577174682387945133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86041129718116454925296755 129061694577174682387945133)
      ·
        refine ⟨48398135466440505895479425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129061694577174682387945133 48398135466440505895479425)
        ·
          refine ⟨36298601599830379421609569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48398135466440505895479425 36298601599830379421609569)
          ·
            refine ⟨27223951199872784566207177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36298601599830379421609569 27223951199872784566207177)
            ·
              refine ⟨20417963399904588424655383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27223951199872784566207177 20417963399904588424655383)
              ·
                refine ⟨30626945099856882636983075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20417963399904588424655383 30626945099856882636983075)
                ·
                  refine ⟨45940417649785323955474613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30626945099856882636983075 45940417649785323955474613)
                  ·
                    refine ⟨4306914154667374120825745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45940417649785323955474613 4306914154667374120825745)
                    ·
                      refine ⟨3230185616000530590619309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4306914154667374120825745 3230185616000530590619309)
                      ·
                        rfl

theorem cell23_6290764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_6290764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290764 prefixEnd_6290764 := by exact prefixLift 6290764
  have htrace : WordTrace (prefixWord ++ tailWord_6290764) baseStart_6290764 baseEnd_6290764 := by
    simpa [prefixWord, tailWord_6290764, baseEnd_6290764] using wordTrace_append hprefix tailTrace_6290764
  have hstable : (prefixWord ++ tailWord_6290764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290764).length < 2 ^ (prefixWord ++ tailWord_6290764).sum := by decide
  have hdescent : baseEnd_6290764 < baseStart_6290764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290807 : List Nat := [1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 4]
def baseStart_6290807 : Nat := 118140960795 + 6290807 * 2 ^ 59
def prefixEnd_6290807 : Nat := 4983230072969 + 3 ^ 40 * 6290807 * 2
def baseEnd_6290807 : Nat := 3230207695668673922381611

theorem tailTrace_6290807 : CollatzResearch.WordTrace tailWord_6290807 prefixEnd_6290807 3230207695668673922381611 := by
  unfold tailWord_6290807
  simp only [CollatzResearch.WordTrace]
  refine ⟨229444580920488098144606675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152963053946992065429737783 229444580920488098144606675)
  ·
    refine ⟨344166871380732147216910013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229444580920488098144606675 344166871380732147216910013)
    ·
      refine ⟨129062576767774555206341255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344166871380732147216910013 129062576767774555206341255)
      ·
        refine ⟨193593865151661832809511883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129062576767774555206341255 193593865151661832809511883)
        ·
          refine ⟨290390797727492749214267825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193593865151661832809511883 290390797727492749214267825)
          ·
            refine ⟨217793098295619561910700869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290390797727492749214267825 217793098295619561910700869)
            ·
              refine ⟨40836205930428667858256413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 217793098295619561910700869 40836205930428667858256413)
              ·
                refine ⟨15313577223910750446846155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40836205930428667858256413 15313577223910750446846155)
                ·
                  refine ⟨22970365835866125670269233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15313577223910750446846155 22970365835866125670269233)
                  ·
                    refine ⟨17227774376899594252701925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22970365835866125670269233 17227774376899594252701925)
                    ·
                      refine ⟨3230207695668673922381611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17227774376899594252701925 3230207695668673922381611)
                      ·
                        rfl

theorem cell23_6290807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_6290807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290807 prefixEnd_6290807 := by exact prefixLift 6290807
  have htrace : WordTrace (prefixWord ++ tailWord_6290807) baseStart_6290807 baseEnd_6290807 := by
    simpa [prefixWord, tailWord_6290807, baseEnd_6290807] using wordTrace_append hprefix tailTrace_6290807
  have hstable : (prefixWord ++ tailWord_6290807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290807).length < 2 ^ (prefixWord ++ tailWord_6290807).sum := by decide
  have hdescent : baseEnd_6290807 < baseStart_6290807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290824 : List Nat := [2, 1, 3, 3, 1, 3, 1, 2, 1, 2, 4]
def baseStart_6290824 : Nat := 118140960795 + 6290824 * 2 ^ 59
def prefixEnd_6290824 : Nat := 4983230072969 + 3 ^ 40 * 6290824 * 2
def baseEnd_6290824 : Nat := 3230216424839800355869033

theorem tailTrace_6290824 : CollatzResearch.WordTrace tailWord_6290824 prefixEnd_6290824 3230216424839800355869033 := by
  unfold tailWord_6290824
  simp only [CollatzResearch.WordTrace]
  refine ⟨114722600480713255023987763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152963467307617673365317017 114722600480713255023987763)
  ·
    refine ⟨172083900721069882535981645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114722600480713255023987763 172083900721069882535981645)
    ·
      refine ⟨64531462770401205950993117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172083900721069882535981645 64531462770401205950993117)
      ·
        refine ⟨24199298538900452231622419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64531462770401205950993117 24199298538900452231622419)
        ·
          refine ⟨36298947808350678347433629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24199298538900452231622419 36298947808350678347433629)
          ·
            refine ⟨13612105428131504380287611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36298947808350678347433629 13612105428131504380287611)
            ·
              refine ⟨20418158142197256570431417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13612105428131504380287611 20418158142197256570431417)
              ·
                refine ⟨15313618606647942427823563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20418158142197256570431417 15313618606647942427823563)
                ·
                  refine ⟨22970427909971913641735345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15313618606647942427823563 22970427909971913641735345)
                  ·
                    refine ⟨17227820932478935231301509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22970427909971913641735345 17227820932478935231301509)
                    ·
                      refine ⟨3230216424839800355869033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17227820932478935231301509 3230216424839800355869033)
                      ·
                        rfl

theorem cell23_6290824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_6290824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290824 prefixEnd_6290824 := by exact prefixLift 6290824
  have htrace : WordTrace (prefixWord ++ tailWord_6290824) baseStart_6290824 baseEnd_6290824 := by
    simpa [prefixWord, tailWord_6290824, baseEnd_6290824] using wordTrace_append hprefix tailTrace_6290824
  have hstable : (prefixWord ++ tailWord_6290824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290824).length < 2 ^ (prefixWord ++ tailWord_6290824).sum := by decide
  have hdescent : baseEnd_6290824 < baseStart_6290824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290828 : List Nat := [2, 2, 1, 2, 1, 3, 2, 5, 1, 2, 2]
def baseStart_6290828 : Nat := 118140960795 + 6290828 * 2 ^ 59
def prefixEnd_6290828 : Nat := 4983230072969 + 3 ^ 40 * 6290828 * 2
def baseEnd_6290828 : Nat := 3230218478762418340219015

theorem tailTrace_6290828 : CollatzResearch.WordTrace tailWord_6290828 prefixEnd_6290828 3230218478762418340219015 := by
  unfold tailWord_6290828
  simp only [CollatzResearch.WordTrace]
  refine ⟨114722673426706009365560569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152963564568941345820747425 114722673426706009365560569)
  ·
    refine ⟨86042005070029507024170427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114722673426706009365560569 86042005070029507024170427)
    ·
      refine ⟨129063007605044260536255641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86042005070029507024170427 129063007605044260536255641)
      ·
        refine ⟨96797255703783195402191731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129063007605044260536255641 96797255703783195402191731)
        ·
          refine ⟨145195883555674793103287597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96797255703783195402191731 145195883555674793103287597)
          ·
            refine ⟨54448456333378047413732849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145195883555674793103287597 54448456333378047413732849)
            ·
              refine ⟨40836342250033535560299637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54448456333378047413732849 40836342250033535560299637)
              ·
                refine ⟨3828407085940643958778091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40836342250033535560299637 3828407085940643958778091)
                ·
                  refine ⟨5742610628910965938167137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3828407085940643958778091 5742610628910965938167137)
                  ·
                    refine ⟨4306957971683224453625353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5742610628910965938167137 4306957971683224453625353)
                    ·
                      refine ⟨3230218478762418340219015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4306957971683224453625353 3230218478762418340219015)
                      ·
                        rfl

theorem cell23_6290828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 5, 1, 2, 2].length) (baseStart_6290828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290828 prefixEnd_6290828 := by exact prefixLift 6290828
  have htrace : WordTrace (prefixWord ++ tailWord_6290828) baseStart_6290828 baseEnd_6290828 := by
    simpa [prefixWord, tailWord_6290828, baseEnd_6290828] using wordTrace_append hprefix tailTrace_6290828
  have hstable : (prefixWord ++ tailWord_6290828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290828).length < 2 ^ (prefixWord ++ tailWord_6290828).sum := by decide
  have hdescent : baseEnd_6290828 < baseStart_6290828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290834 : List Nat := [3, 2, 3, 3, 1, 11]
def baseStart_6290834 : Nat := 118140960795 + 6290834 * 2 ^ 59
def prefixEnd_6290834 : Nat := 4983230072969 + 3 ^ 40 * 6290834 * 2
def baseEnd_6290834 : Nat := 13293092838050803772609

theorem tailTrace_6290834 : CollatzResearch.WordTrace tailWord_6290834 prefixEnd_6290834 13293092838050803772609 := by
  unfold tailWord_6290834
  simp only [CollatzResearch.WordTrace]
  refine ⟨57361391422847570438959889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152963710460926854503893037 57361391422847570438959889)
  ·
    refine ⟨43021043567135677829219917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57361391422847570438959889 43021043567135677829219917)
    ·
      refine ⟨16132891337675879185957469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43021043567135677829219917 16132891337675879185957469)
      ·
        refine ⟨6049834251628454694734051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16132891337675879185957469 6049834251628454694734051)
        ·
          refine ⟨9074751377442682042101077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6049834251628454694734051 9074751377442682042101077)
          ·
            refine ⟨13293092838050803772609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9074751377442682042101077 13293092838050803772609)
            ·
              rfl

theorem cell23_6290834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 11].length) (baseStart_6290834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290834 prefixEnd_6290834 := by exact prefixLift 6290834
  have htrace : WordTrace (prefixWord ++ tailWord_6290834) baseStart_6290834 baseEnd_6290834 := by
    simpa [prefixWord, tailWord_6290834, baseEnd_6290834] using wordTrace_append hprefix tailTrace_6290834
  have hstable : (prefixWord ++ tailWord_6290834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290834).length < 2 ^ (prefixWord ++ tailWord_6290834).sum := by decide
  have hdescent : baseEnd_6290834 < baseStart_6290834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290845 : List Nat := [1, 4, 2, 1, 3, 2, 1, 4, 1, 2, 2]
def baseStart_6290845 : Nat := 118140960795 + 6290845 * 2 ^ 59
def prefixEnd_6290845 : Nat := 4983230072969 + 3 ^ 40 * 6290845 * 2
def baseEnd_6290845 : Nat := 3230227207933544773706437

theorem tailTrace_6290845 : CollatzResearch.WordTrace tailWord_6290845 prefixEnd_6290845 3230227207933544773706437 := by
  unfold tailWord_6290845
  simp only [CollatzResearch.WordTrace]
  refine ⟨229445966894350430634489989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152963977929566953756326659 229445966894350430634489989)
  ·
    refine ⟨43021118792690705743966873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229445966894350430634489989 43021118792690705743966873)
    ·
      refine ⟨32265839094518029307975155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43021118792690705743966873 32265839094518029307975155)
      ·
        refine ⟨48398758641777043961962733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32265839094518029307975155 48398758641777043961962733)
        ·
          refine ⟨18149534490666391485736025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48398758641777043961962733 18149534490666391485736025)
          ·
            refine ⟨13612150867999793614302019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18149534490666391485736025 13612150867999793614302019)
            ·
              refine ⟨20418226301999690421453029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13612150867999793614302019 20418226301999690421453029)
              ·
                refine ⟨3828417431624941954022443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20418226301999690421453029 3828417431624941954022443)
                ·
                  refine ⟨5742626147437412931033665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3828417431624941954022443 5742626147437412931033665)
                  ·
                    refine ⟨4306969610578059698275249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5742626147437412931033665 4306969610578059698275249)
                    ·
                      refine ⟨3230227207933544773706437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4306969610578059698275249 3230227207933544773706437)
                      ·
                        rfl

theorem cell23_6290845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_6290845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290845 prefixEnd_6290845 := by exact prefixLift 6290845
  have htrace : WordTrace (prefixWord ++ tailWord_6290845) baseStart_6290845 baseEnd_6290845 := by
    simpa [prefixWord, tailWord_6290845, baseEnd_6290845] using wordTrace_append hprefix tailTrace_6290845
  have hstable : (prefixWord ++ tailWord_6290845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290845).length < 2 ^ (prefixWord ++ tailWord_6290845).sum := by decide
  have hdescent : baseEnd_6290845 < baseStart_6290845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290847 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 2, 7]
def baseStart_6290847 : Nat := 118140960795 + 6290847 * 2 ^ 59
def prefixEnd_6290847 : Nat := 4983230072969 + 3 ^ 40 * 6290847 * 2
def baseEnd_6290847 : Nat := 1076742744964951255293809

theorem tailTrace_6290847 : CollatzResearch.WordTrace tailWord_6290847 prefixEnd_6290847 1076742744964951255293809 := by
  unfold tailWord_6290847
  simp only [CollatzResearch.WordTrace]
  refine ⟨229446039840343184976062795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152964026560228789984041863 229446039840343184976062795)
  ·
    refine ⟨344169059760514777464094193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229446039840343184976062795 344169059760514777464094193)
    ·
      refine ⟨258126794820386083098070645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344169059760514777464094193 258126794820386083098070645)
      ·
        refine ⟨24199387014411195290444123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 258126794820386083098070645 24199387014411195290444123)
        ·
          refine ⟨36299080521616792935666185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24199387014411195290444123 36299080521616792935666185)
          ·
            refine ⟨27224310391212594701749639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36299080521616792935666185 27224310391212594701749639)
            ·
              refine ⟨40836465586818892052624459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27224310391212594701749639 40836465586818892052624459)
              ·
                refine ⟨61254698380228338078936689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40836465586818892052624459 61254698380228338078936689)
                ·
                  refine ⟨45941023785171253559202517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61254698380228338078936689 45941023785171253559202517)
                  ·
                    refine ⟨1076742744964951255293809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45941023785171253559202517 1076742744964951255293809)
                    ·
                      rfl

theorem cell23_6290847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 7].length) (baseStart_6290847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290847 prefixEnd_6290847 := by exact prefixLift 6290847
  have htrace : WordTrace (prefixWord ++ tailWord_6290847) baseStart_6290847 baseEnd_6290847 := by
    simpa [prefixWord, tailWord_6290847, baseEnd_6290847] using wordTrace_append hprefix tailTrace_6290847
  have hstable : (prefixWord ++ tailWord_6290847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290847).length < 2 ^ (prefixWord ++ tailWord_6290847).sum := by decide
  have hdescent : baseEnd_6290847 < baseStart_6290847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290861 : List Nat := [1, 5, 2, 2, 1, 1, 1, 3, 1, 3, 3]
def baseStart_6290861 : Nat := 118140960795 + 6290861 * 2 ^ 59
def prefixEnd_6290861 : Nat := 4983230072969 + 3 ^ 40 * 6290861 * 2
def baseEnd_6290861 : Nat := 3230235423624016711106363

theorem tailTrace_6290861 : CollatzResearch.WordTrace tailWord_6290861 prefixEnd_6290861 3230235423624016711106363 := by
  unfold tailWord_6290861
  simp only [CollatzResearch.WordTrace]
  refine ⟨229446550462292465367072437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152964366974861643578048291 229446550462292465367072437)
  ·
    refine ⟨21510614105839918628163041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 229446550462292465367072437 21510614105839918628163041)
    ·
      refine ⟨16132960579379938971122281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21510614105839918628163041 16132960579379938971122281)
      ·
        refine ⟨12099720434534954228341711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16132960579379938971122281 12099720434534954228341711)
        ·
          refine ⟨18149580651802431342512567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12099720434534954228341711 18149580651802431342512567)
          ·
            refine ⟨27224370977703647013768851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18149580651802431342512567 27224370977703647013768851)
            ·
              refine ⟨40836556466555470520653277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27224370977703647013768851 40836556466555470520653277)
              ·
                refine ⟨15313708674958301445244979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40836556466555470520653277 15313708674958301445244979)
                ·
                  refine ⟨22970563012437452167867469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15313708674958301445244979 22970563012437452167867469)
                  ·
                    refine ⟨8613961129664044562950301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22970563012437452167867469 8613961129664044562950301)
                    ·
                      refine ⟨3230235423624016711106363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8613961129664044562950301 3230235423624016711106363)
                      ·
                        rfl

theorem cell23_6290861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_6290861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290861 prefixEnd_6290861 := by exact prefixLift 6290861
  have htrace : WordTrace (prefixWord ++ tailWord_6290861) baseStart_6290861 baseEnd_6290861 := by
    simpa [prefixWord, tailWord_6290861, baseEnd_6290861] using wordTrace_append hprefix tailTrace_6290861
  have hstable : (prefixWord ++ tailWord_6290861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290861).length < 2 ^ (prefixWord ++ tailWord_6290861).sum := by decide
  have hdescent : baseEnd_6290861 < baseStart_6290861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290871 : List Nat := [1, 1, 3, 1, 3, 2, 2, 4, 1, 3, 2]
def baseStart_6290871 : Nat := 118140960795 + 6290871 * 2 ^ 59
def prefixEnd_6290871 : Nat := 4983230072969 + 3 ^ 40 * 6290871 * 2
def baseEnd_6290871 : Nat := 3230240558430561671981317

theorem tailTrace_6290871 : CollatzResearch.WordTrace tailWord_6290871 prefixEnd_6290871 3230240558430561671981317 := by
  unfold tailWord_6290871
  simp only [CollatzResearch.WordTrace]
  refine ⟨229446915192256237074936467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152964610128170824716624311 229446915192256237074936467)
  ·
    refine ⟨344170372788384355612404701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229446915192256237074936467 344170372788384355612404701)
    ·
      refine ⟨129063889795644133354651763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344170372788384355612404701 129063889795644133354651763)
      ·
        refine ⟨193595834693466200031977645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129063889795644133354651763 193595834693466200031977645)
        ·
          refine ⟨72598438010049825011991617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193595834693466200031977645 72598438010049825011991617)
          ·
            refine ⟨54448828507537368758993713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72598438010049825011991617 54448828507537368758993713)
            ·
              refine ⟨40836621380653026569245285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54448828507537368758993713 40836621380653026569245285)
              ·
                refine ⟨7656866508872442481733491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40836621380653026569245285 7656866508872442481733491)
                ·
                  refine ⟨11485299763308663722600237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7656866508872442481733491 11485299763308663722600237)
                  ·
                    refine ⟨4306987411240748895975089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11485299763308663722600237 4306987411240748895975089)
                    ·
                      refine ⟨3230240558430561671981317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4306987411240748895975089 3230240558430561671981317)
                      ·
                        rfl

theorem cell23_6290871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 3, 2].length) (baseStart_6290871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290871 prefixEnd_6290871 := by exact prefixLift 6290871
  have htrace : WordTrace (prefixWord ++ tailWord_6290871) baseStart_6290871 baseEnd_6290871 := by
    simpa [prefixWord, tailWord_6290871, baseEnd_6290871] using wordTrace_append hprefix tailTrace_6290871
  have hstable : (prefixWord ++ tailWord_6290871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290871).length < 2 ^ (prefixWord ++ tailWord_6290871).sum := by decide
  have hdescent : baseEnd_6290871 < baseStart_6290871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290877 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 1, 8]
def baseStart_6290877 : Nat := 118140960795 + 6290877 * 2 ^ 59
def prefixEnd_6290877 : Nat := 4983230072969 + 3 ^ 40 * 6290877 * 2
def baseEnd_6290877 : Nat := 1076747879771496216168763

theorem tailTrace_6290877 : CollatzResearch.WordTrace tailWord_6290877 prefixEnd_6290877 1076747879771496216168763 := by
  unfold tailWord_6290877
  simp only [CollatzResearch.WordTrace]
  refine ⟨229447134030234500099654885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152964756020156333399769923 229447134030234500099654885)
  ·
    refine ⟨43021337630668968768685291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229447134030234500099654885 43021337630668968768685291)
    ·
      refine ⟨64532006446003453153027937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43021337630668968768685291 64532006446003453153027937)
      ·
        refine ⟨48399004834502589864770953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64532006446003453153027937 48399004834502589864770953)
        ·
          refine ⟨36299253625876942398578215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48399004834502589864770953 36299253625876942398578215)
          ·
            refine ⟨54448880438815413597867323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36299253625876942398578215 54448880438815413597867323)
            ·
              refine ⟨81673320658223120396800985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54448880438815413597867323 81673320658223120396800985)
              ·
                refine ⟨61254990493667340297600739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81673320658223120396800985 61254990493667340297600739)
                ·
                  refine ⟨91882485740501010446401109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61254990493667340297600739 91882485740501010446401109)
                  ·
                    refine ⟨1076747879771496216168763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 91882485740501010446401109 1076747879771496216168763)
                    ·
                      rfl

theorem cell23_6290877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_6290877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290877 prefixEnd_6290877 := by exact prefixLift 6290877
  have htrace : WordTrace (prefixWord ++ tailWord_6290877) baseStart_6290877 baseEnd_6290877 := by
    simpa [prefixWord, tailWord_6290877, baseEnd_6290877] using wordTrace_append hprefix tailTrace_6290877
  have hstable : (prefixWord ++ tailWord_6290877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290877).length < 2 ^ (prefixWord ++ tailWord_6290877).sum := by decide
  have hdescent : baseEnd_6290877 < baseStart_6290877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290887 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 5]
def baseStart_6290887 : Nat := 118140960795 + 6290887 * 2 ^ 59
def prefixEnd_6290887 : Nat := 4983230072969 + 3 ^ 40 * 6290887 * 2
def baseEnd_6290887 : Nat := 3230248774121033609381243

theorem tailTrace_6290887 : CollatzResearch.WordTrace tailWord_6290887 prefixEnd_6290887 3230248774121033609381243 := by
  unfold tailWord_6290887
  simp only [CollatzResearch.WordTrace]
  refine ⟨229447498760198271807518915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152964999173465514538345943 229447498760198271807518915)
  ·
    refine ⟨344171248140297407711278373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229447498760198271807518915 344171248140297407711278373)
    ·
      refine ⟨64532109026305763945864695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 344171248140297407711278373 64532109026305763945864695)
      ·
        refine ⟨96798163539458645918797043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64532109026305763945864695 96798163539458645918797043)
        ·
          refine ⟨145197245309187968878195565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96798163539458645918797043 145197245309187968878195565)
          ·
            refine ⟨54448966990945488329323337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145197245309187968878195565 54448966990945488329323337)
            ·
              refine ⟨40836725243209116246992503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54448966990945488329323337 40836725243209116246992503)
              ·
                refine ⟨61255087864813674370488755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40836725243209116246992503 61255087864813674370488755)
                ·
                  refine ⟨91882631797220511555733133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61255087864813674370488755 91882631797220511555733133)
                  ·
                    refine ⟨34455986923957691833399925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91882631797220511555733133 34455986923957691833399925)
                    ·
                      refine ⟨3230248774121033609381243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34455986923957691833399925 3230248774121033609381243)
                      ·
                        rfl

theorem cell23_6290887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_6290887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290887 prefixEnd_6290887 := by exact prefixLift 6290887
  have htrace : WordTrace (prefixWord ++ tailWord_6290887) baseStart_6290887 baseEnd_6290887 := by
    simpa [prefixWord, tailWord_6290887, baseEnd_6290887] using wordTrace_append hprefix tailTrace_6290887
  have hstable : (prefixWord ++ tailWord_6290887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290887).length < 2 ^ (prefixWord ++ tailWord_6290887).sum := by decide
  have hdescent : baseEnd_6290887 < baseStart_6290887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290941 : List Nat := [1, 4, 1, 1, 1, 4, 3, 3, 5]
def baseStart_6290941 : Nat := 118140960795 + 6290941 * 2 ^ 59
def prefixEnd_6290941 : Nat := 4983230072969 + 3 ^ 40 * 6290941 * 2
def baseEnd_6290941 : Nat := 358919611341819599789555

theorem tailTrace_6290941 : CollatzResearch.WordTrace tailWord_6290941 prefixEnd_6290941 358919611341819599789555 := by
  unfold tailWord_6290941
  simp only [CollatzResearch.WordTrace]
  refine ⟨229449468302002639029984677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152966312201335092686656451 229449468302002639029984677)
  ·
    refine ⟨43021775306625494818122127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229449468302002639029984677 43021775306625494818122127)
    ·
      refine ⟨64532662959938242227183191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43021775306625494818122127 64532662959938242227183191)
      ·
        refine ⟨96798994439907363340774787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64532662959938242227183191 96798994439907363340774787)
        ·
          refine ⟨145198491659861045011162181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96798994439907363340774787 145198491659861045011162181)
          ·
            refine ⟨27224717186223945939592909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145198491659861045011162181 27224717186223945939592909)
            ·
              refine ⟨10209268944833979727347341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27224717186223945939592909 10209268944833979727347341)
              ·
                refine ⟨3828475854312742397755253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10209268944833979727347341 3828475854312742397755253)
                ·
                  refine ⟨358919611341819599789555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3828475854312742397755253 358919611341819599789555)
                  ·
                    rfl

theorem cell23_6290941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 3, 5].length) (baseStart_6290941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290941 prefixEnd_6290941 := by exact prefixLift 6290941
  have htrace : WordTrace (prefixWord ++ tailWord_6290941) baseStart_6290941 baseEnd_6290941 := by
    simpa [prefixWord, tailWord_6290941, baseEnd_6290941] using wordTrace_append hprefix tailTrace_6290941
  have hstable : (prefixWord ++ tailWord_6290941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290941).length < 2 ^ (prefixWord ++ tailWord_6290941).sum := by decide
  have hdescent : baseEnd_6290941 < baseStart_6290941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290954 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 4, 5]
def baseStart_6290954 : Nat := 118140960795 + 6290954 * 2 ^ 59
def prefixEnd_6290954 : Nat := 4983230072969 + 3 ^ 40 * 6290954 * 2
def baseEnd_6290954 : Nat := 1076761059108294949081145

theorem tailTrace_6290954 : CollatzResearch.WordTrace tailWord_6290954 prefixEnd_6290954 1076761059108294949081145 := by
  unfold tailWord_6290954
  simp only [CollatzResearch.WordTrace]
  refine ⟨57362485612738885562551979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152966628300637028166805277 57362485612738885562551979)
  ·
    refine ⟨86043728419108328343827969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57362485612738885562551979 86043728419108328343827969)
    ·
      refine ⟨64532796314331246257870977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86043728419108328343827969 64532796314331246257870977)
      ·
        refine ⟨48399597235748434693403233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64532796314331246257870977 48399597235748434693403233)
        ·
          refine ⟨36299697926811326020052425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48399597235748434693403233 36299697926811326020052425)
          ·
            refine ⟨27224773445108494515039319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36299697926811326020052425 27224773445108494515039319)
            ·
              refine ⟨40837160167662741772558979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27224773445108494515039319 40837160167662741772558979)
              ·
                refine ⟨61255740251494112658838469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40837160167662741772558979 61255740251494112658838469)
                ·
                  refine ⟨11485451297155146123532213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61255740251494112658838469 11485451297155146123532213)
                  ·
                    refine ⟨1076761059108294949081145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11485451297155146123532213 1076761059108294949081145)
                    ·
                      rfl

theorem cell23_6290954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_6290954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290954 prefixEnd_6290954 := by exact prefixLift 6290954
  have htrace : WordTrace (prefixWord ++ tailWord_6290954) baseStart_6290954 baseEnd_6290954 := by
    simpa [prefixWord, tailWord_6290954, baseEnd_6290954] using wordTrace_append hprefix tailTrace_6290954
  have hstable : (prefixWord ++ tailWord_6290954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290954).length < 2 ^ (prefixWord ++ tailWord_6290954).sum := by decide
  have hdescent : baseEnd_6290954 < baseStart_6290954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290958 : List Nat := [4, 1, 1, 2, 5, 1, 1, 1, 7]
def baseStart_6290958 : Nat := 118140960795 + 6290958 * 2 ^ 59
def prefixEnd_6290958 : Nat := 4983230072969 + 3 ^ 40 * 6290958 * 2
def baseEnd_6290958 : Nat := 358920581249722536843713

theorem tailTrace_6290958 : CollatzResearch.WordTrace tailWord_6290958 prefixEnd_6290958 358920581249722536843713 := by
  unfold tailWord_6290958
  simp only [CollatzResearch.WordTrace]
  refine ⟨28681261042867631366669191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152966725561960700622235685 28681261042867631366669191)
  ·
    refine ⟨43021891564301447050003787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28681261042867631366669191 43021891564301447050003787)
    ·
      refine ⟨64532837346452170575005681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43021891564301447050003787 64532837346452170575005681)
      ·
        refine ⟨48399628009839127931254261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64532837346452170575005681 48399628009839127931254261)
        ·
          refine ⟨4537465125922418243555087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48399628009839127931254261 4537465125922418243555087)
          ·
            refine ⟨6806197688883627365332631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4537465125922418243555087 6806197688883627365332631)
            ·
              refine ⟨10209296533325441047998947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6806197688883627365332631 10209296533325441047998947)
              ·
                refine ⟨15313944799988161571998421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10209296533325441047998947 15313944799988161571998421)
                ·
                  refine ⟨358920581249722536843713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15313944799988161571998421 358920581249722536843713)
                  ·
                    rfl

theorem cell23_6290958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 7].length) (baseStart_6290958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290958 prefixEnd_6290958 := by exact prefixLift 6290958
  have htrace : WordTrace (prefixWord ++ tailWord_6290958) baseStart_6290958 baseEnd_6290958 := by
    simpa [prefixWord, tailWord_6290958, baseEnd_6290958] using wordTrace_append hprefix tailTrace_6290958
  have hstable : (prefixWord ++ tailWord_6290958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290958).length < 2 ^ (prefixWord ++ tailWord_6290958).sum := by decide
  have hdescent : baseEnd_6290958 < baseStart_6290958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290987 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 6]
def baseStart_6290987 : Nat := 118140960795 + 6290987 * 2 ^ 59
def prefixEnd_6290987 : Nat := 4983230072969 + 3 ^ 40 * 6290987 * 2
def baseEnd_6290987 : Nat := 3230300122186483218130783

theorem tailTrace_6290987 : CollatzResearch.WordTrace tailWord_6290987 prefixEnd_6290987 3230300122186483218130783 := by
  unfold tailWord_6290987
  simp only [CollatzResearch.WordTrace]
  refine ⟨229451146059835988886159215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152967430706557325924106143 229451146059835988886159215)
  ·
    refine ⟨344176719089753983329238823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229451146059835988886159215 344176719089753983329238823)
    ·
      refine ⟨516265078634630974993858235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344176719089753983329238823 516265078634630974993858235)
      ·
        refine ⟨774397617951946462490787353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516265078634630974993858235 774397617951946462490787353)
        ·
          refine ⟨580798213463959846868090515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 774397617951946462490787353 580798213463959846868090515)
          ·
            refine ⟨871197320195939770302135773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580798213463959846868090515 871197320195939770302135773)
            ·
              refine ⟨326698995073477413863300915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 871197320195939770302135773 326698995073477413863300915)
              ·
                refine ⟨490048492610216120794951373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 326698995073477413863300915 490048492610216120794951373)
                ·
                  refine ⟨183768184728831045298106765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 490048492610216120794951373 183768184728831045298106765)
                  ·
                    refine ⟨68913069273311641986790037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 183768184728831045298106765 68913069273311641986790037)
                    ·
                      refine ⟨3230300122186483218130783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68913069273311641986790037 3230300122186483218130783)
                      ·
                        rfl

theorem cell23_6290987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 6].length) (baseStart_6290987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290987 prefixEnd_6290987 := by exact prefixLift 6290987
  have htrace : WordTrace (prefixWord ++ tailWord_6290987) baseStart_6290987 baseEnd_6290987 := by
    simpa [prefixWord, tailWord_6290987, baseEnd_6290987] using wordTrace_append hprefix tailTrace_6290987
  have hstable : (prefixWord ++ tailWord_6290987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290987).length < 2 ^ (prefixWord ++ tailWord_6290987).sum := by decide
  have hdescent : baseEnd_6290987 < baseStart_6290987 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291018 : List Nat := [3, 1, 2, 1, 1, 3, 3, 4, 1, 4]
def baseStart_6291018 : Nat := 118140960795 + 6291018 * 2 ^ 59
def prefixEnd_6291018 : Nat := 4983230072969 + 3 ^ 40 * 6291018 * 2
def baseEnd_6291018 : Nat := 1076772013362257532281047

theorem tailTrace_6291018 : CollatzResearch.WordTrace tailWord_6291018 prefixEnd_6291018 1076772013362257532281047 := by
  unfold tailWord_6291018
  simp only [CollatzResearch.WordTrace]
  refine ⟨57363069180680920295134427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152968184481815787453691805 57363069180680920295134427)
  ·
    refine ⟨86044603771021380442701641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57363069180680920295134427 86044603771021380442701641)
    ·
      refine ⟨64533452828266035332026231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86044603771021380442701641 64533452828266035332026231)
      ·
        refine ⟨96800179242399052998039347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64533452828266035332026231 96800179242399052998039347)
        ·
          refine ⟨145200268863598579497059021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96800179242399052998039347 145200268863598579497059021)
          ·
            refine ⟨54450100823849467311397133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145200268863598579497059021 54450100823849467311397133)
            ·
              refine ⟨20418787808943550241773925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54450100823849467311397133 20418787808943550241773925)
              ·
                refine ⟨3828522714176915670332611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20418787808943550241773925 3828522714176915670332611)
                ·
                  refine ⟨5742784071265373505498917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3828522714176915670332611 5742784071265373505498917)
                  ·
                    refine ⟨1076772013362257532281047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5742784071265373505498917 1076772013362257532281047)
                    ·
                      rfl

theorem cell23_6291018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_6291018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291018 prefixEnd_6291018 := by exact prefixLift 6291018
  have htrace : WordTrace (prefixWord ++ tailWord_6291018) baseStart_6291018 baseEnd_6291018 := by
    simpa [prefixWord, tailWord_6291018, baseEnd_6291018] using wordTrace_append hprefix tailTrace_6291018
  have hstable : (prefixWord ++ tailWord_6291018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291018).length < 2 ^ (prefixWord ++ tailWord_6291018).sum := by decide
  have hdescent : baseEnd_6291018 < baseStart_6291018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291126 : List Nat := [5, 1, 3, 1, 1, 2, 3, 2, 1, 1, 3]
def baseStart_6291126 : Nat := 118140960795 + 6291126 * 2 ^ 59
def prefixEnd_6291126 : Nat := 4983230072969 + 3 ^ 40 * 6291126 * 2
def baseEnd_6291126 : Nat := 3230371495997458174292645

theorem tailTrace_6291126 : CollatzResearch.WordTrace tailWord_6291126 prefixEnd_6291126 3230371495997458174292645 := by
  unfold tailWord_6291126
  simp only [CollatzResearch.WordTrace]
  refine ⟨14341013487895775976591827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152970810537554943750312821 14341013487895775976591827)
  ·
    refine ⟨21511520231843663964887741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14341013487895775976591827 21511520231843663964887741)
    ·
      refine ⟨8066820086941373986832903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21511520231843663964887741 8066820086941373986832903)
      ·
        refine ⟨12100230130412060980249355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8066820086941373986832903 12100230130412060980249355)
        ·
          refine ⟨18150345195618091470374033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12100230130412060980249355 18150345195618091470374033)
          ·
            refine ⟨13612758896713568602780525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18150345195618091470374033 13612758896713568602780525)
            ·
              refine ⟨5104784586267588226042697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13612758896713568602780525 5104784586267588226042697)
              ·
                refine ⟨3828588439700691169532023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5104784586267588226042697 3828588439700691169532023)
                ·
                  refine ⟨5742882659551036754298035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3828588439700691169532023 5742882659551036754298035)
                  ·
                    refine ⟨8614323989326555131447053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5742882659551036754298035 8614323989326555131447053)
                    ·
                      refine ⟨3230371495997458174292645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8614323989326555131447053 3230371495997458174292645)
                      ·
                        rfl

theorem cell23_6291126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_6291126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291126 prefixEnd_6291126 := by exact prefixLift 6291126
  have htrace : WordTrace (prefixWord ++ tailWord_6291126) baseStart_6291126 baseEnd_6291126 := by
    simpa [prefixWord, tailWord_6291126, baseEnd_6291126] using wordTrace_append hprefix tailTrace_6291126
  have hstable : (prefixWord ++ tailWord_6291126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291126).length < 2 ^ (prefixWord ++ tailWord_6291126).sum := by decide
  have hdescent : baseEnd_6291126 < baseStart_6291126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291132 : List Nat := [2, 2, 2, 3, 1, 4, 1, 1, 3, 2, 2]
def baseStart_6291132 : Nat := 118140960795 + 6291132 * 2 ^ 59
def prefixEnd_6291132 : Nat := 4983230072969 + 3 ^ 40 * 6291132 * 2
def baseEnd_6291132 : Nat := 3230374576881385150817617

theorem tailTrace_6291132 : CollatzResearch.WordTrace tailWord_6291132 prefixEnd_6291132 3230374576881385150817617 := by
  unfold tailWord_6291132
  simp only [CollatzResearch.WordTrace]
  refine ⟨114728217322155339325093825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152970956429540452433458433 114728217322155339325093825)
  ·
    refine ⟨86046162991616504493820369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114728217322155339325093825 86046162991616504493820369)
    ·
      refine ⟨64534622243712378370365277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86046162991616504493820369 64534622243712378370365277)
      ·
        refine ⟨24200483341392141888886979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64534622243712378370365277 24200483341392141888886979)
        ·
          refine ⟨36300725012088212833330469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24200483341392141888886979 36300725012088212833330469)
          ·
            refine ⟨6806385939766539906249463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36300725012088212833330469 6806385939766539906249463)
            ·
              refine ⟨10209578909649809859374195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6806385939766539906249463 10209578909649809859374195)
              ·
                refine ⟨15314368364474714789061293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10209578909649809859374195 15314368364474714789061293)
                ·
                  refine ⟨5742888136678018045897985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15314368364474714789061293 5742888136678018045897985)
                  ·
                    refine ⟨4307166102508513534423489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5742888136678018045897985 4307166102508513534423489)
                    ·
                      refine ⟨3230374576881385150817617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4307166102508513534423489 3230374576881385150817617)
                      ·
                        rfl

theorem cell23_6291132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_6291132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291132 prefixEnd_6291132 := by exact prefixLift 6291132
  have htrace : WordTrace (prefixWord ++ tailWord_6291132) baseStart_6291132 baseEnd_6291132 := by
    simpa [prefixWord, tailWord_6291132, baseEnd_6291132] using wordTrace_append hprefix tailTrace_6291132
  have hstable : (prefixWord ++ tailWord_6291132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291132).length < 2 ^ (prefixWord ++ tailWord_6291132).sum := by decide
  have hdescent : baseEnd_6291132 < baseStart_6291132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291191 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 2, 4, 3]
def baseStart_6291191 : Nat := 118140960795 + 6291191 * 2 ^ 59
def prefixEnd_6291191 : Nat := 4983230072969 + 3 ^ 40 * 6291191 * 2
def baseEnd_6291191 : Nat := 3230404872240000419979845

theorem tailTrace_6291191 : CollatzResearch.WordTrace tailWord_6291191 prefixEnd_6291191 3230404872240000419979845 := by
  unfold tailWord_6291191
  simp only [CollatzResearch.WordTrace]
  refine ⟨229458586551096931726585427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152972391034064621151056951 229458586551096931726585427)
  ·
    refine ⟨344187879826645397589878141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229458586551096931726585427 344187879826645397589878141)
    ·
      refine ⟨129070454934992024096204303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344187879826645397589878141 129070454934992024096204303)
      ·
        refine ⟨193605682402488036144306455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129070454934992024096204303 193605682402488036144306455)
        ·
          refine ⟨290408523603732054216459683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193605682402488036144306455 290408523603732054216459683)
          ·
            refine ⟨435612785405598081324689525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290408523603732054216459683 435612785405598081324689525)
            ·
              refine ⟨40838698631774820124189643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 435612785405598081324689525 40838698631774820124189643)
              ·
                refine ⟨61258047947662230186284465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40838698631774820124189643 61258047947662230186284465)
                ·
                  refine ⟨45943535960746672639713349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61258047947662230186284465 45943535960746672639713349)
                  ·
                    refine ⟨8614412992640001119946253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45943535960746672639713349 8614412992640001119946253)
                    ·
                      refine ⟨3230404872240000419979845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8614412992640001119946253 3230404872240000419979845)
                      ·
                        rfl

theorem cell23_6291191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 4, 3].length) (baseStart_6291191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291191 prefixEnd_6291191 := by exact prefixLift 6291191
  have htrace : WordTrace (prefixWord ++ tailWord_6291191) baseStart_6291191 baseEnd_6291191 := by
    simpa [prefixWord, tailWord_6291191, baseEnd_6291191] using wordTrace_append hprefix tailTrace_6291191
  have hstable : (prefixWord ++ tailWord_6291191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291191).length < 2 ^ (prefixWord ++ tailWord_6291191).sum := by decide
  have hdescent : baseEnd_6291191 < baseStart_6291191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291201 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 1, 4, 4]
def baseStart_6291201 : Nat := 118140960795 + 6291201 * 2 ^ 59
def prefixEnd_6291201 : Nat := 4983230072969 + 3 ^ 40 * 6291201 * 2
def baseEnd_6291201 : Nat := 3230410007046545380854799

theorem tailTrace_6291201 : CollatzResearch.WordTrace tailWord_6291201 prefixEnd_6291201 3230410007046545380854799 := by
  unfold tailWord_6291201
  simp only [CollatzResearch.WordTrace]
  refine ⟨229458951281060703434449457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152972634187373802289632971 229458951281060703434449457)
  ·
    refine ⟨172094213460795527575837093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229458951281060703434449457 172094213460795527575837093)
    ·
      refine ⟨32267665023899161420469455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172094213460795527575837093 32267665023899161420469455)
      ·
        refine ⟨48401497535848742130704183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32267665023899161420469455 48401497535848742130704183)
        ·
          refine ⟨72602246303773113196056275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48401497535848742130704183 72602246303773113196056275)
          ·
            refine ⟨108903369455659669794084413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72602246303773113196056275 108903369455659669794084413)
            ·
              refine ⟨40838763545872376172781655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108903369455659669794084413 40838763545872376172781655)
              ·
                refine ⟨61258145318808564259172483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40838763545872376172781655 61258145318808564259172483)
                ·
                  refine ⟨91887217978212846388758725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61258145318808564259172483 91887217978212846388758725)
                  ·
                    refine ⟨17228853370914908697892261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91887217978212846388758725 17228853370914908697892261)
                    ·
                      refine ⟨3230410007046545380854799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17228853370914908697892261 3230410007046545380854799)
                      ·
                        rfl

theorem cell23_6291201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_6291201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291201 prefixEnd_6291201 := by exact prefixLift 6291201
  have htrace : WordTrace (prefixWord ++ tailWord_6291201) baseStart_6291201 baseEnd_6291201 := by
    simpa [prefixWord, tailWord_6291201, baseEnd_6291201] using wordTrace_append hprefix tailTrace_6291201
  have hstable : (prefixWord ++ tailWord_6291201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291201).length < 2 ^ (prefixWord ++ tailWord_6291201).sum := by decide
  have hdescent : baseEnd_6291201 < baseStart_6291201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291206 : List Nat := [6, 2, 2, 1, 1, 1, 3, 7]
def baseStart_6291206 : Nat := 118140960795 + 6291206 * 2 ^ 59
def prefixEnd_6291206 : Nat := 4983230072969 + 3 ^ 40 * 6291206 * 2
def baseEnd_6291206 : Nat := 119644910164808068936751

theorem tailTrace_6291206 : CollatzResearch.WordTrace tailWord_6291206 prefixEnd_6291206 119644910164808068936751 := by
  unfold tailWord_6291206
  simp only [CollatzResearch.WordTrace]
  refine ⟨7170597926438830915261921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 152972755764028392858920981 7170597926438830915261921)
  ·
    refine ⟨5377948444829123186446441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7170597926438830915261921 5377948444829123186446441)
    ·
      refine ⟨4033461333621842389834831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5377948444829123186446441 4033461333621842389834831)
      ·
        refine ⟨6050192000432763584752247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4033461333621842389834831 6050192000432763584752247)
        ·
          refine ⟨9075288000649145377128371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6050192000432763584752247 9075288000649145377128371)
          ·
            refine ⟨13612932000973718065692557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9075288000649145377128371 13612932000973718065692557)
            ·
              refine ⟨5104849500365144274634709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13612932000973718065692557 5104849500365144274634709)
              ·
                refine ⟨119644910164808068936751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5104849500365144274634709 119644910164808068936751)
                ·
                  rfl

theorem cell23_6291206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_6291206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291206 prefixEnd_6291206 := by exact prefixLift 6291206
  have htrace : WordTrace (prefixWord ++ tailWord_6291206) baseStart_6291206 baseEnd_6291206 := by
    simpa [prefixWord, tailWord_6291206, baseEnd_6291206] using wordTrace_append hprefix tailTrace_6291206
  have hstable : (prefixWord ++ tailWord_6291206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291206).length < 2 ^ (prefixWord ++ tailWord_6291206).sum := by decide
  have hdescent : baseEnd_6291206 < baseStart_6291206 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291305 : List Nat := [1, 2, 1, 1, 1, 3, 1, 8, 1, 4]
def baseStart_6291305 : Nat := 118140960795 + 6291305 * 2 ^ 59
def prefixEnd_6291305 : Nat := 4983230072969 + 3 ^ 40 * 6291305 * 2
def baseEnd_6291305 : Nat := 1076821136344870991318107

theorem tailTrace_6291305 : CollatzResearch.WordTrace tailWord_6291305 prefixEnd_6291305 1076821136344870991318107 := by
  unfold tailWord_6291305
  simp only [CollatzResearch.WordTrace]
  refine ⟨229462744472683929196235369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152975162981789286130823579 229462744472683929196235369)
  ·
    refine ⟨172097058354512946897176527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229462744472683929196235369 172097058354512946897176527)
    ·
      refine ⟨258145587531769420345764791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172097058354512946897176527 258145587531769420345764791)
      ·
        refine ⟨387218381297654130518647187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258145587531769420345764791 387218381297654130518647187)
        ·
          refine ⟨580827571946481195777970781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387218381297654130518647187 580827571946481195777970781)
          ·
            refine ⟨217810339479930448416739043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 580827571946481195777970781 217810339479930448416739043)
            ·
              refine ⟨326715509219895672625108565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217810339479930448416739043 326715509219895672625108565)
              ·
                refine ⟨3828697373670652413575491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 326715509219895672625108565 3828697373670652413575491)
                ·
                  refine ⟨5743046060505978620363237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3828697373670652413575491 5743046060505978620363237)
                  ·
                    refine ⟨1076821136344870991318107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5743046060505978620363237 1076821136344870991318107)
                    ·
                      rfl

theorem cell23_6291305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 8, 1, 4].length) (baseStart_6291305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291305 prefixEnd_6291305 := by exact prefixLift 6291305
  have htrace : WordTrace (prefixWord ++ tailWord_6291305) baseStart_6291305 baseEnd_6291305 := by
    simpa [prefixWord, tailWord_6291305, baseEnd_6291305] using wordTrace_append hprefix tailTrace_6291305
  have hstable : (prefixWord ++ tailWord_6291305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291305).length < 2 ^ (prefixWord ++ tailWord_6291305).sum := by decide
  have hdescent : baseEnd_6291305 < baseStart_6291305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291352 : List Nat := [2, 1, 2, 6, 1, 1, 2, 2, 6]
def baseStart_6291352 : Nat := 118140960795 + 6291352 * 2 ^ 59
def prefixEnd_6291352 : Nat := 4983230072969 + 3 ^ 40 * 6291352 * 2
def baseEnd_6291352 : Nat := 358943060291708254451845

theorem tailTrace_6291352 : CollatzResearch.WordTrace tailWord_6291352 prefixEnd_6291352 358943060291708254451845 := by
  unfold tailWord_6291352
  simp only [CollatzResearch.WordTrace]
  refine ⟨114732229351756828111598155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152976305802342437482130873 114732229351756828111598155)
  ·
    refine ⟨172098344027635242167397233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114732229351756828111598155 172098344027635242167397233)
    ·
      refine ⟨129073758020726431625547925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172098344027635242167397233 129073758020726431625547925)
      ·
        refine ⟨6050332407221551482447559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 129073758020726431625547925 6050332407221551482447559)
        ·
          refine ⟨9075498610832327223671339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6050332407221551482447559 9075498610832327223671339)
          ·
            refine ⟨13613247916248490835507009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9075498610832327223671339 13613247916248490835507009)
            ·
              refine ⟨10209935937186368126630257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13613247916248490835507009 10209935937186368126630257)
              ·
                refine ⟨7657451952889776094972693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10209935937186368126630257 7657451952889776094972693)
                ·
                  refine ⟨358943060291708254451845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7657451952889776094972693 358943060291708254451845)
                  ·
                    rfl

theorem cell23_6291352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 6].length) (baseStart_6291352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291352 prefixEnd_6291352 := by exact prefixLift 6291352
  have htrace : WordTrace (prefixWord ++ tailWord_6291352) baseStart_6291352 baseEnd_6291352 := by
    simpa [prefixWord, tailWord_6291352, baseEnd_6291352] using wordTrace_append hprefix tailTrace_6291352
  have hstable : (prefixWord ++ tailWord_6291352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291352).length < 2 ^ (prefixWord ++ tailWord_6291352).sum := by decide
  have hdescent : baseEnd_6291352 < baseStart_6291352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291356 : List Nat := [2, 2, 3, 3, 1, 3, 2, 2, 1, 4]
def baseStart_6291356 : Nat := 118140960795 + 6291356 * 2 ^ 59
def prefixEnd_6291356 : Nat := 4983230072969 + 3 ^ 40 * 6291356 * 2
def baseEnd_6291356 : Nat := 1076829865515997424805529

theorem tailTrace_6291356 : CollatzResearch.WordTrace tailWord_6291356 prefixEnd_6291356 1076829865515997424805529 := by
  unfold tailWord_6291356
  simp only [CollatzResearch.WordTrace]
  refine ⟨114732302297749582453170961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152976403063666109937561281 114732302297749582453170961)
  ·
    refine ⟨86049226723312186839878221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114732302297749582453170961 86049226723312186839878221)
    ·
      refine ⟨32268460021242070064954333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86049226723312186839878221 32268460021242070064954333)
      ·
        refine ⟨12100672507965776274357875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32268460021242070064954333 12100672507965776274357875)
        ·
          refine ⟨18151008761948664411536813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12100672507965776274357875 18151008761948664411536813)
          ·
            refine ⟨6806628285730749154326305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18151008761948664411536813 6806628285730749154326305)
            ·
              refine ⟨5104971214298061865744729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6806628285730749154326305 5104971214298061865744729)
              ·
                refine ⟨3828728410723546399308547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5104971214298061865744729 3828728410723546399308547)
                ·
                  refine ⟨5743092616085319598962821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3828728410723546399308547 5743092616085319598962821)
                  ·
                    refine ⟨1076829865515997424805529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5743092616085319598962821 1076829865515997424805529)
                    ·
                      rfl

theorem cell23_6291356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_6291356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291356 prefixEnd_6291356 := by exact prefixLift 6291356
  have htrace : WordTrace (prefixWord ++ tailWord_6291356) baseStart_6291356 baseEnd_6291356 := by
    simpa [prefixWord, tailWord_6291356, baseEnd_6291356] using wordTrace_append hprefix tailTrace_6291356
  have hstable : (prefixWord ++ tailWord_6291356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291356).length < 2 ^ (prefixWord ++ tailWord_6291356).sum := by decide
  have hdescent : baseEnd_6291356 < baseStart_6291356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291385 : List Nat := [1, 2, 1, 4, 2, 1, 2, 4, 1, 1, 4]
def baseStart_6291385 : Nat := 118140960795 + 6291385 * 2 ^ 59
def prefixEnd_6291385 : Nat := 4983230072969 + 3 ^ 40 * 6291385 * 2
def baseEnd_6291385 : Nat := 3230504487486972660953953

theorem tailTrace_6291385 : CollatzResearch.WordTrace tailWord_6291385 prefixEnd_6291385 3230504487486972660953953 := by
  unfold tailWord_6291385
  simp only [CollatzResearch.WordTrace]
  refine ⟨229465662312394102859147609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152977108208262735239431739 229465662312394102859147609)
  ·
    refine ⟨172099246734295577144360707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229465662312394102859147609 172099246734295577144360707)
    ·
      refine ⟨258148870101443365716541061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172099246734295577144360707 258148870101443365716541061)
      ·
        refine ⟨48402913144020631071851449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 258148870101443365716541061 48402913144020631071851449)
        ·
          refine ⟨36302184858015473303888587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48402913144020631071851449 36302184858015473303888587)
          ·
            refine ⟨54453277287023209955832881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36302184858015473303888587 54453277287023209955832881)
            ·
              refine ⟨40839957965267407466874661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54453277287023209955832881 40839957965267407466874661)
              ·
                refine ⟨7657492118487638900038999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40839957965267407466874661 7657492118487638900038999)
                ·
                  refine ⟨11486238177731458350058499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7657492118487638900038999 11486238177731458350058499)
                  ·
                    refine ⟨17229357266597187525087749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11486238177731458350058499 17229357266597187525087749)
                    ·
                      refine ⟨3230504487486972660953953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17229357266597187525087749 3230504487486972660953953)
                      ·
                        rfl

theorem cell23_6291385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_6291385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291385 prefixEnd_6291385 := by exact prefixLift 6291385
  have htrace : WordTrace (prefixWord ++ tailWord_6291385) baseStart_6291385 baseEnd_6291385 := by
    simpa [prefixWord, tailWord_6291385, baseEnd_6291385] using wordTrace_append hprefix tailTrace_6291385
  have hstable : (prefixWord ++ tailWord_6291385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291385).length < 2 ^ (prefixWord ++ tailWord_6291385).sum := by decide
  have hdescent : baseEnd_6291385 < baseStart_6291385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291389 : List Nat := [1, 4, 1, 2, 3, 3, 1, 1, 2, 3, 2]
def baseStart_6291389 : Nat := 118140960795 + 6291389 * 2 ^ 59
def prefixEnd_6291389 : Nat := 4983230072969 + 3 ^ 40 * 6291389 * 2
def baseEnd_6291389 : Nat := 3230506541409590645303935

theorem tailTrace_6291389 : CollatzResearch.WordTrace tailWord_6291389 prefixEnd_6291389 3230506541409590645303935 := by
  unfold tailWord_6291389
  simp only [CollatzResearch.WordTrace]
  refine ⟨229465808204379611542293221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152977205469586407694862147 229465808204379611542293221)
  ·
    refine ⟨43024839038321177164179979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229465808204379611542293221 43024839038321177164179979)
    ·
      refine ⟨64537258557481765746269969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43024839038321177164179979 64537258557481765746269969)
      ·
        refine ⟨48402943918111324309702477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64537258557481765746269969 48402943918111324309702477)
        ·
          refine ⟨18151103969291746616138429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48402943918111324309702477 18151103969291746616138429)
          ·
            refine ⟨6806663988484404981051911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18151103969291746616138429 6806663988484404981051911)
            ·
              refine ⟨10209995982726607471577867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6806663988484404981051911 10209995982726607471577867)
              ·
                refine ⟨15314993974089911207366801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10209995982726607471577867 15314993974089911207366801)
                ·
                  refine ⟨11486245480567433405525101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15314993974089911207366801 11486245480567433405525101)
                  ·
                    refine ⟨4307342055212787527071913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11486245480567433405525101 4307342055212787527071913)
                    ·
                      refine ⟨3230506541409590645303935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4307342055212787527071913 3230506541409590645303935)
                      ·
                        rfl

theorem cell23_6291389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_6291389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291389 prefixEnd_6291389 := by exact prefixLift 6291389
  have htrace : WordTrace (prefixWord ++ tailWord_6291389) baseStart_6291389 baseEnd_6291389 := by
    simpa [prefixWord, tailWord_6291389, baseEnd_6291389] using wordTrace_append hprefix tailTrace_6291389
  have hstable : (prefixWord ++ tailWord_6291389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291389).length < 2 ^ (prefixWord ++ tailWord_6291389).sum := by decide
  have hdescent : baseEnd_6291389 < baseStart_6291389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291402 : List Nat := [3, 1, 2, 1, 2, 1, 6, 1, 1, 1, 4]
def baseStart_6291402 : Nat := 118140960795 + 6291402 * 2 ^ 59
def prefixEnd_6291402 : Nat := 4983230072969 + 3 ^ 40 * 6291402 * 2
def baseEnd_6291402 : Nat := 3230513216658099094441375

theorem tailTrace_6291402 : CollatzResearch.WordTrace tailWord_6291402 prefixEnd_6291402 3230513216658099094441375 := by
  unfold tailWord_6291402
  simp only [CollatzResearch.WordTrace]
  refine ⟨57366570588333128690629115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152977521568888343175010973 57366570588333128690629115)
  ·
    refine ⟨86049855882499693035943673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57366570588333128690629115 86049855882499693035943673)
    ·
      refine ⟨64537391911874769776957755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86049855882499693035943673 64537391911874769776957755)
      ·
        refine ⟨96806087867812154665436633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64537391911874769776957755 96806087867812154665436633)
        ·
          refine ⟨72604565900859115999077475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96806087867812154665436633 72604565900859115999077475)
          ·
            refine ⟨108906848851288673998616213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72604565900859115999077475 108906848851288673998616213)
            ·
              refine ⟨5105008539904156593685135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 108906848851288673998616213 5105008539904156593685135)
              ·
                refine ⟨7657512809856234890527703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5105008539904156593685135 7657512809856234890527703)
                ·
                  refine ⟨11486269214784352335791555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7657512809856234890527703 11486269214784352335791555)
                  ·
                    refine ⟨17229403822176528503687333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11486269214784352335791555 17229403822176528503687333)
                    ·
                      refine ⟨3230513216658099094441375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17229403822176528503687333 3230513216658099094441375)
                      ·
                        rfl

theorem cell23_6291402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 1, 1, 4].length) (baseStart_6291402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291402 prefixEnd_6291402 := by exact prefixLift 6291402
  have htrace : WordTrace (prefixWord ++ tailWord_6291402) baseStart_6291402 baseEnd_6291402 := by
    simpa [prefixWord, tailWord_6291402, baseEnd_6291402] using wordTrace_append hprefix tailTrace_6291402
  have hstable : (prefixWord ++ tailWord_6291402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291402).length < 2 ^ (prefixWord ++ tailWord_6291402).sum := by decide
  have hdescent : baseEnd_6291402 < baseStart_6291402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291448 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 2, 2, 5]
def baseStart_6291448 : Nat := 118140960795 + 6291448 * 2 ^ 59
def prefixEnd_6291448 : Nat := 4983230072969 + 3 ^ 40 * 6291448 * 2
def baseEnd_6291448 : Nat := 3230536836768205914466163

theorem tailTrace_6291448 : CollatzResearch.WordTrace tailWord_6291448 prefixEnd_6291448 3230536836768205914466163 := by
  unfold tailWord_6291448
  simp only [CollatzResearch.WordTrace]
  refine ⟨114733980055582932309345499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152978640074110576412460665 114733980055582932309345499)
  ·
    refine ⟨172100970083374398464018249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114733980055582932309345499 172100970083374398464018249)
    ·
      refine ⟨129075727562530798848013687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172100970083374398464018249 129075727562530798848013687)
      ·
        refine ⟨193613591343796198272020531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129075727562530798848013687 193613591343796198272020531)
        ·
          refine ⟨290420387015694297408030797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193613591343796198272020531 290420387015694297408030797)
          ·
            refine ⟨108907645130885361528011549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 290420387015694297408030797 108907645130885361528011549)
            ·
              refine ⟨40840366924082010573004331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108907645130885361528011549 40840366924082010573004331)
              ·
                refine ⟨61260550386123015859506497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40840366924082010573004331 61260550386123015859506497)
                ·
                  refine ⟨45945412789592261894629873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61260550386123015859506497 45945412789592261894629873)
                  ·
                    refine ⟨34459059592194196420972405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45945412789592261894629873 34459059592194196420972405)
                    ·
                      refine ⟨3230536836768205914466163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34459059592194196420972405 3230536836768205914466163)
                      ·
                        rfl

theorem cell23_6291448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_6291448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291448 prefixEnd_6291448 := by exact prefixLift 6291448
  have htrace : WordTrace (prefixWord ++ tailWord_6291448) baseStart_6291448 baseEnd_6291448 := by
    simpa [prefixWord, tailWord_6291448, baseEnd_6291448] using wordTrace_append hprefix tailTrace_6291448
  have hstable : (prefixWord ++ tailWord_6291448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291448).length < 2 ^ (prefixWord ++ tailWord_6291448).sum := by decide
  have hdescent : baseEnd_6291448 < baseStart_6291448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291496 : List Nat := [2, 1, 5, 3, 1, 1, 1, 1, 3, 3, 2]
def baseStart_6291496 : Nat := 118140960795 + 6291496 * 2 ^ 59
def prefixEnd_6291496 : Nat := 4983230072969 + 3 ^ 40 * 6291496 * 2
def baseEnd_6291496 : Nat := 3230561483839621726665943

theorem tailTrace_6291496 : CollatzResearch.WordTrace tailWord_6291496 prefixEnd_6291496 3230561483839621726665943 := by
  unfold tailWord_6291496
  simp only [CollatzResearch.WordTrace]
  refine ⟨114734855407495984408219171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152979807209994645877625561 114734855407495984408219171)
  ·
    refine ⟨172102283111243976612328757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114734855407495984408219171 172102283111243976612328757)
    ·
      refine ⟨16134589041679122807405821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 172102283111243976612328757 16134589041679122807405821)
      ·
        refine ⟨6050470890629671052777183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16134589041679122807405821 6050470890629671052777183)
        ·
          refine ⟨9075706335944506579165775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6050470890629671052777183 9075706335944506579165775)
          ·
            refine ⟨13613559503916759868748663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9075706335944506579165775 13613559503916759868748663)
            ·
              refine ⟨20420339255875139803122995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13613559503916759868748663 20420339255875139803122995)
              ·
                refine ⟨30630508883812709704684493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20420339255875139803122995 30630508883812709704684493)
                ·
                  refine ⟨11486440831429766139256685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30630508883812709704684493 11486440831429766139256685)
                  ·
                    refine ⟨4307415311786162302221257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11486440831429766139256685 4307415311786162302221257)
                    ·
                      refine ⟨3230561483839621726665943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4307415311786162302221257 3230561483839621726665943)
                      ·
                        rfl

theorem cell23_6291496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_6291496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291496 prefixEnd_6291496 := by exact prefixLift 6291496
  have htrace : WordTrace (prefixWord ++ tailWord_6291496) baseStart_6291496 baseEnd_6291496 := by
    simpa [prefixWord, tailWord_6291496, baseEnd_6291496] using wordTrace_append hprefix tailTrace_6291496
  have hstable : (prefixWord ++ tailWord_6291496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291496).length < 2 ^ (prefixWord ++ tailWord_6291496).sum := by decide
  have hdescent : baseEnd_6291496 < baseStart_6291496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291525 : List Nat := [1, 3, 1, 1, 1, 3, 1, 4, 2, 3, 3]
def baseStart_6291525 : Nat := 118140960795 + 6291525 * 2 ^ 59
def prefixEnd_6291525 : Nat := 4983230072969 + 3 ^ 40 * 6291525 * 2
def baseEnd_6291525 : Nat := 3230576374778602113203309

theorem tailTrace_6291525 : CollatzResearch.WordTrace tailWord_6291525 prefixEnd_6291525 3230576374778602113203309 := by
  unfold tailWord_6291525
  simp only [CollatzResearch.WordTrace]
  refine ⟨229470768531886906769244029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152980512354591271179496019 229470768531886906769244029)
  ·
    refine ⟨86051538199457590038466511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229470768531886906769244029 86051538199457590038466511)
    ·
      refine ⟨129077307299186385057699767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86051538199457590038466511 129077307299186385057699767)
      ·
        refine ⟨193615960948779577586549651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129077307299186385057699767 193615960948779577586549651)
        ·
          refine ⟨290423941423169366379824477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193615960948779577586549651 290423941423169366379824477)
          ·
            refine ⟨108908978033688512392434179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 290423941423169366379824477 108908978033688512392434179)
            ·
              refine ⟨163363467050532768588651269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108908978033688512392434179 163363467050532768588651269)
              ·
                refine ⟨30630650071974894110372113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163363467050532768588651269 30630650071974894110372113)
                ·
                  refine ⟨22972987553981170582779085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30630650071974894110372113 22972987553981170582779085)
                  ·
                    refine ⟨8614870332742938968542157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22972987553981170582779085 8614870332742938968542157)
                    ·
                      refine ⟨3230576374778602113203309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8614870332742938968542157 3230576374778602113203309)
                      ·
                        rfl

theorem cell23_6291525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 3, 3].length) (baseStart_6291525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291525 prefixEnd_6291525 := by exact prefixLift 6291525
  have htrace : WordTrace (prefixWord ++ tailWord_6291525) baseStart_6291525 baseEnd_6291525 := by
    simpa [prefixWord, tailWord_6291525, baseEnd_6291525] using wordTrace_append hprefix tailTrace_6291525
  have hstable : (prefixWord ++ tailWord_6291525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291525).length < 2 ^ (prefixWord ++ tailWord_6291525).sum := by decide
  have hdescent : baseEnd_6291525 < baseStart_6291525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291562 : List Nat := [3, 1, 3, 2, 3, 1, 1, 1, 1, 7]
def baseStart_6291562 : Nat := 118140960795 + 6291562 * 2 ^ 59
def prefixEnd_6291562 : Nat := 4983230072969 + 3 ^ 40 * 6291562 * 2
def baseEnd_6291562 : Nat := 1076865124520939489480213

theorem tailTrace_6291562 : CollatzResearch.WordTrace tailWord_6291562 prefixEnd_6291562 1076865124520939489480213 := by
  unfold tailWord_6291562
  simp only [CollatzResearch.WordTrace]
  refine ⟨57368029508188215522085235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152981412021835241392227293 57368029508188215522085235)
  ·
    refine ⟨86052044262282323283127853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57368029508188215522085235 86052044262282323283127853)
    ·
      refine ⟨32269516598355871231172945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86052044262282323283127853 32269516598355871231172945)
      ·
        refine ⟨24202137448766903423379709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32269516598355871231172945 24202137448766903423379709)
        ·
          refine ⟨9075801543287588783767391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24202137448766903423379709 9075801543287588783767391)
          ·
            refine ⟨13613702314931383175651087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9075801543287588783767391 13613702314931383175651087)
            ·
              refine ⟨20420553472397074763476631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13613702314931383175651087 20420553472397074763476631)
              ·
                refine ⟨30630830208595612145214947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20420553472397074763476631 30630830208595612145214947)
                ·
                  refine ⟨45946245312893418217822421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30630830208595612145214947 45946245312893418217822421)
                  ·
                    refine ⟨1076865124520939489480213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45946245312893418217822421 1076865124520939489480213)
                    ·
                      rfl

theorem cell23_6291562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_6291562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291562 prefixEnd_6291562 := by exact prefixLift 6291562
  have htrace : WordTrace (prefixWord ++ tailWord_6291562) baseStart_6291562 baseEnd_6291562 := by
    simpa [prefixWord, tailWord_6291562, baseEnd_6291562] using wordTrace_append hprefix tailTrace_6291562
  have hstable : (prefixWord ++ tailWord_6291562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291562).length < 2 ^ (prefixWord ++ tailWord_6291562).sum := by decide
  have hdescent : baseEnd_6291562 < baseStart_6291562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291602 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 3, 4, 3]
def baseStart_6291602 : Nat := 118140960795 + 6291602 * 2 ^ 59
def prefixEnd_6291602 : Nat := 4983230072969 + 3 ^ 40 * 6291602 * 2
def baseEnd_6291602 : Nat := 3230615912788998311940455

theorem tailTrace_6291602 : CollatzResearch.WordTrace tailWord_6291602 prefixEnd_6291602 3230615912788998311940455 := by
  unfold tailWord_6291602
  simp only [CollatzResearch.WordTrace]
  refine ⟨57368394238151987229949265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152982384635071965946531373 57368394238151987229949265)
  ·
    refine ⟨43026295678613990422461949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57368394238151987229949265 43026295678613990422461949)
    ·
      refine ⟨16134860879480246408423231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43026295678613990422461949 16134860879480246408423231)
      ·
        refine ⟨24202291319220369612634847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16134860879480246408423231 24202291319220369612634847)
        ·
          refine ⟨36303436978830554418952271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24202291319220369612634847 36303436978830554418952271)
          ·
            refine ⟨54455155468245831628428407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36303436978830554418952271 54455155468245831628428407)
            ·
              refine ⟨81682733202368747442642611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54455155468245831628428407 81682733202368747442642611)
              ·
                refine ⟨122524099803553121163963917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81682733202368747442642611 122524099803553121163963917)
                ·
                  refine ⟨45946537426332420436486469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122524099803553121163963917 45946537426332420436486469)
                  ·
                    refine ⟨8614975767437328831841213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45946537426332420436486469 8614975767437328831841213)
                    ·
                      refine ⟨3230615912788998311940455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8614975767437328831841213 3230615912788998311940455)
                      ·
                        rfl

theorem cell23_6291602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_6291602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291602 prefixEnd_6291602 := by exact prefixLift 6291602
  have htrace : WordTrace (prefixWord ++ tailWord_6291602) baseStart_6291602 baseEnd_6291602 := by
    simpa [prefixWord, tailWord_6291602, baseEnd_6291602] using wordTrace_append hprefix tailTrace_6291602
  have hstable : (prefixWord ++ tailWord_6291602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291602).length < 2 ^ (prefixWord ++ tailWord_6291602).sum := by decide
  have hdescent : baseEnd_6291602 < baseStart_6291602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291635 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 5, 5]
def baseStart_6291635 : Nat := 118140960795 + 6291635 * 2 ^ 59
def prefixEnd_6291635 : Nat := 4983230072969 + 3 ^ 40 * 6291635 * 2
def baseEnd_6291635 : Nat := 1076877619216865560942601

theorem tailTrace_6291635 : CollatzResearch.WordTrace tailWord_6291635 prefixEnd_6291635 1076877619216865560942601 := by
  unfold tailWord_6291635
  simp only [CollatzResearch.WordTrace]
  refine ⟨229474780561488395555748359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152983187040992263703832239 229474780561488395555748359)
  ·
    refine ⟨344212170842232593333622539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229474780561488395555748359 344212170842232593333622539)
    ·
      refine ⟨516318256263348890000433809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344212170842232593333622539 516318256263348890000433809)
      ·
        refine ⟨387238692197511667500325357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 516318256263348890000433809 387238692197511667500325357)
        ·
          refine ⟨145214509574066875312622009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 387238692197511667500325357 145214509574066875312622009)
          ·
            refine ⟨108910882180550156484466507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145214509574066875312622009 108910882180550156484466507)
            ·
              refine ⟨163366323270825234726699761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108910882180550156484466507 163366323270825234726699761)
              ·
                refine ⟨122524742453118926045024821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163366323270825234726699761 122524742453118926045024821)
                ·
                  refine ⟨11486694604979899316721077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122524742453118926045024821 11486694604979899316721077)
                  ·
                    refine ⟨1076877619216865560942601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11486694604979899316721077 1076877619216865560942601)
                    ·
                      rfl

theorem cell23_6291635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 5].length) (baseStart_6291635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291635 prefixEnd_6291635 := by exact prefixLift 6291635
  have htrace : WordTrace (prefixWord ++ tailWord_6291635) baseStart_6291635 baseEnd_6291635 := by
    simpa [prefixWord, tailWord_6291635, baseEnd_6291635] using wordTrace_append hprefix tailTrace_6291635
  have hstable : (prefixWord ++ tailWord_6291635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291635).length < 2 ^ (prefixWord ++ tailWord_6291635).sum := by decide
  have hdescent : baseEnd_6291635 < baseStart_6291635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291645 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 2, 1, 7]
def baseStart_6291645 : Nat := 118140960795 + 6291645 * 2 ^ 59
def prefixEnd_6291645 : Nat := 4983230072969 + 3 ^ 40 * 6291645 * 2
def baseEnd_6291645 : Nat := 3230637992457141643702757

theorem tailTrace_6291645 : CollatzResearch.WordTrace tailWord_6291645 prefixEnd_6291645 3230637992457141643702757 := by
  unfold tailWord_6291645
  simp only [CollatzResearch.WordTrace]
  refine ⟨229475145291452167263612389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152983430194301444842408259 229475145291452167263612389)
  ·
    refine ⟨43026589742147281361927323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229475145291452167263612389 43026589742147281361927323)
    ·
      refine ⟨64539884613220922042890985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43026589742147281361927323 64539884613220922042890985)
      ·
        refine ⟨48404913459915691532168239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64539884613220922042890985 48404913459915691532168239)
        ·
          refine ⟨72607370189873537298252359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48404913459915691532168239 72607370189873537298252359)
          ·
            refine ⟨108911055284810305947378539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72607370189873537298252359 108911055284810305947378539)
            ·
              refine ⟨163366582927215458921067809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108911055284810305947378539 163366582927215458921067809)
              ·
                refine ⟨122524937195411594190800857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163366582927215458921067809 122524937195411594190800857)
                ·
                  refine ⟨91893702896558695643100643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122524937195411594190800857 91893702896558695643100643)
                  ·
                    refine ⟨137840554344838043464650965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91893702896558695643100643 137840554344838043464650965)
                    ·
                      refine ⟨3230637992457141643702757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 137840554344838043464650965 3230637992457141643702757)
                      ·
                        rfl

theorem cell23_6291645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_6291645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291645 prefixEnd_6291645 := by exact prefixLift 6291645
  have htrace : WordTrace (prefixWord ++ tailWord_6291645) baseStart_6291645 baseEnd_6291645 := by
    simpa [prefixWord, tailWord_6291645, baseEnd_6291645] using wordTrace_append hprefix tailTrace_6291645
  have hstable : (prefixWord ++ tailWord_6291645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291645).length < 2 ^ (prefixWord ++ tailWord_6291645).sum := by decide
  have hdescent : baseEnd_6291645 < baseStart_6291645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291655 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 4]
def baseStart_6291655 : Nat := 118140960795 + 6291655 * 2 ^ 59
def prefixEnd_6291655 : Nat := 4983230072969 + 3 ^ 40 * 6291655 * 2
def baseEnd_6291655 : Nat := 3230643127263686604577711

theorem tailTrace_6291655 : CollatzResearch.WordTrace tailWord_6291655 prefixEnd_6291655 3230643127263686604577711 := by
  unfold tailWord_6291655
  simp only [CollatzResearch.WordTrace]
  refine ⟨229475510021415938971476419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152983673347610625980984279 229475510021415938971476419)
  ·
    refine ⟨344213265032123908457214629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229475510021415938971476419 344213265032123908457214629)
    ·
      refine ⟨64539987193523232835727743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 344213265032123908457214629 64539987193523232835727743)
      ·
        refine ⟨96809980790284849253591615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64539987193523232835727743 96809980790284849253591615)
        ·
          refine ⟨145214971185427273880387423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96809980790284849253591615 145214971185427273880387423)
          ·
            refine ⟨217822456778140910820581135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145214971185427273880387423 217822456778140910820581135)
            ·
              refine ⟨326733685167211366230871703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217822456778140910820581135 326733685167211366230871703)
              ·
                refine ⟨490100527750817049346307555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 326733685167211366230871703 490100527750817049346307555)
                ·
                  refine ⟨735150791626225574019461333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 490100527750817049346307555 735150791626225574019461333)
                  ·
                    refine ⟨17230096678739661891081125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 735150791626225574019461333 17230096678739661891081125)
                    ·
                      refine ⟨3230643127263686604577711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17230096678739661891081125 3230643127263686604577711)
                      ·
                        rfl

theorem cell23_6291655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_6291655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291655 prefixEnd_6291655 := by exact prefixLift 6291655
  have htrace : WordTrace (prefixWord ++ tailWord_6291655) baseStart_6291655 baseEnd_6291655 := by
    simpa [prefixWord, tailWord_6291655, baseEnd_6291655] using wordTrace_append hprefix tailTrace_6291655
  have hstable : (prefixWord ++ tailWord_6291655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291655).length < 2 ^ (prefixWord ++ tailWord_6291655).sum := by decide
  have hdescent : baseEnd_6291655 < baseStart_6291655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291669 : List Nat := [1, 3, 2, 4, 2, 1, 1, 1, 3, 5]
def baseStart_6291669 : Nat := 118140960795 + 6291669 * 2 ^ 59
def prefixEnd_6291669 : Nat := 4983230072969 + 3 ^ 40 * 6291669 * 2
def baseEnd_6291669 : Nat := 1076883438664283183267549

theorem tailTrace_6291669 : CollatzResearch.WordTrace tailWord_6291669 prefixEnd_6291669 1076883438664283183267549 := by
  unfold tailWord_6291669
  simp only [CollatzResearch.WordTrace]
  refine ⟨229476020643365219362486061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152984013762243479574990707 229476020643365219362486061)
  ·
    refine ⟨86053507741261957260932273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229476020643365219362486061 86053507741261957260932273)
    ·
      refine ⟨64540130805946467945699205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86053507741261957260932273 64540130805946467945699205)
      ·
        refine ⟨12101274526114962739818601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64540130805946467945699205 12101274526114962739818601)
        ·
          refine ⟨9075955894586222054863951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12101274526114962739818601 9075955894586222054863951)
          ·
            refine ⟨13613933841879333082295927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9075955894586222054863951 13613933841879333082295927)
            ·
              refine ⟨20420900762818999623443891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13613933841879333082295927 20420900762818999623443891)
              ·
                refine ⟨30631351144228499435165837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20420900762818999623443891 30631351144228499435165837)
                ·
                  refine ⟨11486756679085687288187189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30631351144228499435165837 11486756679085687288187189)
                  ·
                    refine ⟨1076883438664283183267549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11486756679085687288187189 1076883438664283183267549)
                    ·
                      rfl

theorem cell23_6291669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_6291669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291669 prefixEnd_6291669 := by exact prefixLift 6291669
  have htrace : WordTrace (prefixWord ++ tailWord_6291669) baseStart_6291669 baseEnd_6291669 := by
    simpa [prefixWord, tailWord_6291669, baseEnd_6291669] using wordTrace_append hprefix tailTrace_6291669
  have hstable : (prefixWord ++ tailWord_6291669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291669).length < 2 ^ (prefixWord ++ tailWord_6291669).sum := by decide
  have hdescent : baseEnd_6291669 < baseStart_6291669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291675 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 5]
def baseStart_6291675 : Nat := 118140960795 + 6291675 * 2 ^ 59
def prefixEnd_6291675 : Nat := 4983230072969 + 3 ^ 40 * 6291675 * 2
def baseEnd_6291675 : Nat := 3230653396876776526327619

theorem tailTrace_6291675 : CollatzResearch.WordTrace tailWord_6291675 prefixEnd_6291675 3230653396876776526327619 := by
  unfold tailWord_6291675
  simp only [CollatzResearch.WordTrace]
  refine ⟨229476239481343482387204479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152984159654228988258136319 229476239481343482387204479)
  ·
    refine ⟨344214359222015223580806719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229476239481343482387204479 344214359222015223580806719)
    ·
      refine ⟨516321538833022835371210079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344214359222015223580806719 516321538833022835371210079)
      ·
        refine ⟨774482308249534253056815119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516321538833022835371210079 774482308249534253056815119)
        ·
          refine ⟨1161723462374301379585222679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 774482308249534253056815119 1161723462374301379585222679)
          ·
            refine ⟨1742585193561452069377834019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1161723462374301379585222679 1742585193561452069377834019)
            ·
              refine ⟨2613877790342178104066751029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1742585193561452069377834019 2613877790342178104066751029)
              ·
                refine ⟨245051042844579197256257909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2613877790342178104066751029 245051042844579197256257909)
                ·
                  refine ⟨22973535266679299742774179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 245051042844579197256257909 22973535266679299742774179)
                  ·
                    refine ⟨34460302900018949614161269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22973535266679299742774179 34460302900018949614161269)
                    ·
                      refine ⟨3230653396876776526327619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34460302900018949614161269 3230653396876776526327619)
                      ·
                        rfl

theorem cell23_6291675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 5].length) (baseStart_6291675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291675 prefixEnd_6291675 := by exact prefixLift 6291675
  have htrace : WordTrace (prefixWord ++ tailWord_6291675) baseStart_6291675 baseEnd_6291675 := by
    simpa [prefixWord, tailWord_6291675, baseEnd_6291675] using wordTrace_append hprefix tailTrace_6291675
  have hstable : (prefixWord ++ tailWord_6291675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291675).length < 2 ^ (prefixWord ++ tailWord_6291675).sum := by decide
  have hdescent : baseEnd_6291675 < baseStart_6291675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291689 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 5, 2, 2]
def baseStart_6291689 : Nat := 118140960795 + 6291689 * 2 ^ 59
def prefixEnd_6291689 : Nat := 4983230072969 + 3 ^ 40 * 6291689 * 2
def baseEnd_6291689 : Nat := 3230660585605939471552555

theorem tailTrace_6291689 : CollatzResearch.WordTrace tailWord_6291689 prefixEnd_6291689 3230660585605939471552555 := by
  unfold tailWord_6291689
  simp only [CollatzResearch.WordTrace]
  refine ⟨229476750103292762778214121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152984500068861841852142747 229476750103292762778214121)
  ·
    refine ⟨172107562577469572083660591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229476750103292762778214121 172107562577469572083660591)
    ·
      refine ⟨258161343866204358125490887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172107562577469572083660591 258161343866204358125490887)
      ·
        refine ⟨387242015799306537188236331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258161343866204358125490887 387242015799306537188236331)
        ·
          refine ⟨580863023698959805782354497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387242015799306537188236331 580863023698959805782354497)
          ·
            refine ⟨435647267774219854336765873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 580863023698959805782354497 435647267774219854336765873)
            ·
              refine ⟨326735450830664890752574405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435647267774219854336765873 326735450830664890752574405)
              ·
                refine ⟨61262897030749667016107701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 326735450830664890752574405 61262897030749667016107701)
                ·
                  refine ⟨5743396596632781282760097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61262897030749667016107701 5743396596632781282760097)
                  ·
                    refine ⟨4307547447474585962070073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5743396596632781282760097 4307547447474585962070073)
                    ·
                      refine ⟨3230660585605939471552555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4307547447474585962070073 3230660585605939471552555)
                      ·
                        rfl

theorem cell23_6291689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 5, 2, 2].length) (baseStart_6291689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291689 prefixEnd_6291689 := by exact prefixLift 6291689
  have htrace : WordTrace (prefixWord ++ tailWord_6291689) baseStart_6291689 baseEnd_6291689 := by
    simpa [prefixWord, tailWord_6291689, baseEnd_6291689] using wordTrace_append hprefix tailTrace_6291689
  have hstable : (prefixWord ++ tailWord_6291689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291689).length < 2 ^ (prefixWord ++ tailWord_6291689).sum := by decide
  have hdescent : baseEnd_6291689 < baseStart_6291689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291695 : List Nat := [1, 1, 2, 1, 6, 12]
def baseStart_6291695 : Nat := 118140960795 + 6291695 * 2 ^ 59
def prefixEnd_6291695 : Nat := 4983230072969 + 3 ^ 40 * 6291695 * 2
def baseEnd_6291695 : Nat := 13294912207777228181389

theorem tailTrace_6291695 : CollatzResearch.WordTrace tailWord_6291695 prefixEnd_6291695 13294912207777228181389 := by
  unfold tailWord_6291695
  simp only [CollatzResearch.WordTrace]
  refine ⟨229476968941271025802932539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152984645960847350535288359 229476968941271025802932539)
  ·
    refine ⟨344215453411906538704398809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229476968941271025802932539 344215453411906538704398809)
    ·
      refine ⟨258161590058929904028299107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344215453411906538704398809 258161590058929904028299107)
      ·
        refine ⟨387242385088394856042448661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258161590058929904028299107 387242385088394856042448661)
        ·
          refine ⟨18151986801018508876989781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 387242385088394856042448661 18151986801018508876989781)
          ·
            refine ⟨13294912207777228181389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 18151986801018508876989781 13294912207777228181389)
            ·
              rfl

theorem cell23_6291695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 12].length) (baseStart_6291695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291695 prefixEnd_6291695 := by exact prefixLift 6291695
  have htrace : WordTrace (prefixWord ++ tailWord_6291695) baseStart_6291695 baseEnd_6291695 := by
    simpa [prefixWord, tailWord_6291695, baseEnd_6291695] using wordTrace_append hprefix tailTrace_6291695
  have hstable : (prefixWord ++ tailWord_6291695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291695).length < 2 ^ (prefixWord ++ tailWord_6291695).sum := by decide
  have hdescent : baseEnd_6291695 < baseStart_6291695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291699 : List Nat := [1, 1, 1, 2, 2, 4, 4, 2, 2, 4]
def baseStart_6291699 : Nat := 118140960795 + 6291699 * 2 ^ 59
def prefixEnd_6291699 : Nat := 4983230072969 + 3 ^ 40 * 6291699 * 2
def baseEnd_6291699 : Nat := 1076888573470828144142503

theorem tailTrace_6291699 : CollatzResearch.WordTrace tailWord_6291699 prefixEnd_6291699 1076888573470828144142503 := by
  unfold tailWord_6291699
  simp only [CollatzResearch.WordTrace]
  refine ⟨229477114833256534486078151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152984743222171022990718767 229477114833256534486078151)
  ·
    refine ⟨344215672249884801729117227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229477114833256534486078151 344215672249884801729117227)
    ·
      refine ⟨516323508374827202593675841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344215672249884801729117227 516323508374827202593675841)
      ·
        refine ⟨387242631281120401945256881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 516323508374827202593675841 387242631281120401945256881)
        ·
          refine ⟨290431973460840301458942661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387242631281120401945256881 290431973460840301458942661)
          ·
            refine ⟨54455995023907556523551749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 290431973460840301458942661 54455995023907556523551749)
            ·
              refine ⟨10210499066982666848165953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54455995023907556523551749 10210499066982666848165953)
              ·
                refine ⟨7657874300237000136124465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10210499066982666848165953 7657874300237000136124465)
                ·
                  refine ⟨5743405725177750102093349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7657874300237000136124465 5743405725177750102093349)
                  ·
                    refine ⟨1076888573470828144142503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5743405725177750102093349 1076888573470828144142503)
                    ·
                      rfl

theorem cell23_6291699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 2, 4].length) (baseStart_6291699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291699 prefixEnd_6291699 := by exact prefixLift 6291699
  have htrace : WordTrace (prefixWord ++ tailWord_6291699) baseStart_6291699 baseEnd_6291699 := by
    simpa [prefixWord, tailWord_6291699, baseEnd_6291699] using wordTrace_append hprefix tailTrace_6291699
  have hstable : (prefixWord ++ tailWord_6291699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291699).length < 2 ^ (prefixWord ++ tailWord_6291699).sum := by decide
  have hdescent : baseEnd_6291699 < baseStart_6291699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291702 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6]
def baseStart_6291702 : Nat := 118140960795 + 6291702 * 2 ^ 59
def prefixEnd_6291702 : Nat := 4983230072969 + 3 ^ 40 * 6291702 * 2
def baseEnd_6291702 : Nat := 3230667260854447920689995

theorem tailTrace_6291702 : CollatzResearch.WordTrace tailWord_6291702 prefixEnd_6291702 3230667260854447920689995 := by
  unfold tailWord_6291702
  simp only [CollatzResearch.WordTrace]
  refine ⟨14342326515765354124902335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152984816168163777332291573 14342326515765354124902335)
  ·
    refine ⟨21513489773648031187353503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14342326515765354124902335 21513489773648031187353503)
    ·
      refine ⟨32270234660472046781030255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21513489773648031187353503 32270234660472046781030255)
      ·
        refine ⟨48405351990708070171545383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32270234660472046781030255 48405351990708070171545383)
        ·
          refine ⟨72608027986062105257318075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48405351990708070171545383 72608027986062105257318075)
          ·
            refine ⟨108912041979093157885977113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72608027986062105257318075 108912041979093157885977113)
            ·
              refine ⟨81684031484319868414482835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108912041979093157885977113 81684031484319868414482835)
              ·
                refine ⟨122526047226479802621724253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81684031484319868414482835 122526047226479802621724253)
                ·
                  refine ⟨45947267709929925983146595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122526047226479802621724253 45947267709929925983146595)
                  ·
                    refine ⟨68920901564894888974719893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45947267709929925983146595 68920901564894888974719893)
                    ·
                      refine ⟨3230667260854447920689995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68920901564894888974719893 3230667260854447920689995)
                      ·
                        rfl

theorem cell23_6291702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_6291702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291702 prefixEnd_6291702 := by exact prefixLift 6291702
  have htrace : WordTrace (prefixWord ++ tailWord_6291702) baseStart_6291702 baseEnd_6291702 := by
    simpa [prefixWord, tailWord_6291702, baseEnd_6291702] using wordTrace_append hprefix tailTrace_6291702
  have hstable : (prefixWord ++ tailWord_6291702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291702).length < 2 ^ (prefixWord ++ tailWord_6291702).sum := by decide
  have hdescent : baseEnd_6291702 < baseStart_6291702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291705 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 2, 2, 7]
def baseStart_6291705 : Nat := 118140960795 + 6291705 * 2 ^ 59
def prefixEnd_6291705 : Nat := 4983230072969 + 3 ^ 40 * 6291705 * 2
def baseEnd_6291705 : Nat := 3230668801296411408952481

theorem tailTrace_6291705 : CollatzResearch.WordTrace tailWord_6291705 prefixEnd_6291705 3230668801296411408952481 := by
  unfold tailWord_6291705
  simp only [CollatzResearch.WordTrace]
  refine ⟨229477333671234797510796569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152984889114156531673864379 229477333671234797510796569)
  ·
    refine ⟨172108000253426098133097427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229477333671234797510796569 172108000253426098133097427)
    ·
      refine ⟨258162000380139147199646141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172108000253426098133097427 258162000380139147199646141)
      ·
        refine ⟨96810750142552180199867303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258162000380139147199646141 96810750142552180199867303)
        ·
          refine ⟨145216125213828270299800955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96810750142552180199867303 145216125213828270299800955)
          ·
            refine ⟨217824187820742405449701433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145216125213828270299800955 217824187820742405449701433)
            ·
              refine ⟨163368140865556804087276075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217824187820742405449701433 163368140865556804087276075)
              ·
                refine ⟨245052211298335206130914113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163368140865556804087276075 245052211298335206130914113)
                ·
                  refine ⟨183789158473751404598185585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245052211298335206130914113 183789158473751404598185585)
                  ·
                    refine ⟨137841868855313553448639189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 183789158473751404598185585 137841868855313553448639189)
                    ·
                      refine ⟨3230668801296411408952481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 137841868855313553448639189 3230668801296411408952481)
                      ·
                        rfl

theorem cell23_6291705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_6291705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291705 prefixEnd_6291705 := by exact prefixLift 6291705
  have htrace : WordTrace (prefixWord ++ tailWord_6291705) baseStart_6291705 baseEnd_6291705 := by
    simpa [prefixWord, tailWord_6291705, baseEnd_6291705] using wordTrace_append hprefix tailTrace_6291705
  have hstable : (prefixWord ++ tailWord_6291705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291705).length < 2 ^ (prefixWord ++ tailWord_6291705).sum := by decide
  have hdescent : baseEnd_6291705 < baseStart_6291705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291743 : List Nat := [1, 1, 2, 4, 3, 3, 2, 1, 1, 2, 3]
def baseStart_6291743 : Nat := 118140960795 + 6291743 * 2 ^ 59
def prefixEnd_6291743 : Nat := 4983230072969 + 3 ^ 40 * 6291743 * 2
def baseEnd_6291743 : Nat := 3230688313561282260277307

theorem tailTrace_6291743 : CollatzResearch.WordTrace tailWord_6291743 prefixEnd_6291743 3230688313561282260277307 := by
  unfold tailWord_6291743
  simp only [CollatzResearch.WordTrace]
  refine ⟨229478719645097130000679883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152985813096731420000453255 229478719645097130000679883)
  ·
    refine ⟨344218079467645695001019825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229478719645097130000679883 344218079467645695001019825)
    ·
      refine ⟨258163559600734271250764869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344218079467645695001019825 258163559600734271250764869)
      ·
        refine ⟨48405667425137675859518413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 258163559600734271250764869 48405667425137675859518413)
        ·
          refine ⟨18152125284426628447319405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48405667425137675859518413 18152125284426628447319405)
          ·
            refine ⟨6807046981659985667744777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18152125284426628447319405 6807046981659985667744777)
            ·
              refine ⟨5105285236244989250808583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6807046981659985667744777 5105285236244989250808583)
              ·
                refine ⟨7657927854367483876212875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5105285236244989250808583 7657927854367483876212875)
                ·
                  refine ⟨11486891781551225814319313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7657927854367483876212875 11486891781551225814319313)
                  ·
                    refine ⟨8615168836163419360739485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11486891781551225814319313 8615168836163419360739485)
                    ·
                      refine ⟨3230688313561282260277307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8615168836163419360739485 3230688313561282260277307)
                      ·
                        rfl

theorem cell23_6291743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_6291743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291743 prefixEnd_6291743 := by exact prefixLift 6291743
  have htrace : WordTrace (prefixWord ++ tailWord_6291743) baseStart_6291743 baseEnd_6291743 := by
    simpa [prefixWord, tailWord_6291743, baseEnd_6291743] using wordTrace_append hprefix tailTrace_6291743
  have hstable : (prefixWord ++ tailWord_6291743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291743).length < 2 ^ (prefixWord ++ tailWord_6291743).sum := by decide
  have hdescent : baseEnd_6291743 < baseStart_6291743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291756 : List Nat := [2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 3]
def baseStart_6291756 : Nat := 118140960795 + 6291756 * 2 ^ 59
def prefixEnd_6291756 : Nat := 4983230072969 + 3 ^ 40 * 6291756 * 2
def baseEnd_6291756 : Nat := 3230694988809790709414747

theorem tailTrace_6291756 : CollatzResearch.WordTrace tailWord_6291756 prefixEnd_6291756 3230694988809790709414747 := by
  unfold tailWord_6291756
  simp only [CollatzResearch.WordTrace]
  refine ⟨114739596897025016610451561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152986129196033355480602081 114739596897025016610451561)
  ·
    refine ⟨86054697672768762457838671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114739596897025016610451561 86054697672768762457838671)
    ·
      refine ⟨129082046509153143686758007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86054697672768762457838671 129082046509153143686758007)
      ·
        refine ⟨193623069763729715530137011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129082046509153143686758007 193623069763729715530137011)
        ·
          refine ⟨290434604645594573295205517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193623069763729715530137011 290434604645594573295205517)
          ·
            refine ⟨108912976742097964985702069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 290434604645594573295205517 108912976742097964985702069)
            ·
              refine ⟨10210591569571684217409569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108912976742097964985702069 10210591569571684217409569)
              ·
                refine ⟨7657943677178763163057177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10210591569571684217409569 7657943677178763163057177)
                ·
                  refine ⟨5743457757884072372292883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7657943677178763163057177 5743457757884072372292883)
                  ·
                    refine ⟨8615186636826108558439325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5743457757884072372292883 8615186636826108558439325)
                    ·
                      refine ⟨3230694988809790709414747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8615186636826108558439325 3230694988809790709414747)
                      ·
                        rfl

theorem cell23_6291756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 3].length) (baseStart_6291756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291756 prefixEnd_6291756 := by exact prefixLift 6291756
  have htrace : WordTrace (prefixWord ++ tailWord_6291756) baseStart_6291756 baseEnd_6291756 := by
    simpa [prefixWord, tailWord_6291756, baseEnd_6291756] using wordTrace_append hprefix tailTrace_6291756
  have hstable : (prefixWord ++ tailWord_6291756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291756).length < 2 ^ (prefixWord ++ tailWord_6291756).sum := by decide
  have hdescent : baseEnd_6291756 < baseStart_6291756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291772 : List Nat := [2, 2, 2, 2, 1, 2, 1, 3, 2, 6]
def baseStart_6291772 : Nat := 118140960795 + 6291772 * 2 ^ 59
def prefixEnd_6291772 : Nat := 4983230072969 + 3 ^ 40 * 6291772 * 2
def baseEnd_6291772 : Nat := 1076901068166754215604891

theorem tailTrace_6291772 : CollatzResearch.WordTrace tailWord_6291772 prefixEnd_6291772 1076901068166754215604891 := by
  unfold tailWord_6291772
  simp only [CollatzResearch.WordTrace]
  refine ⟨114739888680996033976742785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152986518241328045302323713 114739888680996033976742785)
  ·
    refine ⟨86054916510747025482557089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114739888680996033976742785 86054916510747025482557089)
    ·
      refine ⟨64541187383060269111917817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86054916510747025482557089 64541187383060269111917817)
      ·
        refine ⟨48405890537295201833938363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64541187383060269111917817 48405890537295201833938363)
        ·
          refine ⟨72608835805942802750907545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48405890537295201833938363 72608835805942802750907545)
          ·
            refine ⟨54456626854457102063180659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72608835805942802750907545 54456626854457102063180659)
            ·
              refine ⟨81684940281685653094770989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54456626854457102063180659 81684940281685653094770989)
              ·
                refine ⟨30631852605632119910539121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81684940281685653094770989 30631852605632119910539121)
                ·
                  refine ⟨22973889454224089932904341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30631852605632119910539121 22973889454224089932904341)
                  ·
                    refine ⟨1076901068166754215604891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22973889454224089932904341 1076901068166754215604891)
                    ·
                      rfl

theorem cell23_6291772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_6291772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291772 prefixEnd_6291772 := by exact prefixLift 6291772
  have htrace : WordTrace (prefixWord ++ tailWord_6291772) baseStart_6291772 baseEnd_6291772 := by
    simpa [prefixWord, tailWord_6291772, baseEnd_6291772] using wordTrace_append hprefix tailTrace_6291772
  have hstable : (prefixWord ++ tailWord_6291772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291772).length < 2 ^ (prefixWord ++ tailWord_6291772).sum := by decide
  have hdescent : baseEnd_6291772 < baseStart_6291772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291812 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 1, 2, 7]
def baseStart_6291812 : Nat := 118140960795 + 6291812 * 2 ^ 59
def prefixEnd_6291812 : Nat := 4983230072969 + 3 ^ 40 * 6291812 * 2
def baseEnd_6291812 : Nat := 3230723743726442490314489

theorem tailTrace_6291812 : CollatzResearch.WordTrace tailWord_6291812 prefixEnd_6291812 3230723743726442490314489 := by
  unfold tailWord_6291812
  simp only [CollatzResearch.WordTrace]
  refine ⟨114740618140923577392470845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152987490854564769856627793 114740618140923577392470845)
  ·
    refine ⟨43027731802846341522176567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114740618140923577392470845 43027731802846341522176567)
    ·
      refine ⟨64541597704269512283264851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43027731802846341522176567 64541597704269512283264851)
      ·
        refine ⟨96812396556404268424897277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64541597704269512283264851 96812396556404268424897277)
        ·
          refine ⟨36304648708651600659336479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96812396556404268424897277 36304648708651600659336479)
          ·
            refine ⟨54456973062977400989004719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36304648708651600659336479 54456973062977400989004719)
            ·
              refine ⟨81685459594466101483507079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54456973062977400989004719 81685459594466101483507079)
              ·
                refine ⟨122528189391699152225260619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81685459594466101483507079 122528189391699152225260619)
                ·
                  refine ⟨183792284087548728337890929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122528189391699152225260619 183792284087548728337890929)
                  ·
                    refine ⟨137844213065661546253418197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 183792284087548728337890929 137844213065661546253418197)
                    ·
                      refine ⟨3230723743726442490314489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 137844213065661546253418197 3230723743726442490314489)
                      ·
                        rfl

theorem cell23_6291812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_6291812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291812 prefixEnd_6291812 := by exact prefixLift 6291812
  have htrace : WordTrace (prefixWord ++ tailWord_6291812) baseStart_6291812 baseEnd_6291812 := by
    simpa [prefixWord, tailWord_6291812, baseEnd_6291812] using wordTrace_append hprefix tailTrace_6291812
  have hstable : (prefixWord ++ tailWord_6291812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291812).length < 2 ^ (prefixWord ++ tailWord_6291812).sum := by decide
  have hdescent : baseEnd_6291812 < baseStart_6291812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291839 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 2, 5, 2]
def baseStart_6291839 : Nat := 118140960795 + 6291839 * 2 ^ 59
def prefixEnd_6291839 : Nat := 4983230072969 + 3 ^ 40 * 6291839 * 2
def baseEnd_6291839 : Nat := 3230737607704113884676865

theorem tailTrace_6291839 : CollatzResearch.WordTrace tailWord_6291839 prefixEnd_6291839 3230737607704113884676865 := by
  unfold tailWord_6291839
  simp only [CollatzResearch.WordTrace]
  refine ⟨229482221052749338396174571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152988147368499558930783047 229482221052749338396174571)
  ·
    refine ⟨344223331579124007594261857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229482221052749338396174571 344223331579124007594261857)
    ·
      refine ⟨258167498684343005695696393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344223331579124007594261857 258167498684343005695696393)
      ·
        refine ⟨193625624013257254271772295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258167498684343005695696393 193625624013257254271772295)
        ·
          refine ⟨290438436019885881407658443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193625624013257254271772295 290438436019885881407658443)
          ·
            refine ⟨435657654029828822111487665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290438436019885881407658443 435657654029828822111487665)
            ·
              refine ⟨326743240522371616583615749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435657654029828822111487665 326743240522371616583615749)
              ·
                refine ⟨61264357597944678109427953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 326743240522371616583615749 61264357597944678109427953)
                ·
                  refine ⟨45948268198458508582070965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61264357597944678109427953 45948268198458508582070965)
                  ·
                    refine ⟨4307650143605485179569153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45948268198458508582070965 4307650143605485179569153)
                    ·
                      refine ⟨3230737607704113884676865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4307650143605485179569153 3230737607704113884676865)
                      ·
                        rfl

theorem cell23_6291839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 5, 2].length) (baseStart_6291839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291839 prefixEnd_6291839 := by exact prefixLift 6291839
  have htrace : WordTrace (prefixWord ++ tailWord_6291839) baseStart_6291839 baseEnd_6291839 := by
    simpa [prefixWord, tailWord_6291839, baseEnd_6291839] using wordTrace_append hprefix tailTrace_6291839
  have hstable : (prefixWord ++ tailWord_6291839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291839).length < 2 ^ (prefixWord ++ tailWord_6291839).sum := by decide
  have hdescent : baseEnd_6291839 < baseStart_6291839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291849 : List Nat := [1, 2, 1, 1, 6, 1, 1, 3, 2, 5]
def baseStart_6291849 : Nat := 118140960795 + 6291849 * 2 ^ 59
def prefixEnd_6291849 : Nat := 4983230072969 + 3 ^ 40 * 6291849 * 2
def baseEnd_6291849 : Nat := 1076914247503552948517273

theorem tailTrace_6291849 : CollatzResearch.WordTrace tailWord_6291849 prefixEnd_6291849 1076914247503552948517273 := by
  unfold tailWord_6291849
  simp only [CollatzResearch.WordTrace]
  refine ⟨229482585782713110104038601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152988390521808740069359067 229482585782713110104038601)
  ·
    refine ⟨172111939337034832578028951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229482585782713110104038601 172111939337034832578028951)
    ·
      refine ⟨258167909005552248867043427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172111939337034832578028951 258167909005552248867043427)
      ·
        refine ⟨387251863508328373300565141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258167909005552248867043427 387251863508328373300565141)
        ·
          refine ⟨18152431101952892498463991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 387251863508328373300565141 18152431101952892498463991)
          ·
            refine ⟨27228646652929338747695987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18152431101952892498463991 27228646652929338747695987)
            ·
              refine ⟨40842969979394008121543981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27228646652929338747695987 40842969979394008121543981)
              ·
                refine ⟨15316113742272753045578993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40842969979394008121543981 15316113742272753045578993)
                ·
                  refine ⟨11487085306704564784184245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15316113742272753045578993 11487085306704564784184245)
                  ·
                    refine ⟨1076914247503552948517273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11487085306704564784184245 1076914247503552948517273)
                    ·
                      rfl

theorem cell23_6291849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 5].length) (baseStart_6291849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291849 prefixEnd_6291849 := by exact prefixLift 6291849
  have htrace : WordTrace (prefixWord ++ tailWord_6291849) baseStart_6291849 baseEnd_6291849 := by
    simpa [prefixWord, tailWord_6291849, baseEnd_6291849] using wordTrace_append hprefix tailTrace_6291849
  have hstable : (prefixWord ++ tailWord_6291849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291849).length < 2 ^ (prefixWord ++ tailWord_6291849).sum := by decide
  have hdescent : baseEnd_6291849 < baseStart_6291849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291870 : List Nat := [4, 3, 1, 2, 1, 1, 4, 2, 5]
def baseStart_6291870 : Nat := 118140960795 + 6291870 * 2 ^ 59
def prefixEnd_6291870 : Nat := 4983230072969 + 3 ^ 40 * 6291870 * 2
def baseEnd_6291870 : Nat := 358972613956044807043247

theorem tailTrace_6291870 : CollatzResearch.WordTrace tailWord_6291870 prefixEnd_6291870 358972613956044807043247 := by
  unfold tailWord_6291870
  simp only [CollatzResearch.WordTrace]
  refine ⟨28685418964454628836319133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152988901143758020460368709 28685418964454628836319133)
  ·
    refine ⟨10757032111670485813619675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28685418964454628836319133 10757032111670485813619675)
    ·
      refine ⟨16135548167505728720429513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10757032111670485813619675 16135548167505728720429513)
      ·
        refine ⟨12101661125629296540322135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16135548167505728720429513 12101661125629296540322135)
        ·
          refine ⟨18152491688443944810483203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12101661125629296540322135 18152491688443944810483203)
          ·
            refine ⟨27228737532665917215724805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18152491688443944810483203 27228737532665917215724805)
            ·
              refine ⟨5105388287374859477948401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27228737532665917215724805 5105388287374859477948401)
              ·
                refine ⟨3829041215531144608461301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5105388287374859477948401 3829041215531144608461301)
                ·
                  refine ⟨358972613956044807043247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3829041215531144608461301 358972613956044807043247)
                  ·
                    rfl

theorem cell23_6291870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_6291870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291870 prefixEnd_6291870 := by exact prefixLift 6291870
  have htrace : WordTrace (prefixWord ++ tailWord_6291870) baseStart_6291870 baseEnd_6291870 := by
    simpa [prefixWord, tailWord_6291870, baseEnd_6291870] using wordTrace_append hprefix tailTrace_6291870
  have hstable : (prefixWord ++ tailWord_6291870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291870).length < 2 ^ (prefixWord ++ tailWord_6291870).sum := by decide
  have hdescent : baseEnd_6291870 < baseStart_6291870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291926 : List Nat := [5, 2, 1, 1, 1, 1, 3, 1, 8]
def baseStart_6291926 : Nat := 118140960795 + 6291926 * 2 ^ 59
def prefixEnd_6291926 : Nat := 4983230072969 + 3 ^ 40 * 6291926 * 2
def baseEnd_6291926 : Nat := 358975808946783893809885

theorem tailTrace_6291926 : CollatzResearch.WordTrace tailWord_6291926 prefixEnd_6291926 358975808946783893809885 := by
  unfold tailWord_6291926
  simp only [CollatzResearch.WordTrace]
  refine ⟨14342837137714634515911977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152990262802289434836394421 14342837137714634515911977)
  ·
    refine ⟨10757127853285975886933983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14342837137714634515911977 10757127853285975886933983)
    ·
      refine ⟨16135691779928963830400975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10757127853285975886933983 16135691779928963830400975)
      ·
        refine ⟨24203537669893445745601463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16135691779928963830400975 24203537669893445745601463)
        ·
          refine ⟨36305306504840168618402195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24203537669893445745601463 36305306504840168618402195)
          ·
            refine ⟨54457959757260252927603293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36305306504840168618402195 54457959757260252927603293)
            ·
              refine ⟨20421734908972594847851235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54457959757260252927603293 20421734908972594847851235)
              ·
                refine ⟨30632602363458892271776853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20421734908972594847851235 30632602363458892271776853)
                ·
                  refine ⟨358975808946783893809885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30632602363458892271776853 358975808946783893809885)
                  ·
                    rfl

theorem cell23_6291926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_6291926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291926 prefixEnd_6291926 := by exact prefixLift 6291926
  have htrace : WordTrace (prefixWord ++ tailWord_6291926) baseStart_6291926 baseEnd_6291926 := by
    simpa [prefixWord, tailWord_6291926, baseEnd_6291926] using wordTrace_append hprefix tailTrace_6291926
  have hstable : (prefixWord ++ tailWord_6291926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291926).length < 2 ^ (prefixWord ++ tailWord_6291926).sum := by decide
  have hdescent : baseEnd_6291926 < baseStart_6291926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291959 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 4]
def baseStart_6291959 : Nat := 118140960795 + 6291959 * 2 ^ 59
def prefixEnd_6291959 : Nat := 4983230072969 + 3 ^ 40 * 6291959 * 2
def baseEnd_6291959 : Nat := 3230799225382653415176313

theorem tailTrace_6291959 : CollatzResearch.WordTrace tailWord_6291959 prefixEnd_6291959 3230799225382653415176313 := by
  unfold tailWord_6291959
  simp only [CollatzResearch.WordTrace]
  refine ⟨229486597812314598890542931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152991065208209732593695287 229486597812314598890542931)
  ·
    refine ⟨344229896718471898335814397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229486597812314598890542931 344229896718471898335814397)
    ·
      refine ⟨129086211269426961875930399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344229896718471898335814397 129086211269426961875930399)
      ·
        refine ⟨193629316904140442813895599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129086211269426961875930399 193629316904140442813895599)
        ·
          refine ⟨290443975356210664220843399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193629316904140442813895599 290443975356210664220843399)
          ·
            refine ⟨435665963034315996331265099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290443975356210664220843399 435665963034315996331265099)
            ·
              refine ⟨653498944551473994496897649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 435665963034315996331265099 653498944551473994496897649)
              ·
                refine ⟨490124208413605495872673237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 653498944551473994496897649 490124208413605495872673237)
                ·
                  refine ⟨11487286134693878809515779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 490124208413605495872673237 11487286134693878809515779)
                  ·
                    refine ⟨17230929202040818214273669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11487286134693878809515779 17230929202040818214273669)
                    ·
                      refine ⟨3230799225382653415176313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17230929202040818214273669 3230799225382653415176313)
                      ·
                        rfl

theorem cell23_6291959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_6291959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291959 prefixEnd_6291959 := by exact prefixLift 6291959
  have htrace : WordTrace (prefixWord ++ tailWord_6291959) baseStart_6291959 baseEnd_6291959 := by
    simpa [prefixWord, tailWord_6291959, baseEnd_6291959] using wordTrace_append hprefix tailTrace_6291959
  have hstable : (prefixWord ++ tailWord_6291959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291959).length < 2 ^ (prefixWord ++ tailWord_6291959).sum := by decide
  have hdescent : baseEnd_6291959 < baseStart_6291959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291989 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 3, 1, 6]
def baseStart_6291989 : Nat := 118140960795 + 6291989 * 2 ^ 59
def prefixEnd_6291989 : Nat := 4983230072969 + 3 ^ 40 * 6291989 * 2
def baseEnd_6291989 : Nat := 3230814629802288297801175

theorem tailTrace_6291989 : CollatzResearch.WordTrace tailWord_6291989 prefixEnd_6291989 3230814629802288297801175 := by
  unfold tailWord_6291989
  simp only [CollatzResearch.WordTrace]
  refine ⟨229487692002205914014135021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152991794668137276009423347 229487692002205914014135021)
  ·
    refine ⟨86057884500827217755300633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229487692002205914014135021 86057884500827217755300633)
    ·
      refine ⟨64543413375620413316475475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86057884500827217755300633 64543413375620413316475475)
      ·
        refine ⟨96815120063430619974713213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64543413375620413316475475 96815120063430619974713213)
        ·
          refine ⟨36305670023786482490517455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96815120063430619974713213 36305670023786482490517455)
          ·
            refine ⟨54458505035679723735776183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36305670023786482490517455 54458505035679723735776183)
            ·
              refine ⟨81687757553519585603664275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54458505035679723735776183 81687757553519585603664275)
              ·
                refine ⟨122531636330279378405496413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81687757553519585603664275 122531636330279378405496413)
                ·
                  refine ⟨45949363623854766902061155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122531636330279378405496413 45949363623854766902061155)
                  ·
                    refine ⟨68924045435782150353091733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45949363623854766902061155 68924045435782150353091733)
                    ·
                      refine ⟨3230814629802288297801175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68924045435782150353091733 3230814629802288297801175)
                      ·
                        rfl

theorem cell23_6291989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_6291989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291989 prefixEnd_6291989 := by exact prefixLift 6291989
  have htrace : WordTrace (prefixWord ++ tailWord_6291989) baseStart_6291989 baseEnd_6291989 := by
    simpa [prefixWord, tailWord_6291989, baseEnd_6291989] using wordTrace_append hprefix tailTrace_6291989
  have hstable : (prefixWord ++ tailWord_6291989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291989).length < 2 ^ (prefixWord ++ tailWord_6291989).sum := by decide
  have hdescent : baseEnd_6291989 < baseStart_6291989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6291996 : List Nat := [2, 2, 3, 1, 2, 2, 2, 2, 1, 1, 5]
def baseStart_6291996 : Nat := 118140960795 + 6291996 * 2 ^ 59
def prefixEnd_6291996 : Nat := 4983230072969 + 3 ^ 40 * 6291996 * 2
def baseEnd_6291996 : Nat := 3230818224166869770413643

theorem tailTrace_6291996 : CollatzResearch.WordTrace tailWord_6291996 prefixEnd_6291996 3230818224166869770413643 := by
  unfold tailWord_6291996
  simp only [CollatzResearch.WordTrace]
  refine ⟨114743973656590277104819921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152991964875453702806426561 114743973656590277104819921)
  ·
    refine ⟨86057980242442707828614941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114743973656590277104819921 86057980242442707828614941)
    ·
      refine ⟨32271742590916015435730603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86057980242442707828614941 32271742590916015435730603)
      ·
        refine ⟨48407613886374023153595905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32271742590916015435730603 48407613886374023153595905)
        ·
          refine ⟨36305710414780517365196929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48407613886374023153595905 36305710414780517365196929)
          ·
            refine ⟨27229282811085388023897697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36305710414780517365196929 27229282811085388023897697)
            ·
              refine ⟨20421962108314041017923273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27229282811085388023897697 20421962108314041017923273)
              ·
                refine ⟨15316471581235530763442455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20421962108314041017923273 15316471581235530763442455)
                ·
                  refine ⟨22974707371853296145163683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15316471581235530763442455 22974707371853296145163683)
                  ·
                    refine ⟨34462061057779944217745525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22974707371853296145163683 34462061057779944217745525)
                    ·
                      refine ⟨3230818224166869770413643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34462061057779944217745525 3230818224166869770413643)
                      ·
                        rfl

theorem cell23_6291996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_6291996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6291996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6291996 prefixEnd_6291996 := by exact prefixLift 6291996
  have htrace : WordTrace (prefixWord ++ tailWord_6291996) baseStart_6291996 baseEnd_6291996 := by
    simpa [prefixWord, tailWord_6291996, baseEnd_6291996] using wordTrace_append hprefix tailTrace_6291996
  have hstable : (prefixWord ++ tailWord_6291996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6291996).length < 2 ^ (prefixWord ++ tailWord_6291996).sum := by decide
  have hdescent : baseEnd_6291996 < baseStart_6291996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6291996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292003 : List Nat := [1, 1, 1, 4, 4, 2, 1, 3, 2, 4]
def baseStart_6292003 : Nat := 118140960795 + 6292003 * 2 ^ 59
def prefixEnd_6292003 : Nat := 4983230072969 + 3 ^ 40 * 6292003 * 2
def baseEnd_6292003 : Nat := 1076940606177150414342037

theorem tailTrace_6292003 : CollatzResearch.WordTrace tailWord_6292003 prefixEnd_6292003 1076940606177150414342037 := by
  unfold tailWord_6292003
  simp only [CollatzResearch.WordTrace]
  refine ⟨229488202624155194405144663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152992135082770129603429775 229488202624155194405144663)
  ·
    refine ⟨344232303936232791607716995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229488202624155194405144663 344232303936232791607716995)
    ·
      refine ⟨516348455904349187411575493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344232303936232791607716995 516348455904349187411575493)
      ·
        refine ⟨96815335482065472639670405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 516348455904349187411575493 96815335482065472639670405)
        ·
          refine ⟨18152875402887276119938201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96815335482065472639670405 18152875402887276119938201)
          ·
            refine ⟨13614656552165457089953651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18152875402887276119938201 13614656552165457089953651)
            ·
              refine ⟨20421984828248185634930477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13614656552165457089953651 20421984828248185634930477)
              ·
                refine ⟨7658244310593069613098929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20421984828248185634930477 7658244310593069613098929)
                ·
                  refine ⟨5743683232944802209824197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7658244310593069613098929 5743683232944802209824197)
                  ·
                    refine ⟨1076940606177150414342037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5743683232944802209824197 1076940606177150414342037)
                    ·
                      rfl

theorem cell23_6292003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 2, 4].length) (baseStart_6292003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292003 prefixEnd_6292003 := by exact prefixLift 6292003
  have htrace : WordTrace (prefixWord ++ tailWord_6292003) baseStart_6292003 baseEnd_6292003 := by
    simpa [prefixWord, tailWord_6292003, baseEnd_6292003] using wordTrace_append hprefix tailTrace_6292003
  have hstable : (prefixWord ++ tailWord_6292003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292003).length < 2 ^ (prefixWord ++ tailWord_6292003).sum := by decide
  have hdescent : baseEnd_6292003 < baseStart_6292003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292007 : List Nat := [1, 1, 7, 2, 1, 2, 1, 2, 1, 5]
def baseStart_6292007 : Nat := 118140960795 + 6292007 * 2 ^ 59
def prefixEnd_6292007 : Nat := 4983230072969 + 3 ^ 40 * 6292007 * 2
def baseEnd_6292007 : Nat := 1076941290818023075792031

theorem tailTrace_6292007 : CollatzResearch.WordTrace tailWord_6292007 prefixEnd_6292007 1076941290818023075792031 := by
  unfold tailWord_6292007
  simp only [CollatzResearch.WordTrace]
  refine ⟨229488348516140703088290275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152992232344093802058860183 229488348516140703088290275)
  ·
    refine ⟨344232522774211054632435413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229488348516140703088290275 344232522774211054632435413)
    ·
      refine ⟨8067949752520571592947705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 344232522774211054632435413 8067949752520571592947705)
      ·
        refine ⟨6050962314390428694710779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8067949752520571592947705 6050962314390428694710779)
        ·
          refine ⟨9076443471585643042066169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6050962314390428694710779 9076443471585643042066169)
          ·
            refine ⟨6807332603689232281549627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9076443471585643042066169 6807332603689232281549627)
            ·
              refine ⟨10210998905533848422324441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6807332603689232281549627 10210998905533848422324441)
              ·
                refine ⟨7658249179150386316743331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10210998905533848422324441 7658249179150386316743331)
                ·
                  refine ⟨11487373768725579475114997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7658249179150386316743331 11487373768725579475114997)
                  ·
                    refine ⟨1076941290818023075792031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11487373768725579475114997 1076941290818023075792031)
                    ·
                      rfl

theorem cell23_6292007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_6292007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292007 prefixEnd_6292007 := by exact prefixLift 6292007
  have htrace : WordTrace (prefixWord ++ tailWord_6292007) baseStart_6292007 baseEnd_6292007 := by
    simpa [prefixWord, tailWord_6292007, baseEnd_6292007] using wordTrace_append hprefix tailTrace_6292007
  have hstable : (prefixWord ++ tailWord_6292007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292007).length < 2 ^ (prefixWord ++ tailWord_6292007).sum := by decide
  have hdescent : baseEnd_6292007 < baseStart_6292007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292010 : List Nat := [3, 1, 4, 1, 1, 4, 1, 2, 1, 1, 4]
def baseStart_6292010 : Nat := 118140960795 + 6292010 * 2 ^ 59
def prefixEnd_6292010 : Nat := 4983230072969 + 3 ^ 40 * 6292010 * 2
def baseEnd_6292010 : Nat := 3230825412896032715638579

theorem tailTrace_6292010 : CollatzResearch.WordTrace tailWord_6292010 prefixEnd_6292010 3230825412896032715638579 := by
  unfold tailWord_6292010
  simp only [CollatzResearch.WordTrace]
  refine ⟨57372114483782458650162371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152992305290086556400432989 57372114483782458650162371)
  ·
    refine ⟨86058171725673687975243557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57372114483782458650162371 86058171725673687975243557)
    ·
      refine ⟨16135907198563816495358167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86058171725673687975243557 16135907198563816495358167)
      ·
        refine ⟨24203860797845724743037251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16135907198563816495358167 24203860797845724743037251)
        ·
          refine ⟨36305791196768587114555877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24203860797845724743037251 36305791196768587114555877)
          ·
            refine ⟨6807335849394110083979227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36305791196768587114555877 6807335849394110083979227)
            ·
              refine ⟨10211003774091165125968841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6807335849394110083979227 10211003774091165125968841)
              ·
                refine ⟨7658252830568373844476631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10211003774091165125968841 7658252830568373844476631)
                ·
                  refine ⟨11487379245852560766714947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7658252830568373844476631 11487379245852560766714947)
                  ·
                    refine ⟨17231068868778841150072421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11487379245852560766714947 17231068868778841150072421)
                    ·
                      refine ⟨3230825412896032715638579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17231068868778841150072421 3230825412896032715638579)
                      ·
                        rfl

theorem cell23_6292010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_6292010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292010 prefixEnd_6292010 := by exact prefixLift 6292010
  have htrace : WordTrace (prefixWord ++ tailWord_6292010) baseStart_6292010 baseEnd_6292010 := by
    simpa [prefixWord, tailWord_6292010, baseEnd_6292010] using wordTrace_append hprefix tailTrace_6292010
  have hstable : (prefixWord ++ tailWord_6292010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292010).length < 2 ^ (prefixWord ++ tailWord_6292010).sum := by decide
  have hdescent : baseEnd_6292010 < baseStart_6292010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292020 : List Nat := [2, 5, 1, 3, 1, 1, 1, 2, 1, 6]
def baseStart_6292020 : Nat := 118140960795 + 6292020 * 2 ^ 59
def prefixEnd_6292020 : Nat := 4983230072969 + 3 ^ 40 * 6292020 * 2
def baseEnd_6292020 : Nat := 1076943515900859225504511

theorem tailTrace_6292020 : CollatzResearch.WordTrace tailWord_6292020 prefixEnd_6292020 1076943515900859225504511 := by
  unfold tailWord_6292020
  simp only [CollatzResearch.WordTrace]
  refine ⟨114744411332546803154256757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152992548443395737539009009 114744411332546803154256757)
  ·
    refine ⟨10757288562426262795711571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114744411332546803154256757 10757288562426262795711571)
    ·
      refine ⟨16135932843639394193567357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10757288562426262795711571 16135932843639394193567357)
      ·
        refine ⟨6050974816364772822587759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16135932843639394193567357 6050974816364772822587759)
        ·
          refine ⟨9076462224547159233881639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6050974816364772822587759 9076462224547159233881639)
          ·
            refine ⟨13614693336820738850822459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9076462224547159233881639 13614693336820738850822459)
            ·
              refine ⟨20422040005231108276233689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13614693336820738850822459 20422040005231108276233689)
              ·
                refine ⟨15316530003923331207175267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20422040005231108276233689 15316530003923331207175267)
                ·
                  refine ⟨22974795005884996810762901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15316530003923331207175267 22974795005884996810762901)
                  ·
                    refine ⟨1076943515900859225504511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22974795005884996810762901 1076943515900859225504511)
                    ·
                      rfl

theorem cell23_6292020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_6292020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292020 prefixEnd_6292020 := by exact prefixLift 6292020
  have htrace : WordTrace (prefixWord ++ tailWord_6292020) baseStart_6292020 baseEnd_6292020 := by
    simpa [prefixWord, tailWord_6292020, baseEnd_6292020] using wordTrace_append hprefix tailTrace_6292020
  have hstable : (prefixWord ++ tailWord_6292020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292020).length < 2 ^ (prefixWord ++ tailWord_6292020).sum := by decide
  have hdescent : baseEnd_6292020 < baseStart_6292020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292026 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 3, 3, 3]
def baseStart_6292026 : Nat := 118140960795 + 6292026 * 2 ^ 59
def prefixEnd_6292026 : Nat := 4983230072969 + 3 ^ 40 * 6292026 * 2
def baseEnd_6292026 : Nat := 3230833628586504653038505

theorem tailTrace_6292026 : CollatzResearch.WordTrace tailWord_6292026 prefixEnd_6292026 3230833628586504653038505 := by
  unfold tailWord_6292026
  simp only [CollatzResearch.WordTrace]
  refine ⟨57372260375767967333307983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152992694335381246222154621 57372260375767967333307983)
  ·
    refine ⟨86058390563651950999961975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57372260375767967333307983 86058390563651950999961975)
    ·
      refine ⟨129087585845477926499942963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86058390563651950999961975 129087585845477926499942963)
      ·
        refine ⟨193631378768216889749914445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129087585845477926499942963 193631378768216889749914445)
        ·
          refine ⟨72611767038081333656217917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193631378768216889749914445 72611767038081333656217917)
          ·
            refine ⟨27229412639280500121081719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72611767038081333656217917 27229412639280500121081719)
            ·
              refine ⟨40844118958920750181622579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27229412639280500121081719 40844118958920750181622579)
              ·
                refine ⟨61266178438381125272433869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40844118958920750181622579 61266178438381125272433869)
                ·
                  refine ⟨22974816914392921977162701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61266178438381125272433869 22974816914392921977162701)
                  ·
                    refine ⟨8615556342897345741436013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22974816914392921977162701 8615556342897345741436013)
                    ·
                      refine ⟨3230833628586504653038505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8615556342897345741436013 3230833628586504653038505)
                      ·
                        rfl

theorem cell23_6292026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 3, 3, 3].length) (baseStart_6292026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292026 prefixEnd_6292026 := by exact prefixLift 6292026
  have htrace : WordTrace (prefixWord ++ tailWord_6292026) baseStart_6292026 baseEnd_6292026 := by
    simpa [prefixWord, tailWord_6292026, baseEnd_6292026] using wordTrace_append hprefix tailTrace_6292026
  have hstable : (prefixWord ++ tailWord_6292026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292026).length < 2 ^ (prefixWord ++ tailWord_6292026).sum := by decide
  have hdescent : baseEnd_6292026 < baseStart_6292026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292043 : List Nat := [1, 1, 1, 1, 3, 1, 5, 4, 2, 1, 3]
def baseStart_6292043 : Nat := 118140960795 + 6292043 * 2 ^ 59
def prefixEnd_6292043 : Nat := 4983230072969 + 3 ^ 40 * 6292043 * 2
def baseEnd_6292043 : Nat := 3230842357757631086525927

theorem tailTrace_6292043 : CollatzResearch.WordTrace tailWord_6292043 prefixEnd_6292043 3230842357757631086525927 := by
  unfold tailWord_6292043
  simp only [CollatzResearch.WordTrace]
  refine ⟨229489661544010281236600783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152993107696006854157733855 229489661544010281236600783)
  ·
    refine ⟨344234492316015421854901175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229489661544010281236600783 344234492316015421854901175)
    ·
      refine ⟨516351738474023132782351763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344234492316015421854901175 516351738474023132782351763)
      ·
        refine ⟨774527607711034699173527645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516351738474023132782351763 774527607711034699173527645)
        ·
          refine ⟨290447852891638012190072867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 774527607711034699173527645 290447852891638012190072867)
          ·
            refine ⟨435671779337457018285109301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290447852891638012190072867 435671779337457018285109301)
            ·
              refine ⟨40844229312886595464228997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 435671779337457018285109301 40844229312886595464228997)
              ·
                refine ⟨7658292996166236649542937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40844229312886595464228997 7658292996166236649542937)
                ·
                  refine ⟨5743719747124677487157203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7658292996166236649542937 5743719747124677487157203)
                  ·
                    refine ⟨8615579620687016230735805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5743719747124677487157203 8615579620687016230735805)
                    ·
                      refine ⟨3230842357757631086525927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8615579620687016230735805 3230842357757631086525927)
                      ·
                        rfl

theorem cell23_6292043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2, 1, 3].length) (baseStart_6292043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292043 prefixEnd_6292043 := by exact prefixLift 6292043
  have htrace : WordTrace (prefixWord ++ tailWord_6292043) baseStart_6292043 baseEnd_6292043 := by
    simpa [prefixWord, tailWord_6292043, baseEnd_6292043] using wordTrace_append hprefix tailTrace_6292043
  have hstable : (prefixWord ++ tailWord_6292043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292043).length < 2 ^ (prefixWord ++ tailWord_6292043).sum := by decide
  have hdescent : baseEnd_6292043 < baseStart_6292043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292053 : List Nat := [1, 3, 2, 2, 1, 1, 3, 2, 3, 3, 2]
def baseStart_6292053 : Nat := 118140960795 + 6292053 * 2 ^ 59
def prefixEnd_6292053 : Nat := 4983230072969 + 3 ^ 40 * 6292053 * 2
def baseEnd_6292053 : Nat := 3230847492564176047400881

theorem tailTrace_6292053 : CollatzResearch.WordTrace tailWord_6292053 prefixEnd_6292053 3230847492564176047400881 := by
  unfold tailWord_6292053
  simp only [CollatzResearch.WordTrace]
  refine ⟨229490026273974052944464813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152993350849316035296309875 229490026273974052944464813)
  ·
    refine ⟨86058759852740269854174305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229490026273974052944464813 86058759852740269854174305)
    ·
      refine ⟨64544069889555202390630729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86058759852740269854174305 64544069889555202390630729)
      ·
        refine ⟨48408052417166401792973047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64544069889555202390630729 48408052417166401792973047)
        ·
          refine ⟨72612078625749602689459571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48408052417166401792973047 72612078625749602689459571)
          ·
            refine ⟨108918117938624404034189357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72612078625749602689459571 108918117938624404034189357)
            ·
              refine ⟨40844294226984151512821009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108918117938624404034189357 40844294226984151512821009)
              ·
                refine ⟨30633220670238113634615757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40844294226984151512821009 30633220670238113634615757)
                ·
                  refine ⟨11487457751339292612980909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30633220670238113634615757 11487457751339292612980909)
                  ·
                    refine ⟨4307796656752234729867841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11487457751339292612980909 4307796656752234729867841)
                    ·
                      refine ⟨3230847492564176047400881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4307796656752234729867841 3230847492564176047400881)
                      ·
                        rfl

theorem cell23_6292053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_6292053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292053 prefixEnd_6292053 := by exact prefixLift 6292053
  have htrace : WordTrace (prefixWord ++ tailWord_6292053) baseStart_6292053 baseEnd_6292053 := by
    simpa [prefixWord, tailWord_6292053, baseEnd_6292053] using wordTrace_append hprefix tailTrace_6292053
  have hstable : (prefixWord ++ tailWord_6292053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292053).length < 2 ^ (prefixWord ++ tailWord_6292053).sum := by decide
  have hdescent : baseEnd_6292053 < baseStart_6292053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292060 : List Nat := [2, 2, 4, 1, 3, 1, 2, 1, 1, 3, 3]
def baseStart_6292060 : Nat := 118140960795 + 6292060 * 2 ^ 59
def prefixEnd_6292060 : Nat := 4983230072969 + 3 ^ 40 * 6292060 * 2
def baseEnd_6292060 : Nat := 3230851086928757520013349

theorem tailTrace_6292060 : CollatzResearch.WordTrace tailWord_6292060 prefixEnd_6292060 3230851086928757520013349 := by
  unfold tailWord_6292060
  simp only [CollatzResearch.WordTrace]
  refine ⟨114745140792474346569984817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152993521056632462093313089 114745140792474346569984817)
  ·
    refine ⟨86058855594355759927488613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114745140792474346569984817 86058855594355759927488613)
    ·
      refine ⟨16136035423941704986404115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86058855594355759927488613 16136035423941704986404115)
      ·
        refine ⟨24204053135912557479606173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16136035423941704986404115 24204053135912557479606173)
        ·
          refine ⟨9076519925967209054852315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24204053135912557479606173 9076519925967209054852315)
          ·
            refine ⟨13614779888950813582278473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9076519925967209054852315 13614779888950813582278473)
            ·
              refine ⟨10211084916713110186708855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13614779888950813582278473 10211084916713110186708855)
              ·
                refine ⟨15316627375069665280063283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10211084916713110186708855 15316627375069665280063283)
                ·
                  refine ⟨22974941062604497920094925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15316627375069665280063283 22974941062604497920094925)
                  ·
                    refine ⟨8615602898476686720035597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22974941062604497920094925 8615602898476686720035597)
                    ·
                      refine ⟨3230851086928757520013349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8615602898476686720035597 3230851086928757520013349)
                      ·
                        rfl

theorem cell23_6292060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_6292060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292060 prefixEnd_6292060 := by exact prefixLift 6292060
  have htrace : WordTrace (prefixWord ++ tailWord_6292060) baseStart_6292060 baseEnd_6292060 := by
    simpa [prefixWord, tailWord_6292060, baseEnd_6292060] using wordTrace_append hprefix tailTrace_6292060
  have hstable : (prefixWord ++ tailWord_6292060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292060).length < 2 ^ (prefixWord ++ tailWord_6292060).sum := by decide
  have hdescent : baseEnd_6292060 < baseStart_6292060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292096 : List Nat := [2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 4]
def baseStart_6292096 : Nat := 118140960795 + 6292096 * 2 ^ 59
def prefixEnd_6292096 : Nat := 4983230072969 + 3 ^ 40 * 6292096 * 2
def baseEnd_6292096 : Nat := 3230869572232319379163183

theorem tailTrace_6292096 : CollatzResearch.WordTrace tailWord_6292096 prefixEnd_6292096 3230869572232319379163183 := by
  unfold tailWord_6292096
  simp only [CollatzResearch.WordTrace]
  refine ⟨114745797306409135644140071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152994396408545514192186761 114745797306409135644140071)
  ·
    refine ⟨172118695959613703466210107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114745797306409135644140071 172118695959613703466210107)
    ·
      refine ⟨258178043939420555199315161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172118695959613703466210107 258178043939420555199315161)
      ·
        refine ⟨193633532954565416399486371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258178043939420555199315161 193633532954565416399486371)
        ·
          refine ⟨290450299431848124599229557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193633532954565416399486371 290450299431848124599229557)
          ·
            refine ⟨27229715571735761681177771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 290450299431848124599229557 27229715571735761681177771)
            ·
              refine ⟨40844573357603642521766657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27229715571735761681177771 40844573357603642521766657)
              ·
                refine ⟨30633430018202731891324993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40844573357603642521766657 30633430018202731891324993)
                ·
                  refine ⟨22975072513652048918493745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30633430018202731891324993 22975072513652048918493745)
                  ·
                    refine ⟨17231304385239036688870309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22975072513652048918493745 17231304385239036688870309)
                    ·
                      refine ⟨3230869572232319379163183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17231304385239036688870309 3230869572232319379163183)
                      ·
                        rfl

theorem cell23_6292096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_6292096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292096 prefixEnd_6292096 := by exact prefixLift 6292096
  have htrace : WordTrace (prefixWord ++ tailWord_6292096) baseStart_6292096 baseEnd_6292096 := by
    simpa [prefixWord, tailWord_6292096, baseEnd_6292096] using wordTrace_append hprefix tailTrace_6292096
  have hstable : (prefixWord ++ tailWord_6292096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292096).length < 2 ^ (prefixWord ++ tailWord_6292096).sum := by decide
  have hdescent : baseEnd_6292096 < baseStart_6292096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292146 : List Nat := [3, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5]
def baseStart_6292146 : Nat := 118140960795 + 6292146 * 2 ^ 59
def prefixEnd_6292146 : Nat := 4983230072969 + 3 ^ 40 * 6292146 * 2
def baseEnd_6292146 : Nat := 3230895246265044183537953

theorem tailTrace_6292146 : CollatzResearch.WordTrace tailWord_6292146 prefixEnd_6292146 3230895246265044183537953 := by
  unfold tailWord_6292146
  simp only [CollatzResearch.WordTrace]
  refine ⟨57373354565659282456900073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152995612175091419885066861 57373354565659282456900073)
  ·
    refine ⟨43030015924244461842675055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57373354565659282456900073 43030015924244461842675055)
    ·
      refine ⟨64545023886366692764012583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43030015924244461842675055 64545023886366692764012583)
      ·
        refine ⟨96817535829550039146018875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64545023886366692764012583 96817535829550039146018875)
        ·
          refine ⟨145226303744325058719028313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96817535829550039146018875 145226303744325058719028313)
          ·
            refine ⟨108919727808243794039271235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145226303744325058719028313 108919727808243794039271235)
            ·
              refine ⟨163379591712365691058906853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108919727808243794039271235 163379591712365691058906853)
              ·
                refine ⟨30633673446068567073545035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163379591712365691058906853 30633673446068567073545035)
                ·
                  refine ⟨45950510169102850610317553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30633673446068567073545035 45950510169102850610317553)
                  ·
                    refine ⟨34462882626827137957738165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45950510169102850610317553 34462882626827137957738165)
                    ·
                      refine ⟨3230895246265044183537953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34462882626827137957738165 3230895246265044183537953)
                      ·
                        rfl

theorem cell23_6292146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_6292146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292146 prefixEnd_6292146 := by exact prefixLift 6292146
  have htrace : WordTrace (prefixWord ++ tailWord_6292146) baseStart_6292146 baseEnd_6292146 := by
    simpa [prefixWord, tailWord_6292146, baseEnd_6292146] using wordTrace_append hprefix tailTrace_6292146
  have hstable : (prefixWord ++ tailWord_6292146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292146).length < 2 ^ (prefixWord ++ tailWord_6292146).sum := by decide
  have hdescent : baseEnd_6292146 < baseStart_6292146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292210 : List Nat := [3, 2, 1, 3, 1, 2, 2, 2, 2, 2, 3]
def baseStart_6292210 : Nat := 118140960795 + 6292210 * 2 ^ 59
def prefixEnd_6292210 : Nat := 4983230072969 + 3 ^ 40 * 6292210 * 2
def baseEnd_6292210 : Nat := 3230928109026931933137659

theorem tailTrace_6292210 : CollatzResearch.WordTrace tailWord_6292210 prefixEnd_6292210 3230928109026931933137659 := by
  unfold tailWord_6292210
  simp only [CollatzResearch.WordTrace]
  refine ⟨57373938133601317189482521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152997168356270179171953389 57373938133601317189482521)
  ·
    refine ⟨43030453600200987892111891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57373938133601317189482521 43030453600200987892111891)
    ·
      refine ⟨64545680400301481838167837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43030453600200987892111891 64545680400301481838167837)
      ·
        refine ⟨24204630150113055689312939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64545680400301481838167837 24204630150113055689312939)
        ·
          refine ⟨36306945225169583533969409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24204630150113055689312939 36306945225169583533969409)
          ·
            refine ⟨27230208918877187650477057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36306945225169583533969409 27230208918877187650477057)
            ·
              refine ⟨20422656689157890737857793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27230208918877187650477057 20422656689157890737857793)
              ·
                refine ⟨15316992516868418053393345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20422656689157890737857793 15316992516868418053393345)
                ·
                  refine ⟨11487744387651313540045009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15316992516868418053393345 11487744387651313540045009)
                  ·
                    refine ⟨8615808290738485155033757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11487744387651313540045009 8615808290738485155033757)
                    ·
                      refine ⟨3230928109026931933137659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8615808290738485155033757 3230928109026931933137659)
                      ·
                        rfl

theorem cell23_6292210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_6292210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292210 prefixEnd_6292210 := by exact prefixLift 6292210
  have htrace : WordTrace (prefixWord ++ tailWord_6292210) baseStart_6292210 baseEnd_6292210 := by
    simpa [prefixWord, tailWord_6292210, baseEnd_6292210] using wordTrace_append hprefix tailTrace_6292210
  have hstable : (prefixWord ++ tailWord_6292210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292210).length < 2 ^ (prefixWord ++ tailWord_6292210).sum := by decide
  have hdescent : baseEnd_6292210 < baseStart_6292210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292216 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 1, 2, 6]
def baseStart_6292216 : Nat := 118140960795 + 6292216 * 2 ^ 59
def prefixEnd_6292216 : Nat := 4983230072969 + 3 ^ 40 * 6292216 * 2
def baseEnd_6292216 : Nat := 3230931189910858909662631

theorem tailTrace_6292216 : CollatzResearch.WordTrace tailWord_6292216 prefixEnd_6292216 3230931189910858909662631 := by
  unfold tailWord_6292216
  simp only [CollatzResearch.WordTrace]
  refine ⟨114747985686191765891324251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152997314248255687855099001 114747985686191765891324251)
  ·
    refine ⟨172121978529287648836986377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114747985686191765891324251 172121978529287648836986377)
    ·
      refine ⟨129091483896965736627739783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172121978529287648836986377 129091483896965736627739783)
      ·
        refine ⟨193637225845448604941609675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129091483896965736627739783 193637225845448604941609675)
        ·
          refine ⟨290455838768172907412414513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193637225845448604941609675 290455838768172907412414513)
          ·
            refine ⟨217841879076129680559310885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290455838768172907412414513 217841879076129680559310885)
            ·
              refine ⟨40845352326774315104870791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 217841879076129680559310885 40845352326774315104870791)
              ·
                refine ⟨61268028490161472657306187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40845352326774315104870791 61268028490161472657306187)
                ·
                  refine ⟨91902042735242208985959281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61268028490161472657306187 91902042735242208985959281)
                  ·
                    refine ⟨68926532051431656739469461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91902042735242208985959281 68926532051431656739469461)
                    ·
                      refine ⟨3230931189910858909662631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68926532051431656739469461 3230931189910858909662631)
                      ·
                        rfl

theorem cell23_6292216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_6292216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292216 prefixEnd_6292216 := by exact prefixLift 6292216
  have htrace : WordTrace (prefixWord ++ tailWord_6292216) baseStart_6292216 baseEnd_6292216 := by
    simpa [prefixWord, tailWord_6292216, baseEnd_6292216] using wordTrace_append hprefix tailTrace_6292216
  have hstable : (prefixWord ++ tailWord_6292216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292216).length < 2 ^ (prefixWord ++ tailWord_6292216).sum := by decide
  have hdescent : baseEnd_6292216 < baseStart_6292216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292236 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 1, 3, 7]
def baseStart_6292236 : Nat := 118140960795 + 6292236 * 2 ^ 59
def prefixEnd_6292236 : Nat := 4983230072969 + 3 ^ 40 * 6292236 * 2
def baseEnd_6292236 : Nat := 3230941459523948831412539

theorem tailTrace_6292236 : CollatzResearch.WordTrace tailWord_6292236 prefixEnd_6292236 3230941459523948831412539 := by
  unfold tailWord_6292236
  simp only [CollatzResearch.WordTrace]
  refine ⟨114748350416155537599188281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152997800554874050132251041 114748350416155537599188281)
  ·
    refine ⟨86061262812116653199391211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114748350416155537599188281 86061262812116653199391211)
    ·
      refine ⟨129091894218174979799086817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86061262812116653199391211 129091894218174979799086817)
      ·
        refine ⟨96818920663631234849315113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129091894218174979799086817 96818920663631234849315113)
        ·
          refine ⟨72614190497723426136986335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96818920663631234849315113 72614190497723426136986335)
          ·
            refine ⟨108921285746585139205479503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72614190497723426136986335 108921285746585139205479503)
            ·
              refine ⟨163381928619877708808219255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108921285746585139205479503 163381928619877708808219255)
              ·
                refine ⟨245072892929816563212328883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163381928619877708808219255 245072892929816563212328883)
                ·
                  refine ⟨367609339394724844818493325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 245072892929816563212328883 367609339394724844818493325)
                  ·
                    refine ⟨137853502273021816806934997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 367609339394724844818493325 137853502273021816806934997)
                    ·
                      refine ⟨3230941459523948831412539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 137853502273021816806934997 3230941459523948831412539)
                      ·
                        rfl

theorem cell23_6292236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_6292236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292236 prefixEnd_6292236 := by exact prefixLift 6292236
  have htrace : WordTrace (prefixWord ++ tailWord_6292236) baseStart_6292236 baseEnd_6292236 := by
    simpa [prefixWord, tailWord_6292236, baseEnd_6292236] using wordTrace_append hprefix tailTrace_6292236
  have hstable : (prefixWord ++ tailWord_6292236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292236).length < 2 ^ (prefixWord ++ tailWord_6292236).sum := by decide
  have hdescent : baseEnd_6292236 < baseStart_6292236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292243 : List Nat := [1, 1, 1, 2, 1, 3, 4, 4, 1, 5]
def baseStart_6292243 : Nat := 118140960795 + 6292243 * 2 ^ 59
def prefixEnd_6292243 : Nat := 4983230072969 + 3 ^ 40 * 6292243 * 2
def baseEnd_6292243 : Nat := 1076981684629510101341669

theorem tailTrace_6292243 : CollatzResearch.WordTrace tailWord_6292243 prefixEnd_6292243 1076981684629510101341669 := by
  unfold tailWord_6292243
  simp only [CollatzResearch.WordTrace]
  refine ⟨229496956143285715393881383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152997970762190476929254255 229496956143285715393881383)
  ·
    refine ⟨344245434214928573090822075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229496956143285715393881383 344245434214928573090822075)
    ·
      refine ⟨516368151322392859636233113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344245434214928573090822075 516368151322392859636233113)
      ·
        refine ⟨387276113491794644727174835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 516368151322392859636233113 387276113491794644727174835)
        ·
          refine ⟨580914170237691967090762253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387276113491794644727174835 580914170237691967090762253)
          ·
            refine ⟨217842813839134487659035845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 580914170237691967090762253 217842813839134487659035845)
            ·
              refine ⟨40845527594837716436069221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 217842813839134487659035845 40845527594837716436069221)
              ·
                refine ⟨7658536424032071831762979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40845527594837716436069221 7658536424032071831762979)
                ·
                  refine ⟨11487804636048107747644469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7658536424032071831762979 11487804636048107747644469)
                  ·
                    refine ⟨1076981684629510101341669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11487804636048107747644469 1076981684629510101341669)
                    ·
                      rfl

theorem cell23_6292243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 5].length) (baseStart_6292243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292243 prefixEnd_6292243 := by exact prefixLift 6292243
  have htrace : WordTrace (prefixWord ++ tailWord_6292243) baseStart_6292243 baseEnd_6292243 := by
    simpa [prefixWord, tailWord_6292243, baseEnd_6292243] using wordTrace_append hprefix tailTrace_6292243
  have hstable : (prefixWord ++ tailWord_6292243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292243).length < 2 ^ (prefixWord ++ tailWord_6292243).sum := by decide
  have hdescent : baseEnd_6292243 < baseStart_6292243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292250 : List Nat := [3, 1, 1, 3, 2, 1, 3, 1, 1, 5, 2]
def baseStart_6292250 : Nat := 118140960795 + 6292250 * 2 ^ 59
def prefixEnd_6292250 : Nat := 4983230072969 + 3 ^ 40 * 6292250 * 2
def baseEnd_6292250 : Nat := 3230948648253111776637475

theorem tailTrace_6292250 : CollatzResearch.WordTrace tailWord_6292250 prefixEnd_6292250 3230948648253111776637475 := by
  unfold tailWord_6292250
  simp only [CollatzResearch.WordTrace]
  refine ⟨57374302863565088897346551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152998140969506903726257469 57374302863565088897346551)
  ·
    refine ⟨86061454295347633346019827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57374302863565088897346551 86061454295347633346019827)
    ·
      refine ⟨129092181443021450019029741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86061454295347633346019827 129092181443021450019029741)
      ·
        refine ⟨48409568041133043757136153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129092181443021450019029741 48409568041133043757136153)
        ·
          refine ⟨36307176030849782817852115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48409568041133043757136153 36307176030849782817852115)
          ·
            refine ⟨54460764046274674226778173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36307176030849782817852115 54460764046274674226778173)
            ·
              refine ⟨20422786517353002835041815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54460764046274674226778173 20422786517353002835041815)
              ·
                refine ⟨30634179776029504252562723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20422786517353002835041815 30634179776029504252562723)
                ·
                  refine ⟨45951269664044256378844085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30634179776029504252562723 45951269664044256378844085)
                  ·
                    refine ⟨4307931531004149035516633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45951269664044256378844085 4307931531004149035516633)
                    ·
                      refine ⟨3230948648253111776637475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4307931531004149035516633 3230948648253111776637475)
                      ·
                        rfl

theorem cell23_6292250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_6292250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292250 prefixEnd_6292250 := by exact prefixLift 6292250
  have htrace : WordTrace (prefixWord ++ tailWord_6292250) baseStart_6292250 baseEnd_6292250 := by
    simpa [prefixWord, tailWord_6292250, baseEnd_6292250] using wordTrace_append hprefix tailTrace_6292250
  have hstable : (prefixWord ++ tailWord_6292250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292250).length < 2 ^ (prefixWord ++ tailWord_6292250).sum := by decide
  have hdescent : baseEnd_6292250 < baseStart_6292250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292293 : List Nat := [1, 3, 1, 1, 1, 2, 2, 5, 1, 2, 4]
def baseStart_6292293 : Nat := 118140960795 + 6292293 * 2 ^ 59
def prefixEnd_6292293 : Nat := 4983230072969 + 3 ^ 40 * 6292293 * 2
def baseEnd_6292293 : Nat := 3230970727921255108399777

theorem tailTrace_6292293 : CollatzResearch.WordTrace tailWord_6292293 prefixEnd_6292293 3230970727921255108399777 := by
  unfold tailWord_6292293
  simp only [CollatzResearch.WordTrace]
  refine ⟨229498779793104573933201533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152999186528736382622134355 229498779793104573933201533)
  ·
    refine ⟨86062042422414215224950575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229498779793104573933201533 86062042422414215224950575)
    ·
      refine ⟨129093063633621322837425863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86062042422414215224950575 129093063633621322837425863)
      ·
        refine ⟨193639595450431984256138795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129093063633621322837425863 193639595450431984256138795)
        ·
          refine ⟨290459393175647976384208193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193639595450431984256138795 290459393175647976384208193)
          ·
            refine ⟨217844544881735982288156145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290459393175647976384208193 217844544881735982288156145)
            ·
              refine ⟨163383408661301986716117109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217844544881735982288156145 163383408661301986716117109)
              ·
                refine ⟨15317194561997061254635979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 163383408661301986716117109 15317194561997061254635979)
                ·
                  refine ⟨22975791842995591881953969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15317194561997061254635979 22975791842995591881953969)
                  ·
                    refine ⟨17231843882246693911465477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22975791842995591881953969 17231843882246693911465477)
                    ·
                      refine ⟨3230970727921255108399777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17231843882246693911465477 3230970727921255108399777)
                      ·
                        rfl

theorem cell23_6292293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_6292293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292293 prefixEnd_6292293 := by exact prefixLift 6292293
  have htrace : WordTrace (prefixWord ++ tailWord_6292293) baseStart_6292293 baseEnd_6292293 := by
    simpa [prefixWord, tailWord_6292293, baseEnd_6292293] using wordTrace_append hprefix tailTrace_6292293
  have hstable : (prefixWord ++ tailWord_6292293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292293).length < 2 ^ (prefixWord ++ tailWord_6292293).sum := by decide
  have hdescent : baseEnd_6292293 < baseStart_6292293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292297 : List Nat := [1, 2, 1, 1, 2, 5, 2, 2, 3, 2, 2]
def baseStart_6292297 : Nat := 118140960795 + 6292297 * 2 ^ 59
def prefixEnd_6292297 : Nat := 4983230072969 + 3 ^ 40 * 6292297 * 2
def baseEnd_6292297 : Nat := 3230972781843873092749759

theorem tailTrace_6292297 : CollatzResearch.WordTrace tailWord_6292297 prefixEnd_6292297 3230972781843873092749759 := by
  unfold tailWord_6292297
  simp only [CollatzResearch.WordTrace]
  refine ⟨229498925685090082616347145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152999283790060055077564763 229498925685090082616347145)
  ·
    refine ⟨172124194263817561962260359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229498925685090082616347145 172124194263817561962260359)
    ·
      refine ⟨258186291395726342943390539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172124194263817561962260359 258186291395726342943390539)
      ·
        refine ⟨387279437093589514415085809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258186291395726342943390539 387279437093589514415085809)
        ·
          refine ⟨290459577820192135811314357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387279437093589514415085809 290459577820192135811314357)
          ·
            refine ⟨27230585420643012732310721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 290459577820192135811314357 27230585420643012732310721)
            ·
              refine ⟨20422939065482259549233041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27230585420643012732310721 20422939065482259549233041)
              ·
                refine ⟨15317204299111694661924781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20422939065482259549233041 15317204299111694661924781)
                ·
                  refine ⟨5743951612166885498221793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15317204299111694661924781 5743951612166885498221793)
                  ·
                    refine ⟨4307963709125164123666345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5743951612166885498221793 4307963709125164123666345)
                    ·
                      refine ⟨3230972781843873092749759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4307963709125164123666345 3230972781843873092749759)
                      ·
                        rfl

theorem cell23_6292297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 3, 2, 2].length) (baseStart_6292297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292297 prefixEnd_6292297 := by exact prefixLift 6292297
  have htrace : WordTrace (prefixWord ++ tailWord_6292297) baseStart_6292297 baseEnd_6292297 := by
    simpa [prefixWord, tailWord_6292297, baseEnd_6292297] using wordTrace_append hprefix tailTrace_6292297
  have hstable : (prefixWord ++ tailWord_6292297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292297).length < 2 ^ (prefixWord ++ tailWord_6292297).sum := by decide
  have hdescent : baseEnd_6292297 < baseStart_6292297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292308 : List Nat := [2, 4, 1, 1, 5, 1, 1, 3, 1, 1, 3]
def baseStart_6292308 : Nat := 118140960795 + 6292308 * 2 ^ 59
def prefixEnd_6292308 : Nat := 4983230072969 + 3 ^ 40 * 6292308 * 2
def baseEnd_6292308 : Nat := 3230978430131072549712209

theorem tailTrace_6292308 : CollatzResearch.WordTrace tailWord_6292308 prefixEnd_6292308 3230978430131072549712209 := by
  unfold tailWord_6292308
  simp only [CollatzResearch.WordTrace]
  refine ⟨114749663444025115747498789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152999551258700154329998385 114749663444025115747498789)
  ·
    refine ⟨21515561895754709202656023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114749663444025115747498789 21515561895754709202656023)
    ·
      refine ⟨32273342843632063803984035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21515561895754709202656023 32273342843632063803984035)
      ·
        refine ⟨48410014265448095705976053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32273342843632063803984035 48410014265448095705976053)
        ·
          refine ⟨4538438837385758972435255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48410014265448095705976053 4538438837385758972435255)
          ·
            refine ⟨6807658256078638458652883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4538438837385758972435255 6807658256078638458652883)
            ·
              refine ⟨10211487384117957687979325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6807658256078638458652883 10211487384117957687979325)
              ·
                refine ⟨3829307769044234132992247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10211487384117957687979325 3829307769044234132992247)
                ·
                  refine ⟨5743961653566351199488371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3829307769044234132992247 5743961653566351199488371)
                  ·
                    refine ⟨8615942480349526799232557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5743961653566351199488371 8615942480349526799232557)
                    ·
                      refine ⟨3230978430131072549712209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8615942480349526799232557 3230978430131072549712209)
                      ·
                        rfl

theorem cell23_6292308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_6292308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292308 prefixEnd_6292308 := by exact prefixLift 6292308
  have htrace : WordTrace (prefixWord ++ tailWord_6292308) baseStart_6292308 baseEnd_6292308 := by
    simpa [prefixWord, tailWord_6292308, baseEnd_6292308] using wordTrace_append hprefix tailTrace_6292308
  have hstable : (prefixWord ++ tailWord_6292308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292308).length < 2 ^ (prefixWord ++ tailWord_6292308).sum := by decide
  have hdescent : baseEnd_6292308 < baseStart_6292308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292333 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 2, 7]
def baseStart_6292333 : Nat := 118140960795 + 6292333 * 2 ^ 59
def prefixEnd_6292333 : Nat := 4983230072969 + 3 ^ 40 * 6292333 * 2
def baseEnd_6292333 : Nat := 1076997089049144983966531

theorem tailTrace_6292333 : CollatzResearch.WordTrace tailWord_6292333 prefixEnd_6292333 1076997089049144983966531 := by
  unfold tailWord_6292333
  simp only [CollatzResearch.WordTrace]
  refine ⟨229500238712959660764657653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153000159141973107176438435 229500238712959660764657653)
  ·
    refine ⟨21515647379339968196686655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 229500238712959660764657653 21515647379339968196686655)
    ·
      refine ⟨32273471069009952295029983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21515647379339968196686655 32273471069009952295029983)
      ·
        refine ⟨48410206603514928442544975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32273471069009952295029983 48410206603514928442544975)
        ·
          refine ⟨72615309905272392663817463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48410206603514928442544975 72615309905272392663817463)
          ·
            refine ⟨108922964857908588995726195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72615309905272392663817463 108922964857908588995726195)
            ·
              refine ⟨163384447286862883493589293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108922964857908588995726195 163384447286862883493589293)
              ·
                refine ⟨61269167732573581310095985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163384447286862883493589293 61269167732573581310095985)
                ·
                  refine ⟨45951875799430185982571989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61269167732573581310095985 45951875799430185982571989)
                  ·
                    refine ⟨1076997089049144983966531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45951875799430185982571989 1076997089049144983966531)
                    ·
                      rfl

theorem cell23_6292333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_6292333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292333 prefixEnd_6292333 := by exact prefixLift 6292333
  have htrace : WordTrace (prefixWord ++ tailWord_6292333) baseStart_6292333 baseEnd_6292333 := by
    simpa [prefixWord, tailWord_6292333, baseEnd_6292333] using wordTrace_append hprefix tailTrace_6292333
  have hstable : (prefixWord ++ tailWord_6292333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292333).length < 2 ^ (prefixWord ++ tailWord_6292333).sum := by decide
  have hdescent : baseEnd_6292333 < baseStart_6292333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292357 : List Nat := [1, 3, 1, 1, 3, 4, 1, 1, 3, 3, 2]
def baseStart_6292357 : Nat := 118140960795 + 6292357 * 2 ^ 59
def prefixEnd_6292357 : Nat := 4983230072969 + 3 ^ 40 * 6292357 * 2
def baseEnd_6292357 : Nat := 3231003590683142857999483

theorem tailTrace_6292357 : CollatzResearch.WordTrace tailWord_6292357 prefixEnd_6292357 3231003590683142857999483 := by
  unfold tailWord_6292357
  simp only [CollatzResearch.WordTrace]
  refine ⟨229501114064872712863531325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153000742709915141909020883 229501114064872712863531325)
  ·
    refine ⟨86062917774327267323824247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229501114064872712863531325 86062917774327267323824247)
    ·
      refine ⟨129094376661490900985736371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86062917774327267323824247 129094376661490900985736371)
      ·
        refine ⟨193641564992236351478604557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129094376661490900985736371 193641564992236351478604557)
        ·
          refine ⟨72615586872088631804476709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193641564992236351478604557 72615586872088631804476709)
          ·
            refine ⟨13615422538516618463339383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72615586872088631804476709 13615422538516618463339383)
            ·
              refine ⟨20423133807774927695009075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13615422538516618463339383 20423133807774927695009075)
              ·
                refine ⟨30634700711662391542513613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20423133807774927695009075 30634700711662391542513613)
                ·
                  refine ⟨11488012766873396828442605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30634700711662391542513613 11488012766873396828442605)
                  ·
                    refine ⟨4308004787577523810665977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11488012766873396828442605 4308004787577523810665977)
                    ·
                      refine ⟨3231003590683142857999483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4308004787577523810665977 3231003590683142857999483)
                      ·
                        rfl

theorem cell23_6292357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 3, 2].length) (baseStart_6292357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292357 prefixEnd_6292357 := by exact prefixLift 6292357
  have htrace : WordTrace (prefixWord ++ tailWord_6292357) baseStart_6292357 baseEnd_6292357 := by
    simpa [prefixWord, tailWord_6292357, baseEnd_6292357] using wordTrace_append hprefix tailTrace_6292357
  have hstable : (prefixWord ++ tailWord_6292357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292357).length < 2 ^ (prefixWord ++ tailWord_6292357).sum := by decide
  have hdescent : baseEnd_6292357 < baseStart_6292357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292387 : List Nat := [1, 1, 1, 4, 1, 2, 2, 3, 4, 2, 2]
def baseStart_6292387 : Nat := 118140960795 + 6292387 * 2 ^ 59
def prefixEnd_6292387 : Nat := 4983230072969 + 3 ^ 40 * 6292387 * 2
def baseEnd_6292387 : Nat := 3231018995102777740624345

theorem tailTrace_6292387 : CollatzResearch.WordTrace tailWord_6292387 prefixEnd_6292387 3231018995102777740624345 := by
  unfold tailWord_6292387
  simp only [CollatzResearch.WordTrace]
  refine ⟨229502208254764027987123415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153001472169842685324748943 229502208254764027987123415)
  ·
    refine ⟨344253312382146041980685123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229502208254764027987123415 344253312382146041980685123)
    ·
      refine ⟨516379968573219062971027685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344253312382146041980685123 516379968573219062971027685)
      ·
        refine ⟨96821244107478574307067691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 516379968573219062971027685 96821244107478574307067691)
        ·
          refine ⟨145231866161217861460601537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96821244107478574307067691 145231866161217861460601537)
          ·
            refine ⟨108923899620913396095451153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145231866161217861460601537 108923899620913396095451153)
            ·
              refine ⟨81692924715685047071588365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108923899620913396095451153 81692924715685047071588365)
              ·
                refine ⟨30634846768381892651845637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81692924715685047071588365 30634846768381892651845637)
                ·
                  refine ⟨5744033769071604872221057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30634846768381892651845637 5744033769071604872221057)
                  ·
                    refine ⟨4308025326803703654165793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5744033769071604872221057 4308025326803703654165793)
                    ·
                      refine ⟨3231018995102777740624345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4308025326803703654165793 3231018995102777740624345)
                      ·
                        rfl

theorem cell23_6292387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 4, 2, 2].length) (baseStart_6292387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292387 prefixEnd_6292387 := by exact prefixLift 6292387
  have htrace : WordTrace (prefixWord ++ tailWord_6292387) baseStart_6292387 baseEnd_6292387 := by
    simpa [prefixWord, tailWord_6292387, baseEnd_6292387] using wordTrace_append hprefix tailTrace_6292387
  have hstable : (prefixWord ++ tailWord_6292387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292387).length < 2 ^ (prefixWord ++ tailWord_6292387).sum := by decide
  have hdescent : baseEnd_6292387 < baseStart_6292387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292393 : List Nat := [1, 2, 1, 1, 1, 1, 6, 3, 7]
def baseStart_6292393 : Nat := 118140960795 + 6292393 * 2 ^ 59
def prefixEnd_6292393 : Nat := 4983230072969 + 3 ^ 40 * 6292393 * 2
def baseEnd_6292393 : Nat := 359002452887411635238813

theorem tailTrace_6292393 : CollatzResearch.WordTrace tailWord_6292393 prefixEnd_6292393 359002452887411635238813 := by
  unfold tailWord_6292393
  simp only [CollatzResearch.WordTrace]
  refine ⟨229502427092742291011841833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153001618061828194007894555 229502427092742291011841833)
  ·
    refine ⟨172126820319556718258881375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229502427092742291011841833 172126820319556718258881375)
    ·
      refine ⟨258190230479335077388322063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172126820319556718258881375 258190230479335077388322063)
      ·
        refine ⟨387285345719002616082483095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258190230479335077388322063 387285345719002616082483095)
        ·
          refine ⟨580928018578503924123724643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387285345719002616082483095 580928018578503924123724643)
          ·
            refine ⟨871392027867755886185586965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580928018578503924123724643 871392027867755886185586965)
            ·
              refine ⟨40846501306301057164949389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 871392027867755886185586965 40846501306301057164949389)
              ·
                refine ⟨15317437989862896436856021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40846501306301057164949389 15317437989862896436856021)
                ·
                  refine ⟨359002452887411635238813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15317437989862896436856021 359002452887411635238813)
                  ·
                    rfl

theorem cell23_6292393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 7].length) (baseStart_6292393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292393 prefixEnd_6292393 := by exact prefixLift 6292393
  have htrace : WordTrace (prefixWord ++ tailWord_6292393) baseStart_6292393 baseEnd_6292393 := by
    simpa [prefixWord, tailWord_6292393, baseEnd_6292393] using wordTrace_append hprefix tailTrace_6292393
  have hstable : (prefixWord ++ tailWord_6292393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292393).length < 2 ^ (prefixWord ++ tailWord_6292393).sum := by decide
  have hdescent : baseEnd_6292393 < baseStart_6292393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292427 : List Nat := [1, 1, 1, 1, 3, 6, 2, 3, 5]
def baseStart_6292427 : Nat := 118140960795 + 6292427 * 2 ^ 59
def prefixEnd_6292427 : Nat := 4983230072969 + 3 ^ 40 * 6292427 * 2
def baseEnd_6292427 : Nat := 359004392703217509347129

theorem tailTrace_6292427 : CollatzResearch.WordTrace tailWord_6292427 prefixEnd_6292427 359004392703217509347129 := by
  unfold tailWord_6292427
  simp only [CollatzResearch.WordTrace]
  refine ⟨229503667174619114818579535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153002444783079409879053023 229503667174619114818579535)
  ·
    refine ⟨344255500761928672227869303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229503667174619114818579535 344255500761928672227869303)
    ·
      refine ⟨516383251142893008341803955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344255500761928672227869303 516383251142893008341803955)
      ·
        refine ⟨774574876714339512512705933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516383251142893008341803955 774574876714339512512705933)
        ·
          refine ⟨290465578767877317192264725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 774574876714339512512705933 290465578767877317192264725)
          ·
            refine ⟨13615574004744249243387409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 290465578767877317192264725 13615574004744249243387409)
            ·
              refine ⟨10211680503558186932540557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13615574004744249243387409 10211680503558186932540557)
              ·
                refine ⟨3829380188834320099702709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10211680503558186932540557 3829380188834320099702709)
                ·
                  refine ⟨359004392703217509347129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3829380188834320099702709 359004392703217509347129)
                  ·
                    rfl

theorem cell23_6292427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 3, 5].length) (baseStart_6292427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292427 prefixEnd_6292427 := by exact prefixLift 6292427
  have htrace : WordTrace (prefixWord ++ tailWord_6292427) baseStart_6292427 baseEnd_6292427 := by
    simpa [prefixWord, tailWord_6292427, baseEnd_6292427] using wordTrace_append hprefix tailTrace_6292427
  have hstable : (prefixWord ++ tailWord_6292427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292427).length < 2 ^ (prefixWord ++ tailWord_6292427).sum := by decide
  have hdescent : baseEnd_6292427 < baseStart_6292427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
