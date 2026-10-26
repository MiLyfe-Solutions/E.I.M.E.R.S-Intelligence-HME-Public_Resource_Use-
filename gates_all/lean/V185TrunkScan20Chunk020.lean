import V185TrunkScan20Chunk019

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_121289 : List Nat := [1, 2, 1, 1, 2, 1, 8, 2, 2]
def baseStart_121289 : Nat := 118140960795 + 121289 * 2 ^ 59
def prefixEnd_121289 : Nat := 4983230072969 + 3 ^ 40 * 121289 * 2
def baseEnd_121289 : Nat := 55359604536249946604185

theorem tailTrace_121289 : CollatzResearch.WordTrace tailWord_121289 prefixEnd_121289 55359604536249946604185 := by
  unfold tailWord_121289
  simp only [CollatzResearch.WordTrace]
  refine ⟨4423773257598142357142921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2949182171732094904761947 4423773257598142357142921)
  ·
    refine ⟨3317829943198606767857191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4423773257598142357142921 3317829943198606767857191)
    ·
      refine ⟨4976744914797910151785787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3317829943198606767857191 4976744914797910151785787)
      ·
        refine ⟨7465117372196865227678681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4976744914797910151785787 7465117372196865227678681)
        ·
          refine ⟨5598838029147648920759011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7465117372196865227678681 5598838029147648920759011)
          ·
            refine ⟨8398257043721473381138517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5598838029147648920759011 8398257043721473381138517)
            ·
              refine ⟨98417074731111016185217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 8398257043721473381138517 98417074731111016185217)
              ·
                refine ⟨73812806048333262138913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98417074731111016185217 73812806048333262138913)
                ·
                  refine ⟨55359604536249946604185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73812806048333262138913 55359604536249946604185)
                  ·
                    rfl

theorem cell20_121289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 2, 2].length) (baseStart_121289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121289 prefixEnd_121289 := by exact prefixLift 121289
  have htrace : WordTrace (prefixWord ++ tailWord_121289) baseStart_121289 baseEnd_121289 := by
    simpa [prefixWord, tailWord_121289, baseEnd_121289] using wordTrace_append hprefix tailTrace_121289
  have hstable : (prefixWord ++ tailWord_121289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121289).length < 2 ^ (prefixWord ++ tailWord_121289).sum := by decide
  have hdescent : baseEnd_121289 < baseStart_121289 := by decide
  rcases family_descends (prefixWord ++ tailWord_121289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121348 : List Nat := [2, 3, 2, 3, 1, 1, 1, 3, 4]
def baseStart_121348 : Nat := 118140960795 + 121348 * 2 ^ 59
def prefixEnd_121348 : Nat := 4983230072969 + 3 ^ 40 * 121348 * 2
def baseEnd_121348 : Nat := 55386533743907963637277

theorem tailTrace_121348 : CollatzResearch.WordTrace tailWord_121348 prefixEnd_121348 55386533743907963637277 := by
  unfold tailWord_121348
  simp only [CollatzResearch.WordTrace]
  refine ⟨2212962582192197716770349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2950616776256263622360465 2212962582192197716770349)
  ·
    refine ⟨829860968322074143788881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2212962582192197716770349 829860968322074143788881)
    ·
      refine ⟨622395726241555607841661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 829860968322074143788881 622395726241555607841661)
      ·
        refine ⟨233398397340583352940623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 622395726241555607841661 233398397340583352940623)
        ·
          refine ⟨350097596010875029410935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233398397340583352940623 350097596010875029410935)
          ·
            refine ⟨525146394016312544116403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350097596010875029410935 525146394016312544116403)
            ·
              refine ⟨787719591024468816174605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525146394016312544116403 787719591024468816174605)
              ·
                refine ⟨295394846634175806065477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 787719591024468816174605 295394846634175806065477)
                ·
                  refine ⟨55386533743907963637277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 295394846634175806065477 55386533743907963637277)
                  ·
                    rfl

theorem cell20_121348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_121348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121348 prefixEnd_121348 := by exact prefixLift 121348
  have htrace : WordTrace (prefixWord ++ tailWord_121348) baseStart_121348 baseEnd_121348 := by
    simpa [prefixWord, tailWord_121348, baseEnd_121348] using wordTrace_append hprefix tailTrace_121348
  have hstable : (prefixWord ++ tailWord_121348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121348).length < 2 ^ (prefixWord ++ tailWord_121348).sum := by decide
  have hdescent : baseEnd_121348 < baseStart_121348 := by decide
  rcases family_descends (prefixWord ++ tailWord_121348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121358 : List Nat := [4, 1, 1, 2, 3, 2, 3, 1, 3]
def baseStart_121358 : Nat := 118140960795 + 121358 * 2 ^ 59
def prefixEnd_121358 : Nat := 4983230072969 + 3 ^ 40 * 121358 * 2
def baseEnd_121358 : Nat := 55391098016392373303903

theorem tailTrace_121358 : CollatzResearch.WordTrace tailWord_121358 prefixEnd_121358 55391098016392373303903 := by
  unfold tailWord_121358
  simp only [CollatzResearch.WordTrace]
  refine ⟨553286236793520892675591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2950859929565444760936485 553286236793520892675591)
  ·
    refine ⟨829929355190281339013387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 553286236793520892675591 829929355190281339013387)
    ·
      refine ⟨1244894032785422008520081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 829929355190281339013387 1244894032785422008520081)
      ·
        refine ⟨933670524589066506390061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1244894032785422008520081 933670524589066506390061)
        ·
          refine ⟨350126446720899939896273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 933670524589066506390061 350126446720899939896273)
          ·
            refine ⟨262594835040674954922205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350126446720899939896273 262594835040674954922205)
            ·
              refine ⟨98473063140253108095827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262594835040674954922205 98473063140253108095827)
              ·
                refine ⟨147709594710379662143741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98473063140253108095827 147709594710379662143741)
                ·
                  refine ⟨55391098016392373303903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147709594710379662143741 55391098016392373303903)
                  ·
                    rfl

theorem cell20_121358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_121358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121358 prefixEnd_121358 := by exact prefixLift 121358
  have htrace : WordTrace (prefixWord ++ tailWord_121358) baseStart_121358 baseEnd_121358 := by
    simpa [prefixWord, tailWord_121358, baseEnd_121358] using wordTrace_append hprefix tailTrace_121358
  have hstable : (prefixWord ++ tailWord_121358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121358).length < 2 ^ (prefixWord ++ tailWord_121358).sum := by decide
  have hdescent : baseEnd_121358 < baseStart_121358 := by decide
  rcases family_descends (prefixWord ++ tailWord_121358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121372 : List Nat := [2, 2, 3, 1, 2, 4, 2, 4]
def baseStart_121372 : Nat := 118140960795 + 121372 * 2 ^ 59
def prefixEnd_121372 : Nat := 4983230072969 + 3 ^ 40 * 121372 * 2
def baseEnd_121372 : Nat := 18465829332623515612393

theorem tailTrace_121372 : CollatzResearch.WordTrace tailWord_121372 prefixEnd_121372 18465829332623515612393 := by
  unfold tailWord_121372
  simp only [CollatzResearch.WordTrace]
  refine ⟨2213400258148723766207185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2951200344198298354942913 2213400258148723766207185)
  ·
    refine ⟨1660050193611542824655389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2213400258148723766207185 1660050193611542824655389)
    ·
      refine ⟨622518822604328559245771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1660050193611542824655389 622518822604328559245771)
      ·
        refine ⟨933778233906492838868657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622518822604328559245771 933778233906492838868657)
        ·
          refine ⟨700333675429869629151493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 933778233906492838868657 700333675429869629151493)
          ·
            refine ⟨131312564143100555465905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 700333675429869629151493 131312564143100555465905)
            ·
              refine ⟨98484423107325416599429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131312564143100555465905 98484423107325416599429)
              ·
                refine ⟨18465829332623515612393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98484423107325416599429 18465829332623515612393)
                ·
                  rfl

theorem cell20_121372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 4].length) (baseStart_121372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121372 prefixEnd_121372 := by exact prefixLift 121372
  have htrace : WordTrace (prefixWord ++ tailWord_121372) baseStart_121372 baseEnd_121372 := by
    simpa [prefixWord, tailWord_121372, baseEnd_121372] using wordTrace_append hprefix tailTrace_121372
  have hstable : (prefixWord ++ tailWord_121372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121372).length < 2 ^ (prefixWord ++ tailWord_121372).sum := by decide
  have hdescent : baseEnd_121372 < baseStart_121372 := by decide
  rcases family_descends (prefixWord ++ tailWord_121372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121400 : List Nat := [2, 1, 2, 1, 4, 1, 2, 4, 3]
def baseStart_121400 : Nat := 118140960795 + 121400 * 2 ^ 59
def prefixEnd_121400 : Nat := 4983230072969 + 3 ^ 40 * 121400 * 2
def baseEnd_121400 : Nat := 55410267960826893903731

theorem tailTrace_121400 : CollatzResearch.WordTrace tailWord_121400 prefixEnd_121400 55410267960826893903731 := by
  unfold tailWord_121400
  simp only [CollatzResearch.WordTrace]
  refine ⟨2213910880098004157216827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2951881173464005542955769 2213910880098004157216827)
  ·
    refine ⟨3320866320147006235825241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2213910880098004157216827 3320866320147006235825241)
    ·
      refine ⟨2490649740110254676868931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3320866320147006235825241 2490649740110254676868931)
      ·
        refine ⟨3735974610165382015303397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2490649740110254676868931 3735974610165382015303397)
        ·
          refine ⟨700495239406009127869387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3735974610165382015303397 700495239406009127869387)
          ·
            refine ⟨1050742859109013691804081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700495239406009127869387 1050742859109013691804081)
            ·
              refine ⟨788057144331760268853061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1050742859109013691804081 788057144331760268853061)
              ·
                refine ⟨147760714562205050409949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 788057144331760268853061 147760714562205050409949)
                ·
                  refine ⟨55410267960826893903731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147760714562205050409949 55410267960826893903731)
                  ·
                    rfl

theorem cell20_121400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 3].length) (baseStart_121400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121400 prefixEnd_121400 := by exact prefixLift 121400
  have htrace : WordTrace (prefixWord ++ tailWord_121400) baseStart_121400 baseEnd_121400 := by
    simpa [prefixWord, tailWord_121400, baseEnd_121400] using wordTrace_append hprefix tailTrace_121400
  have hstable : (prefixWord ++ tailWord_121400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121400).length < 2 ^ (prefixWord ++ tailWord_121400).sum := by decide
  have hdescent : baseEnd_121400 < baseStart_121400 := by decide
  rcases family_descends (prefixWord ++ tailWord_121400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121497 : List Nat := [1, 2, 1, 2, 1, 2, 4, 2, 5]
def baseStart_121497 : Nat := 118140960795 + 121497 * 2 ^ 59
def prefixEnd_121497 : Nat := 4983230072969 + 3 ^ 40 * 121497 * 2
def baseEnd_121497 : Nat := 55454541403925667670001

theorem tailTrace_121497 : CollatzResearch.WordTrace tailWord_121497 prefixEnd_121497 55454541403925667670001 := by
  unfold tailWord_121497
  simp only [CollatzResearch.WordTrace]
  refine ⟨4431359640844593880714745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2954239760563062587143163 4431359640844593880714745)
  ·
    refine ⟨3323519730633445410536059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4431359640844593880714745 3323519730633445410536059)
    ·
      refine ⟨4985279595950168115804089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3323519730633445410536059 4985279595950168115804089)
      ·
        refine ⟨3738959696962626086853067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4985279595950168115804089 3738959696962626086853067)
        ·
          refine ⟨5608439545443939130279601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3738959696962626086853067 5608439545443939130279601)
          ·
            refine ⟨4206329659082954347709701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5608439545443939130279601 4206329659082954347709701)
            ·
              refine ⟨788686811078053940195569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4206329659082954347709701 788686811078053940195569)
              ·
                refine ⟨591515108308540455146677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 788686811078053940195569 591515108308540455146677)
                ·
                  refine ⟨55454541403925667670001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 591515108308540455146677 55454541403925667670001)
                  ·
                    rfl

theorem cell20_121497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_121497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121497 prefixEnd_121497 := by exact prefixLift 121497
  have htrace : WordTrace (prefixWord ++ tailWord_121497) baseStart_121497 baseEnd_121497 := by
    simpa [prefixWord, tailWord_121497, baseEnd_121497] using wordTrace_append hprefix tailTrace_121497
  have hstable : (prefixWord ++ tailWord_121497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121497).length < 2 ^ (prefixWord ++ tailWord_121497).sum := by decide
  have hdescent : baseEnd_121497 < baseStart_121497 := by decide
  rcases family_descends (prefixWord ++ tailWord_121497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121517 : List Nat := [1, 5, 2, 1, 1, 2, 2, 4, 2]
def baseStart_121517 : Nat := 118140960795 + 121517 * 2 ^ 59
def prefixEnd_121517 : Nat := 4983230072969 + 3 ^ 40 * 121517 * 2
def baseEnd_121517 : Nat := 55463669948894487003253

theorem tailTrace_121517 : CollatzResearch.WordTrace tailWord_121517 prefixEnd_121517 55463669948894487003253 := by
  unfold tailWord_121517
  simp only [CollatzResearch.WordTrace]
  refine ⟨4432089100772137296442805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2954726067181424864295203 4432089100772137296442805)
  ·
    refine ⟨415508353197387871541513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4432089100772137296442805 415508353197387871541513)
    ·
      refine ⟨311631264898040903656135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415508353197387871541513 311631264898040903656135)
      ·
        refine ⟨467446897347061355484203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311631264898040903656135 467446897347061355484203)
        ·
          refine ⟨701170346020592033226305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467446897347061355484203 701170346020592033226305)
          ·
            refine ⟨525877759515444024919729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 701170346020592033226305 525877759515444024919729)
            ·
              refine ⟨394408319636583018689797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 525877759515444024919729 394408319636583018689797)
              ·
                refine ⟨73951559931859316004337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 394408319636583018689797 73951559931859316004337)
                ·
                  refine ⟨55463669948894487003253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73951559931859316004337 55463669948894487003253)
                  ·
                    rfl

theorem cell20_121517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_121517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121517 prefixEnd_121517 := by exact prefixLift 121517
  have htrace : WordTrace (prefixWord ++ tailWord_121517) baseStart_121517 baseEnd_121517 := by
    simpa [prefixWord, tailWord_121517, baseEnd_121517] using wordTrace_append hprefix tailTrace_121517
  have hstable : (prefixWord ++ tailWord_121517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121517).length < 2 ^ (prefixWord ++ tailWord_121517).sum := by decide
  have hdescent : baseEnd_121517 < baseStart_121517 := by decide
  rcases family_descends (prefixWord ++ tailWord_121517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121586 : List Nat := [3, 2, 1, 3, 1, 4, 2, 1, 3]
def baseStart_121586 : Nat := 118140960795 + 121586 * 2 ^ 59
def prefixEnd_121586 : Nat := 4983230072969 + 3 ^ 40 * 121586 * 2
def baseEnd_121586 : Nat := 55495163429036913702971

theorem tailTrace_121586 : CollatzResearch.WordTrace tailWord_121586 prefixEnd_121586 55495163429036913702971 := by
  unfold tailWord_121586
  simp only [CollatzResearch.WordTrace]
  refine ⟨1108651434380540520176153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2956403825014774720469741 1108651434380540520176153)
  ·
    refine ⟨831488575785405390132115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1108651434380540520176153 831488575785405390132115)
    ·
      refine ⟨1247232863678108085198173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 831488575785405390132115 1247232863678108085198173)
      ·
        refine ⟨467712323879290531949315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1247232863678108085198173 467712323879290531949315)
        ·
          refine ⟨701568485818935797923973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467712323879290531949315 701568485818935797923973)
          ·
            refine ⟨131544091091050462110745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 701568485818935797923973 131544091091050462110745)
            ·
              refine ⟨98658068318287846583059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131544091091050462110745 98658068318287846583059)
              ·
                refine ⟨147987102477431769874589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98658068318287846583059 147987102477431769874589)
                ·
                  refine ⟨55495163429036913702971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147987102477431769874589 55495163429036913702971)
                  ·
                    rfl

theorem cell20_121586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_121586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121586 prefixEnd_121586 := by exact prefixLift 121586
  have htrace : WordTrace (prefixWord ++ tailWord_121586) baseStart_121586 baseEnd_121586 := by
    simpa [prefixWord, tailWord_121586, baseEnd_121586] using wordTrace_append hprefix tailTrace_121586
  have hstable : (prefixWord ++ tailWord_121586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121586).length < 2 ^ (prefixWord ++ tailWord_121586).sum := by decide
  have hdescent : baseEnd_121586 < baseStart_121586 := by decide
  rcases family_descends (prefixWord ++ tailWord_121586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121604 : List Nat := [2, 3, 2, 2, 1, 1, 1, 8]
def baseStart_121604 : Nat := 118140960795 + 121604 * 2 ^ 59
def prefixEnd_121604 : Nat := 4983230072969 + 3 ^ 40 * 121604 * 2
def baseEnd_121604 : Nat := 18501126373169617034299

theorem tailTrace_121604 : CollatzResearch.WordTrace tailWord_121604 prefixEnd_121604 18501126373169617034299 := by
  unfold tailWord_121604
  simp only [CollatzResearch.WordTrace]
  refine ⟨2217631125728475577429933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2956841500971300769906577 2217631125728475577429933)
  ·
    refine ⟨831611672148178341536225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2217631125728475577429933 831611672148178341536225)
    ·
      refine ⟨623708754111133756152169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 831611672148178341536225 623708754111133756152169)
      ·
        refine ⟨467781565583350317114127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 623708754111133756152169 467781565583350317114127)
        ·
          refine ⟨701672348375025475671191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467781565583350317114127 701672348375025475671191)
          ·
            refine ⟨1052508522562538213506787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701672348375025475671191 1052508522562538213506787)
            ·
              refine ⟨1578762783843807320260181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052508522562538213506787 1578762783843807320260181)
              ·
                refine ⟨18501126373169617034299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1578762783843807320260181 18501126373169617034299)
                ·
                  rfl

theorem cell20_121604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 8].length) (baseStart_121604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121604 prefixEnd_121604 := by exact prefixLift 121604
  have htrace : WordTrace (prefixWord ++ tailWord_121604) baseStart_121604 baseEnd_121604 := by
    simpa [prefixWord, tailWord_121604, baseEnd_121604] using wordTrace_append hprefix tailTrace_121604
  have hstable : (prefixWord ++ tailWord_121604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121604).length < 2 ^ (prefixWord ++ tailWord_121604).sum := by decide
  have hdescent : baseEnd_121604 < baseStart_121604 := by decide
  rcases family_descends (prefixWord ++ tailWord_121604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121614 : List Nat := [4, 1, 1, 2, 1, 1, 1, 7, 2]
def baseStart_121614 : Nat := 118140960795 + 121614 * 2 ^ 59
def prefixEnd_121614 : Nat := 4983230072969 + 3 ^ 40 * 121614 * 2
def baseEnd_121614 : Nat := 55507943391993260769523

theorem tailTrace_121614 : CollatzResearch.WordTrace tailWord_121614 prefixEnd_121614 55507943391993260769523 := by
  unfold tailWord_121614
  simp only [CollatzResearch.WordTrace]
  refine ⟨554453372677590357840487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2957084654280481908482597 554453372677590357840487)
  ·
    refine ⟨831680059016385536760731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 554453372677590357840487 831680059016385536760731)
    ·
      refine ⟨1247520088524578305141097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 831680059016385536760731 1247520088524578305141097)
      ·
        refine ⟨935640066393433728855823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1247520088524578305141097 935640066393433728855823)
        ·
          refine ⟨1403460099590150593283735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 935640066393433728855823 1403460099590150593283735)
          ·
            refine ⟨2105190149385225889925603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1403460099590150593283735 2105190149385225889925603)
            ·
              refine ⟨3157785224077838834888405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2105190149385225889925603 3157785224077838834888405)
              ·
                refine ⟨74010591189324347692697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3157785224077838834888405 74010591189324347692697)
                ·
                  refine ⟨55507943391993260769523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74010591189324347692697 55507943391993260769523)
                  ·
                    rfl

theorem cell20_121614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_121614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121614 prefixEnd_121614 := by exact prefixLift 121614
  have htrace : WordTrace (prefixWord ++ tailWord_121614) baseStart_121614 baseEnd_121614 := by
    simpa [prefixWord, tailWord_121614, baseEnd_121614] using wordTrace_append hprefix tailTrace_121614
  have hstable : (prefixWord ++ tailWord_121614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121614).length < 2 ^ (prefixWord ++ tailWord_121614).sum := by decide
  have hdescent : baseEnd_121614 < baseStart_121614 := by decide
  rcases family_descends (prefixWord ++ tailWord_121614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121628 : List Nat := [2, 2, 3, 1, 1, 3, 1, 4, 3]
def baseStart_121628 : Nat := 118140960795 + 121628 * 2 ^ 59
def prefixEnd_121628 : Nat := 4983230072969 + 3 ^ 40 * 121628 * 2
def baseEnd_121628 : Nat := 55514333373471434302799

theorem tailTrace_121628 : CollatzResearch.WordTrace tailWord_121628 prefixEnd_121628 55514333373471434302799 := by
  unfold tailWord_121628
  simp only [CollatzResearch.WordTrace]
  refine ⟨2218068801685001626866769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2957425068913335502489025 2218068801685001626866769)
  ·
    refine ⟨1663551601263751220150077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2218068801685001626866769 1663551601263751220150077)
    ·
      refine ⟨623831850473906707556279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1663551601263751220150077 623831850473906707556279)
      ·
        refine ⟨935747775710860061334419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623831850473906707556279 935747775710860061334419)
        ·
          refine ⟨1403621663566290092001629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 935747775710860061334419 1403621663566290092001629)
          ·
            refine ⟨526358123837358784500611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1403621663566290092001629 526358123837358784500611)
            ·
              refine ⟨789537185756038176750917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526358123837358784500611 789537185756038176750917)
              ·
                refine ⟨148038222329257158140797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 789537185756038176750917 148038222329257158140797)
                ·
                  refine ⟨55514333373471434302799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148038222329257158140797 55514333373471434302799)
                  ·
                    rfl

theorem cell20_121628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_121628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121628 prefixEnd_121628 := by exact prefixLift 121628
  have htrace : WordTrace (prefixWord ++ tailWord_121628) baseStart_121628 baseEnd_121628 := by
    simpa [prefixWord, tailWord_121628, baseEnd_121628] using wordTrace_append hprefix tailTrace_121628
  have hstable : (prefixWord ++ tailWord_121628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121628).length < 2 ^ (prefixWord ++ tailWord_121628).sum := by decide
  have hdescent : baseEnd_121628 < baseStart_121628 := by decide
  rcases family_descends (prefixWord ++ tailWord_121628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121631 : List Nat := [1, 1, 2, 4, 2, 2, 4, 2, 2]
def baseStart_121631 : Nat := 118140960795 + 121631 * 2 ^ 59
def prefixEnd_121631 : Nat := 4983230072969 + 3 ^ 40 * 121631 * 2
def baseEnd_121631 : Nat := 55515702655216757202787

theorem tailTrace_121631 : CollatzResearch.WordTrace tailWord_121631 prefixEnd_121631 55515702655216757202787 := by
  unfold tailWord_121631
  simp only [CollatzResearch.WordTrace]
  refine ⟨4436247022359134766092747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2957498014906089844061831 4436247022359134766092747)
  ·
    refine ⟨6654370533538702149139121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4436247022359134766092747 6654370533538702149139121)
    ·
      refine ⟨4990777900154026611854341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6654370533538702149139121 4990777900154026611854341)
      ·
        refine ⟨935770856278879989722689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4990777900154026611854341 935770856278879989722689)
        ·
          refine ⟨701828142209159992292017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 935770856278879989722689 701828142209159992292017)
          ·
            refine ⟨526371106656869994219013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 701828142209159992292017 526371106656869994219013)
            ·
              refine ⟨98694582498163123916065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 526371106656869994219013 98694582498163123916065)
              ·
                refine ⟨74020936873622342937049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98694582498163123916065 74020936873622342937049)
                ·
                  refine ⟨55515702655216757202787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74020936873622342937049 55515702655216757202787)
                  ·
                    rfl

theorem cell20_121631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 2, 2].length) (baseStart_121631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121631 prefixEnd_121631 := by exact prefixLift 121631
  have htrace : WordTrace (prefixWord ++ tailWord_121631) baseStart_121631 baseEnd_121631 := by
    simpa [prefixWord, tailWord_121631, baseEnd_121631] using wordTrace_append hprefix tailTrace_121631
  have hstable : (prefixWord ++ tailWord_121631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121631).length < 2 ^ (prefixWord ++ tailWord_121631).sum := by decide
  have hdescent : baseEnd_121631 < baseStart_121631 := by decide
  rcases family_descends (prefixWord ++ tailWord_121631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121690 : List Nat := [3, 1, 1, 2, 1, 4, 2, 4, 2]
def baseStart_121690 : Nat := 118140960795 + 121690 * 2 ^ 59
def prefixEnd_121690 : Nat := 4983230072969 + 3 ^ 40 * 121690 * 2
def baseEnd_121690 : Nat := 55542631862874774235879

theorem tailTrace_121690 : CollatzResearch.WordTrace tailWord_121690 prefixEnd_121690 55542631862874774235879 := by
  unfold tailWord_121690
  simp only [CollatzResearch.WordTrace]
  refine ⟨1109599732286346960622631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2958932619430258561660349 1109599732286346960622631)
  ·
    refine ⟨1664399598429520440933947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1109599732286346960622631 1664399598429520440933947)
    ·
      refine ⟨2496599397644280661400921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1664399598429520440933947 2496599397644280661400921)
      ·
        refine ⟨1872449548233210496050691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2496599397644280661400921 1872449548233210496050691)
        ·
          refine ⟨2808674322349815744076037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1872449548233210496050691 2808674322349815744076037)
          ·
            refine ⟨526626435440590452014257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2808674322349815744076037 526626435440590452014257)
            ·
              refine ⟨394969826580442839010693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526626435440590452014257 394969826580442839010693)
              ·
                refine ⟨74056842483833032314505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 394969826580442839010693 74056842483833032314505)
                ·
                  refine ⟨55542631862874774235879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74056842483833032314505 55542631862874774235879)
                  ·
                    rfl

theorem cell20_121690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 4, 2].length) (baseStart_121690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121690 prefixEnd_121690 := by exact prefixLift 121690
  have htrace : WordTrace (prefixWord ++ tailWord_121690) baseStart_121690 baseEnd_121690 := by
    simpa [prefixWord, tailWord_121690, baseEnd_121690] using wordTrace_append hprefix tailTrace_121690
  have hstable : (prefixWord ++ tailWord_121690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121690).length < 2 ^ (prefixWord ++ tailWord_121690).sum := by decide
  have hdescent : baseEnd_121690 < baseStart_121690 := by decide
  rcases family_descends (prefixWord ++ tailWord_121690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121725 : List Nat := [1, 4, 1, 1, 2, 1, 3, 2, 5]
def baseStart_121725 : Nat := 118140960795 + 121725 * 2 ^ 59
def prefixEnd_121725 : Nat := 4983230072969 + 3 ^ 40 * 121725 * 2
def baseEnd_121725 : Nat := 55558606816570208069069

theorem tailTrace_121725 : CollatzResearch.WordTrace tailWord_121725 prefixEnd_121725 55558606816570208069069 := by
  unfold tailWord_121725
  simp only [CollatzResearch.WordTrace]
  refine ⟨4439675484018588820014629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2959783656012392546676419 4439675484018588820014629)
  ·
    refine ⟨832439153253485403752743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4439675484018588820014629 832439153253485403752743)
    ·
      refine ⟨1248658729880228105629115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 832439153253485403752743 1248658729880228105629115)
      ·
        refine ⟨1872988094820342158443673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1248658729880228105629115 1872988094820342158443673)
        ·
          refine ⟨1404741071115256618832755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1872988094820342158443673 1404741071115256618832755)
          ·
            refine ⟨2107111606672884928249133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1404741071115256618832755 2107111606672884928249133)
            ·
              refine ⟨790166852502331848093425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2107111606672884928249133 790166852502331848093425)
              ·
                refine ⟨592625139376748886070069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 790166852502331848093425 592625139376748886070069)
                ·
                  refine ⟨55558606816570208069069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 592625139376748886070069 55558606816570208069069)
                  ·
                    rfl

theorem cell20_121725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_121725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121725 prefixEnd_121725 := by exact prefixLift 121725
  have htrace : WordTrace (prefixWord ++ tailWord_121725) baseStart_121725 baseEnd_121725 := by
    simpa [prefixWord, tailWord_121725, baseEnd_121725] using wordTrace_append hprefix tailTrace_121725
  have hstable : (prefixWord ++ tailWord_121725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121725).length < 2 ^ (prefixWord ++ tailWord_121725).sum := by decide
  have hdescent : baseEnd_121725 < baseStart_121725 := by decide
  rcases family_descends (prefixWord ++ tailWord_121725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121739 : List Nat := [1, 1, 1, 1, 4, 2, 10]
def baseStart_121739 : Nat := 118140960795 + 121739 * 2 ^ 59
def prefixEnd_121739 : Nat := 4983230072969 + 3 ^ 40 * 121739 * 2
def baseEnd_121739 : Nat := 6173888533116486844705

theorem tailTrace_121739 : CollatzResearch.WordTrace tailWord_121739 prefixEnd_121739 6173888533116486844705 := by
  unfold tailWord_121739
  simp only [CollatzResearch.WordTrace]
  refine ⟨4440186105967869211024271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2960124070645246140682847 4440186105967869211024271)
  ·
    refine ⟨6660279158951803816536407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4440186105967869211024271 6660279158951803816536407)
    ·
      refine ⟨9990418738427705724804611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6660279158951803816536407 9990418738427705724804611)
      ·
        refine ⟨14985628107641558587206917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9990418738427705724804611 14985628107641558587206917)
        ·
          refine ⟨2809805270182792235101297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14985628107641558587206917 2809805270182792235101297)
          ·
            refine ⟨2107353952637094176325973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2809805270182792235101297 2107353952637094176325973)
            ·
              refine ⟨6173888533116486844705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2107353952637094176325973 6173888533116486844705)
              ·
                rfl

theorem cell20_121739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 10].length) (baseStart_121739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121739 prefixEnd_121739 := by exact prefixLift 121739
  have htrace : WordTrace (prefixWord ++ tailWord_121739) baseStart_121739 baseEnd_121739 := by
    simpa [prefixWord, tailWord_121739, baseEnd_121739] using wordTrace_append hprefix tailTrace_121739
  have hstable : (prefixWord ++ tailWord_121739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121739).length < 2 ^ (prefixWord ++ tailWord_121739).sum := by decide
  have hdescent : baseEnd_121739 < baseStart_121739 := by decide
  rcases family_descends (prefixWord ++ tailWord_121739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121749 : List Nat := [1, 3, 2, 1, 1, 4, 3, 1, 4]
def baseStart_121749 : Nat := 118140960795 + 121749 * 2 ^ 59
def prefixEnd_121749 : Nat := 4983230072969 + 3 ^ 40 * 121749 * 2
def baseEnd_121749 : Nat := 55569561070532791268971

theorem tailTrace_121749 : CollatzResearch.WordTrace tailWord_121749 prefixEnd_121749 55569561070532791268971 := by
  unfold tailWord_121749
  simp only [CollatzResearch.WordTrace]
  refine ⟨4440550835931640918888301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2960367223954427279258867 4440550835931640918888301)
  ·
    refine ⟨1665206563474365344583113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4440550835931640918888301 1665206563474365344583113)
    ·
      refine ⟨1248904922605774008437335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1665206563474365344583113 1248904922605774008437335)
      ·
        refine ⟨1873357383908661012656003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1248904922605774008437335 1873357383908661012656003)
        ·
          refine ⟨2810036075862991518984005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1873357383908661012656003 2810036075862991518984005)
          ·
            refine ⟨526881764224310909809501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2810036075862991518984005 526881764224310909809501)
            ·
              refine ⟨197580661584116591178563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 526881764224310909809501 197580661584116591178563)
              ·
                refine ⟨296370992376174886767845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197580661584116591178563 296370992376174886767845)
                ·
                  refine ⟨55569561070532791268971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 296370992376174886767845 55569561070532791268971)
                  ·
                    rfl

theorem cell20_121749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_121749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121749 prefixEnd_121749 := by exact prefixLift 121749
  have htrace : WordTrace (prefixWord ++ tailWord_121749) baseStart_121749 baseEnd_121749 := by
    simpa [prefixWord, tailWord_121749, baseEnd_121749] using wordTrace_append hprefix tailTrace_121749
  have hstable : (prefixWord ++ tailWord_121749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121749).length < 2 ^ (prefixWord ++ tailWord_121749).sum := by decide
  have hdescent : baseEnd_121749 < baseStart_121749 := by decide
  rcases family_descends (prefixWord ++ tailWord_121749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121759 : List Nat := [1, 1, 2, 5, 2, 1, 4, 1, 3]
def baseStart_121759 : Nat := 118140960795 + 121759 * 2 ^ 59
def prefixEnd_121759 : Nat := 4983230072969 + 3 ^ 40 * 121759 * 2
def baseEnd_121759 : Nat := 55574125343017200935597

theorem tailTrace_121759 : CollatzResearch.WordTrace tailWord_121759 prefixEnd_121759 55574125343017200935597 := by
  unfold tailWord_121759
  simp only [CollatzResearch.WordTrace]
  refine ⟨4440915565895412626752331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2960610377263608417834887 4440915565895412626752331)
  ·
    refine ⟨6661373348843118940128497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4440915565895412626752331 6661373348843118940128497)
    ·
      refine ⟨4996030011632339205096373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6661373348843118940128497 4996030011632339205096373)
      ·
        refine ⟨468377813590531800477785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4996030011632339205096373 468377813590531800477785)
        ·
          refine ⟨351283360192898850358339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468377813590531800477785 351283360192898850358339)
          ·
            refine ⟨526925040289348275537509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351283360192898850358339 526925040289348275537509)
            ·
              refine ⟨98798445054252801663283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 526925040289348275537509 98798445054252801663283)
              ·
                refine ⟨148197667581379202494925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98798445054252801663283 148197667581379202494925)
                ·
                  refine ⟨55574125343017200935597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148197667581379202494925 55574125343017200935597)
                  ·
                    rfl

theorem cell20_121759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 3].length) (baseStart_121759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121759 prefixEnd_121759 := by exact prefixLift 121759
  have htrace : WordTrace (prefixWord ++ tailWord_121759) baseStart_121759 baseEnd_121759 := by
    simpa [prefixWord, tailWord_121759, baseEnd_121759] using wordTrace_append hprefix tailTrace_121759
  have hstable : (prefixWord ++ tailWord_121759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121759).length < 2 ^ (prefixWord ++ tailWord_121759).sum := by decide
  have hdescent : baseEnd_121759 < baseStart_121759 := by decide
  rcases family_descends (prefixWord ++ tailWord_121759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121794 : List Nat := [3, 5, 12]
def baseStart_121794 : Nat := 118140960795 + 121794 * 2 ^ 59
def prefixEnd_121794 : Nat := 4983230072969 + 3 ^ 40 * 121794 * 2
def baseEnd_121794 : Nat := 76255281614146275403

theorem tailTrace_121794 : CollatzResearch.WordTrace tailWord_121794 prefixEnd_121794 76255281614146275403 := by
  unfold tailWord_121794
  simp only [CollatzResearch.WordTrace]
  refine ⟨1110548030192153401069109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2961461413845742402850957 1110548030192153401069109)
  ·
    refine ⟨104113877830514381350229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1110548030192153401069109 104113877830514381350229)
    ·
      refine ⟨76255281614146275403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 12 104113877830514381350229 76255281614146275403)
      ·
        rfl

theorem cell20_121794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 12].length) (baseStart_121794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121794 prefixEnd_121794 := by exact prefixLift 121794
  have htrace : WordTrace (prefixWord ++ tailWord_121794) baseStart_121794 baseEnd_121794 := by
    simpa [prefixWord, tailWord_121794, baseEnd_121794] using wordTrace_append hprefix tailTrace_121794
  have hstable : (prefixWord ++ tailWord_121794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121794).length < 2 ^ (prefixWord ++ tailWord_121794).sum := by decide
  have hdescent : baseEnd_121794 < baseStart_121794 := by decide
  rcases family_descends (prefixWord ++ tailWord_121794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121796 : List Nat := [2, 3, 3, 3, 2, 1, 2, 2, 2]
def baseStart_121796 : Nat := 118140960795 + 121796 * 2 ^ 59
def prefixEnd_121796 : Nat := 4983230072969 + 3 ^ 40 * 121796 * 2
def baseEnd_121796 : Nat := 55591013151209516702113

theorem tailTrace_121796 : CollatzResearch.WordTrace tailWord_121796 prefixEnd_121796 55591013151209516702113 := by
  unfold tailWord_121796
  simp only [CollatzResearch.WordTrace]
  refine ⟨2221132533380683972924621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2961510044507578630566161 2221132533380683972924621)
  ·
    refine ⟨832924700017756489846733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2221132533380683972924621 832924700017756489846733)
    ·
      refine ⟨312346762506658683692525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 832924700017756489846733 312346762506658683692525)
      ·
        refine ⟨117130035939997006384697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312346762506658683692525 117130035939997006384697)
        ·
          refine ⟨87847526954997754788523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117130035939997006384697 87847526954997754788523)
          ·
            refine ⟨131771290432496632182785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87847526954997754788523 131771290432496632182785)
            ·
              refine ⟨98828467824372474137089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131771290432496632182785 98828467824372474137089)
              ·
                refine ⟨74121350868279355602817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98828467824372474137089 74121350868279355602817)
                ·
                  refine ⟨55591013151209516702113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74121350868279355602817 55591013151209516702113)
                  ·
                    rfl

theorem cell20_121796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_121796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121796 prefixEnd_121796 := by exact prefixLift 121796
  have htrace : WordTrace (prefixWord ++ tailWord_121796) baseStart_121796 baseEnd_121796 := by
    simpa [prefixWord, tailWord_121796, baseEnd_121796] using wordTrace_append hprefix tailTrace_121796
  have hstable : (prefixWord ++ tailWord_121796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121796).length < 2 ^ (prefixWord ++ tailWord_121796).sum := by decide
  have hdescent : baseEnd_121796 < baseStart_121796 := by decide
  rcases family_descends (prefixWord ++ tailWord_121796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121800 : List Nat := [2, 1, 3, 1, 5, 2, 2, 2, 2]
def baseStart_121800 : Nat := 118140960795 + 121800 * 2 ^ 59
def prefixEnd_121800 : Nat := 4983230072969 + 3 ^ 40 * 121800 * 2
def baseEnd_121800 : Nat := 55592838860203280568763

theorem tailTrace_121800 : CollatzResearch.WordTrace tailWord_121800 prefixEnd_121800 55592838860203280568763 := by
  unfold tailWord_121800
  simp only [CollatzResearch.WordTrace]
  refine ⟨2221205479373438314497427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2961607305831251085996569 2221205479373438314497427)
  ·
    refine ⟨3331808219060157471746141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2221205479373438314497427 3331808219060157471746141)
    ·
      refine ⟨1249428082147559051904803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3331808219060157471746141 1249428082147559051904803)
      ·
        refine ⟨1874142123221338577857205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1249428082147559051904803 1874142123221338577857205)
        ·
          refine ⟨175700824052000491674113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1874142123221338577857205 175700824052000491674113)
          ·
            refine ⟨131775618039000368755585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175700824052000491674113 131775618039000368755585)
            ·
              refine ⟨98831713529250276566689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131775618039000368755585 98831713529250276566689)
              ·
                refine ⟨74123785146937707425017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98831713529250276566689 74123785146937707425017)
                ·
                  refine ⟨55592838860203280568763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74123785146937707425017 55592838860203280568763)
                  ·
                    rfl

theorem cell20_121800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 2, 2].length) (baseStart_121800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121800 prefixEnd_121800 := by exact prefixLift 121800
  have htrace : WordTrace (prefixWord ++ tailWord_121800) baseStart_121800 baseEnd_121800 := by
    simpa [prefixWord, tailWord_121800, baseEnd_121800] using wordTrace_append hprefix tailTrace_121800
  have hstable : (prefixWord ++ tailWord_121800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121800).length < 2 ^ (prefixWord ++ tailWord_121800).sum := by decide
  have hdescent : baseEnd_121800 < baseStart_121800 := by decide
  rcases family_descends (prefixWord ++ tailWord_121800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121804 : List Nat := [2, 2, 1, 4, 1, 1, 3, 4, 2]
def baseStart_121804 : Nat := 118140960795 + 121804 * 2 ^ 59
def prefixEnd_121804 : Nat := 4983230072969 + 3 ^ 40 * 121804 * 2
def baseEnd_121804 : Nat := 55594664569197044435413

theorem tailTrace_121804 : CollatzResearch.WordTrace tailWord_121804 prefixEnd_121804 55594664569197044435413 := by
  unfold tailWord_121804
  simp only [CollatzResearch.WordTrace]
  refine ⟨2221278425366192656070233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2961704567154923541426977 2221278425366192656070233)
  ·
    refine ⟨1665958819024644492052675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2221278425366192656070233 1665958819024644492052675)
    ·
      refine ⟨2498938228536966738079013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1665958819024644492052675 2498938228536966738079013)
      ·
        refine ⟨468550917850681263389815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2498938228536966738079013 468550917850681263389815)
        ·
          refine ⟨702826376776021895084723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468550917850681263389815 702826376776021895084723)
          ·
            refine ⟨1054239565164032842627085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702826376776021895084723 1054239565164032842627085)
            ·
              refine ⟨395339836936512315985157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1054239565164032842627085 395339836936512315985157)
              ·
                refine ⟨74126219425596059247217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 395339836936512315985157 74126219425596059247217)
                ·
                  refine ⟨55594664569197044435413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74126219425596059247217 55594664569197044435413)
                  ·
                    rfl

theorem cell20_121804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 4, 2].length) (baseStart_121804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121804 prefixEnd_121804 := by exact prefixLift 121804
  have htrace : WordTrace (prefixWord ++ tailWord_121804) baseStart_121804 baseEnd_121804 := by
    simpa [prefixWord, tailWord_121804, baseEnd_121804] using wordTrace_append hprefix tailTrace_121804
  have hstable : (prefixWord ++ tailWord_121804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121804).length < 2 ^ (prefixWord ++ tailWord_121804).sum := by decide
  have hdescent : baseEnd_121804 < baseStart_121804 := by decide
  rcases family_descends (prefixWord ++ tailWord_121804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121808 : List Nat := [2, 1, 1, 1, 1, 2, 3, 5, 4]
def baseStart_121808 : Nat := 118140960795 + 121808 * 2 ^ 59
def prefixEnd_121808 : Nat := 4983230072969 + 3 ^ 40 * 121808 * 2
def baseEnd_121808 : Nat := 55596490278190808302063

theorem tailTrace_121808 : CollatzResearch.WordTrace tailWord_121808 prefixEnd_121808 55596490278190808302063 := by
  unfold tailWord_121808
  simp only [CollatzResearch.WordTrace]
  refine ⟨2221351371358946997643039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2961801828478595996857385 2221351371358946997643039)
  ·
    refine ⟨3332027057038420496464559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2221351371358946997643039 3332027057038420496464559)
    ·
      refine ⟨4998040585557630744696839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3332027057038420496464559 4998040585557630744696839)
      ·
        refine ⟨7497060878336446117045259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4998040585557630744696839 7497060878336446117045259)
        ·
          refine ⟨11245591317504669175567889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7497060878336446117045259 11245591317504669175567889)
          ·
            refine ⟨8434193488128501881675917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11245591317504669175567889 8434193488128501881675917)
            ·
              refine ⟨3162822558048188205628469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8434193488128501881675917 3162822558048188205628469)
              ·
                refine ⟨296514614817017644277669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3162822558048188205628469 296514614817017644277669)
                ·
                  refine ⟨55596490278190808302063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 296514614817017644277669 55596490278190808302063)
                  ·
                    rfl

theorem cell20_121808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_121808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121808 prefixEnd_121808 := by exact prefixLift 121808
  have htrace : WordTrace (prefixWord ++ tailWord_121808) baseStart_121808 baseEnd_121808 := by
    simpa [prefixWord, tailWord_121808, baseEnd_121808] using wordTrace_append hprefix tailTrace_121808
  have hstable : (prefixWord ++ tailWord_121808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121808).length < 2 ^ (prefixWord ++ tailWord_121808).sum := by decide
  have hdescent : baseEnd_121808 < baseStart_121808 := by decide
  rcases family_descends (prefixWord ++ tailWord_121808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121815 : List Nat := [1, 1, 3, 2, 1, 1, 2, 9]
def baseStart_121815 : Nat := 118140960795 + 121815 * 2 ^ 59
def prefixEnd_121815 : Nat := 4983230072969 + 3 ^ 40 * 121815 * 2
def baseEnd_121815 : Nat := 18533228422976631689567

theorem tailTrace_121815 : CollatzResearch.WordTrace tailWord_121815 prefixEnd_121815 18533228422976631689567 := by
  unfold tailWord_121815
  simp only [CollatzResearch.WordTrace]
  refine ⟨4442958053692534190790899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2961972035795022793860599 4442958053692534190790899)
  ·
    refine ⟨6664437080538801286186349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4442958053692534190790899 6664437080538801286186349)
    ·
      refine ⟨2499163905202050482319881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6664437080538801286186349 2499163905202050482319881)
      ·
        refine ⟨1874372928901537861739911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2499163905202050482319881 1874372928901537861739911)
        ·
          refine ⟨2811559393352306792609867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1874372928901537861739911 2811559393352306792609867)
          ·
            refine ⟨4217339090028460188914801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2811559393352306792609867 4217339090028460188914801)
            ·
              refine ⟨3163004317521345141686101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4217339090028460188914801 3163004317521345141686101)
              ·
                refine ⟨18533228422976631689567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3163004317521345141686101 18533228422976631689567)
                ·
                  rfl

theorem cell20_121815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 9].length) (baseStart_121815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121815 prefixEnd_121815 := by exact prefixLift 121815
  have htrace : WordTrace (prefixWord ++ tailWord_121815) baseStart_121815 baseEnd_121815 := by
    simpa [prefixWord, tailWord_121815, baseEnd_121815] using wordTrace_append hprefix tailTrace_121815
  have hstable : (prefixWord ++ tailWord_121815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121815).length < 2 ^ (prefixWord ++ tailWord_121815).sum := by decide
  have hdescent : baseEnd_121815 < baseStart_121815 := by decide
  rcases family_descends (prefixWord ++ tailWord_121815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121818 : List Nat := [3, 1, 1, 2, 4, 1, 2, 3, 3]
def baseStart_121818 : Nat := 118140960795 + 121818 * 2 ^ 59
def prefixEnd_121818 : Nat := 4983230072969 + 3 ^ 40 * 121818 * 2
def baseEnd_121818 : Nat := 55601054550675217968689

theorem tailTrace_121818 : CollatzResearch.WordTrace tailWord_121818 prefixEnd_121818 55601054550675217968689 := by
  unfold tailWord_121818
  simp only [CollatzResearch.WordTrace]
  refine ⟨1110766868170416425787527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2962044981787777135433405 1110766868170416425787527)
  ·
    refine ⟨1666150302255624638681291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1110766868170416425787527 1666150302255624638681291)
    ·
      refine ⟨2499225453383436958021937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1666150302255624638681291 2499225453383436958021937)
      ·
        refine ⟨1874419090037577718516453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2499225453383436958021937 1874419090037577718516453)
        ·
          refine ⟨351453579382045822221835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1874419090037577718516453 351453579382045822221835)
          ·
            refine ⟨527180369073068733332753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351453579382045822221835 527180369073068733332753)
            ·
              refine ⟨395385276804801549999565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 527180369073068733332753 395385276804801549999565)
              ·
                refine ⟨148269478801800581249837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 395385276804801549999565 148269478801800581249837)
                ·
                  refine ⟨55601054550675217968689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148269478801800581249837 55601054550675217968689)
                  ·
                    rfl

theorem cell20_121818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_121818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121818 prefixEnd_121818 := by exact prefixLift 121818
  have htrace : WordTrace (prefixWord ++ tailWord_121818) baseStart_121818 baseEnd_121818 := by
    simpa [prefixWord, tailWord_121818, baseEnd_121818] using wordTrace_append hprefix tailTrace_121818
  have hstable : (prefixWord ++ tailWord_121818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121818).length < 2 ^ (prefixWord ++ tailWord_121818).sum := by decide
  have hdescent : baseEnd_121818 < baseStart_121818 := by decide
  rcases family_descends (prefixWord ++ tailWord_121818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121863 : List Nat := [1, 1, 4, 3, 1, 1, 4, 1, 4]
def baseStart_121863 : Nat := 118140960795 + 121863 * 2 ^ 59
def prefixEnd_121863 : Nat := 4983230072969 + 3 ^ 40 * 121863 * 2
def baseEnd_121863 : Nat := 55621593776855061468505

theorem tailTrace_121863 : CollatzResearch.WordTrace tailWord_121863 prefixEnd_121863 55621593776855061468505 := by
  unfold tailWord_121863
  simp only [CollatzResearch.WordTrace]
  refine ⟨4444708757518638388538243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2963139171679092259025495 4444708757518638388538243)
  ·
    refine ⟨6667063136277957582807365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4444708757518638388538243 6667063136277957582807365)
    ·
      refine ⟨1250074338052117046776381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6667063136277957582807365 1250074338052117046776381)
      ·
        refine ⟨468777876769543892541143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1250074338052117046776381 468777876769543892541143)
        ·
          refine ⟨703166815154315838811715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468777876769543892541143 703166815154315838811715)
          ·
            refine ⟨1054750222731473758217573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703166815154315838811715 1054750222731473758217573)
            ·
              refine ⟨197765666762151329665795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1054750222731473758217573 197765666762151329665795)
              ·
                refine ⟨296648500143226994498693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197765666762151329665795 296648500143226994498693)
                ·
                  refine ⟨55621593776855061468505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 296648500143226994498693 55621593776855061468505)
                  ·
                    rfl

theorem cell20_121863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 4].length) (baseStart_121863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121863 prefixEnd_121863 := by exact prefixLift 121863
  have htrace : WordTrace (prefixWord ++ tailWord_121863) baseStart_121863 baseEnd_121863 := by
    simpa [prefixWord, tailWord_121863, baseEnd_121863] using wordTrace_append hprefix tailTrace_121863
  have hstable : (prefixWord ++ tailWord_121863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121863).length < 2 ^ (prefixWord ++ tailWord_121863).sum := by decide
  have hdescent : baseEnd_121863 < baseStart_121863 := by decide
  rcases family_descends (prefixWord ++ tailWord_121863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121887 : List Nat := [1, 1, 2, 4, 1, 5, 2, 4]
def baseStart_121887 : Nat := 118140960795 + 121887 * 2 ^ 59
def prefixEnd_121887 : Nat := 4983230072969 + 3 ^ 40 * 121887 * 2
def baseEnd_121887 : Nat := 18544182676939214889469

theorem tailTrace_121887 : CollatzResearch.WordTrace tailWord_121887 prefixEnd_121887 18544182676939214889469 := by
  unfold tailWord_121887
  simp only [CollatzResearch.WordTrace]
  refine ⟨4445584109431690487411915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2963722739621126991607943 4445584109431690487411915)
  ·
    refine ⟨6668376164147535731117873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4445584109431690487411915 6668376164147535731117873)
    ·
      refine ⟨5001282123110651798338405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6668376164147535731117873 5001282123110651798338405)
      ·
        refine ⟨937740398083247212188451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5001282123110651798338405 937740398083247212188451)
        ·
          refine ⟨1406610597124870818282677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 937740398083247212188451 1406610597124870818282677)
          ·
            refine ⟨131869743480456639214001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1406610597124870818282677 131869743480456639214001)
            ·
              refine ⟨98902307610342479410501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131869743480456639214001 98902307610342479410501)
              ·
                refine ⟨18544182676939214889469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98902307610342479410501 18544182676939214889469)
                ·
                  rfl

theorem cell20_121887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 4].length) (baseStart_121887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121887 prefixEnd_121887 := by exact prefixLift 121887
  have htrace : WordTrace (prefixWord ++ tailWord_121887) baseStart_121887 baseEnd_121887 := by
    simpa [prefixWord, tailWord_121887, baseEnd_121887] using wordTrace_append hprefix tailTrace_121887
  have hstable : (prefixWord ++ tailWord_121887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121887).length < 2 ^ (prefixWord ++ tailWord_121887).sum := by decide
  have hdescent : baseEnd_121887 < baseStart_121887 := by decide
  rcases family_descends (prefixWord ++ tailWord_121887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121918 : List Nat := [4, 2, 1, 3, 1, 1, 3, 1, 4]
def baseStart_121918 : Nat := 118140960795 + 121918 * 2 ^ 59
def prefixEnd_121918 : Nat := 4983230072969 + 3 ^ 40 * 121918 * 2
def baseEnd_121918 : Nat := 55646697275519314634947

theorem tailTrace_121918 : CollatzResearch.WordTrace tailWord_121918 prefixEnd_121918 55646697275519314634947 := by
  unfold tailWord_121918
  simp only [CollatzResearch.WordTrace]
  refine ⟨555839346539922847723801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2964476514879588521193605 555839346539922847723801)
  ·
    refine ⟨416879509904942135792851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 555839346539922847723801 416879509904942135792851)
    ·
      refine ⟨625319264857413203689277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416879509904942135792851 625319264857413203689277)
      ·
        refine ⟨234494724321529951383479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 625319264857413203689277 234494724321529951383479)
        ·
          refine ⟨351742086482294927075219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234494724321529951383479 351742086482294927075219)
          ·
            refine ⟨527613129723442390612829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351742086482294927075219 527613129723442390612829)
            ·
              refine ⟨197854923646290896479811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 527613129723442390612829 197854923646290896479811)
              ·
                refine ⟨296782385469436344719717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197854923646290896479811 296782385469436344719717)
                ·
                  refine ⟨55646697275519314634947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 296782385469436344719717 55646697275519314634947)
                  ·
                    rfl

theorem cell20_121918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_121918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121918 prefixEnd_121918 := by exact prefixLift 121918
  have htrace : WordTrace (prefixWord ++ tailWord_121918) baseStart_121918 baseEnd_121918 := by
    simpa [prefixWord, tailWord_121918, baseEnd_121918] using wordTrace_append hprefix tailTrace_121918
  have hstable : (prefixWord ++ tailWord_121918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121918).length < 2 ^ (prefixWord ++ tailWord_121918).sum := by decide
  have hdescent : baseEnd_121918 < baseStart_121918 := by decide
  rcases family_descends (prefixWord ++ tailWord_121918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121970 : List Nat := [3, 2, 1, 2, 2, 1, 4, 2, 3]
def baseStart_121970 : Nat := 118140960795 + 121970 * 2 ^ 59
def prefixEnd_121970 : Nat := 4983230072969 + 3 ^ 40 * 121970 * 2
def baseEnd_121970 : Nat := 55670431492438244901401

theorem tailTrace_121970 : CollatzResearch.WordTrace tailWord_121970 prefixEnd_121970 55670431492438244901401 := by
  unfold tailWord_121970
  simp only [CollatzResearch.WordTrace]
  refine ⟨1112152842032748915670841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2965740912087330441788909 1112152842032748915670841)
  ·
    refine ⟨834114631524561686753131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1112152842032748915670841 834114631524561686753131)
    ·
      refine ⟨1251171947286842530129697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 834114631524561686753131 1251171947286842530129697)
      ·
        refine ⟨938378960465131897597273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1251171947286842530129697 938378960465131897597273)
        ·
          refine ⟨703784220348848923197955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 938378960465131897597273 703784220348848923197955)
          ·
            refine ⟨1055676330523273384796933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703784220348848923197955 1055676330523273384796933)
            ·
              refine ⟨197939311973113759649425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1055676330523273384796933 197939311973113759649425)
              ·
                refine ⟨148454483979835319737069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197939311973113759649425 148454483979835319737069)
                ·
                  refine ⟨55670431492438244901401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148454483979835319737069 55670431492438244901401)
                  ·
                    rfl

theorem cell20_121970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_121970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121970 prefixEnd_121970 := by exact prefixLift 121970
  have htrace : WordTrace (prefixWord ++ tailWord_121970) baseStart_121970 baseEnd_121970 := by
    simpa [prefixWord, tailWord_121970, baseEnd_121970] using wordTrace_append hprefix tailTrace_121970
  have hstable : (prefixWord ++ tailWord_121970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121970).length < 2 ^ (prefixWord ++ tailWord_121970).sum := by decide
  have hdescent : baseEnd_121970 < baseStart_121970 := by decide
  rcases family_descends (prefixWord ++ tailWord_121970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122077 : List Nat := [1, 4, 3, 2, 2, 2, 6]
def baseStart_122077 : Nat := 118140960795 + 122077 * 2 ^ 59
def prefixEnd_122077 : Nat := 4983230072969 + 3 ^ 40 * 122077 * 2
def baseEnd_122077 : Nat := 6191029912002380926033

theorem tailTrace_122077 : CollatzResearch.WordTrace tailWord_122077 prefixEnd_122077 6191029912002380926033 := by
  unfold tailWord_122077
  simp only [CollatzResearch.WordTrace]
  refine ⟨4452513978743352936828485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2968342652495568624552323 4452513978743352936828485)
  ·
    refine ⟨834846371014378675655341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4452513978743352936828485 834846371014378675655341)
    ·
      refine ⟨313067389130392003370753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 834846371014378675655341 313067389130392003370753)
      ·
        refine ⟨234800541847794002528065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313067389130392003370753 234800541847794002528065)
        ·
          refine ⟨176100406385845501896049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234800541847794002528065 176100406385845501896049)
          ·
            refine ⟨132075304789384126422037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176100406385845501896049 132075304789384126422037)
            ·
              refine ⟨6191029912002380926033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 132075304789384126422037 6191029912002380926033)
              ·
                rfl

theorem cell20_122077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 6].length) (baseStart_122077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122077 prefixEnd_122077 := by exact prefixLift 122077
  have htrace : WordTrace (prefixWord ++ tailWord_122077) baseStart_122077 baseEnd_122077 := by
    simpa [prefixWord, tailWord_122077, baseEnd_122077] using wordTrace_append hprefix tailTrace_122077
  have hstable : (prefixWord ++ tailWord_122077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122077).length < 2 ^ (prefixWord ++ tailWord_122077).sum := by decide
  have hdescent : baseEnd_122077 < baseStart_122077 := by decide
  rcases family_descends (prefixWord ++ tailWord_122077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122081 : List Nat := [1, 2, 3, 1, 3, 2, 8]
def baseStart_122081 : Nat := 118140960795 + 122081 * 2 ^ 59
def prefixEnd_122081 : Nat := 4983230072969 + 3 ^ 40 * 122081 * 2
def baseEnd_122081 : Nat := 6191232768557243577883

theorem tailTrace_122081 : CollatzResearch.WordTrace tailWord_122081 prefixEnd_122081 6191232768557243577883 := by
  unfold tailWord_122081
  simp only [CollatzResearch.WordTrace]
  refine ⟨4452659870728861619974097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2968439913819241079982731 4452659870728861619974097)
  ·
    refine ⟨3339494903046646214980573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4452659870728861619974097 3339494903046646214980573)
    ·
      refine ⟨1252310588642492330617715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3339494903046646214980573 1252310588642492330617715)
      ·
        refine ⟨1878465882963738495926573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1252310588642492330617715 1878465882963738495926573)
        ·
          refine ⟨704424706111401935972465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1878465882963738495926573 704424706111401935972465)
          ·
            refine ⟨528318529583551451979349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 704424706111401935972465 528318529583551451979349)
            ·
              refine ⟨6191232768557243577883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 528318529583551451979349 6191232768557243577883)
              ·
                rfl

theorem cell20_122081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 8].length) (baseStart_122081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122081 prefixEnd_122081 := by exact prefixLift 122081
  have htrace : WordTrace (prefixWord ++ tailWord_122081) baseStart_122081 baseEnd_122081 := by
    simpa [prefixWord, tailWord_122081, baseEnd_122081] using wordTrace_append hprefix tailTrace_122081
  have hstable : (prefixWord ++ tailWord_122081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122081).length < 2 ^ (prefixWord ++ tailWord_122081).sum := by decide
  have hdescent : baseEnd_122081 < baseStart_122081 := by decide
  rcases family_descends (prefixWord ++ tailWord_122081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122087 : List Nat := [1, 1, 5, 3, 3, 1, 1, 1, 4]
def baseStart_122087 : Nat := 118140960795 + 122087 * 2 ^ 59
def prefixEnd_122087 : Nat := 4983230072969 + 3 ^ 40 * 122087 * 2
def baseEnd_122087 : Nat := 55723833480505838000923

theorem tailTrace_122087 : CollatzResearch.WordTrace tailWord_122087 prefixEnd_122087 55723833480505838000923 := by
  unfold tailWord_122087
  simp only [CollatzResearch.WordTrace]
  refine ⟨4452878708707124644692515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2968585805804749763128343 4452878708707124644692515)
  ·
    refine ⟨6679318063060686967038773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4452878708707124644692515 6679318063060686967038773)
    ·
      refine ⟨626186068411939403159885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6679318063060686967038773 626186068411939403159885)
      ·
        refine ⟨234819775654477276184957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 626186068411939403159885 234819775654477276184957)
        ·
          refine ⟨88057415870428978569359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234819775654477276184957 88057415870428978569359)
          ·
            refine ⟨132086123805643467854039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88057415870428978569359 132086123805643467854039)
            ·
              refine ⟨198129185708465201781059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132086123805643467854039 198129185708465201781059)
              ·
                refine ⟨297193778562697802671589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198129185708465201781059 297193778562697802671589)
                ·
                  refine ⟨55723833480505838000923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 297193778562697802671589 55723833480505838000923)
                  ·
                    rfl

theorem cell20_122087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 4].length) (baseStart_122087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122087 prefixEnd_122087 := by exact prefixLift 122087
  have htrace : WordTrace (prefixWord ++ tailWord_122087) baseStart_122087 baseEnd_122087 := by
    simpa [prefixWord, tailWord_122087, baseEnd_122087] using wordTrace_append hprefix tailTrace_122087
  have hstable : (prefixWord ++ tailWord_122087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122087).length < 2 ^ (prefixWord ++ tailWord_122087).sum := by decide
  have hdescent : baseEnd_122087 < baseStart_122087 := by decide
  rcases family_descends (prefixWord ++ tailWord_122087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122091 : List Nat := [1, 1, 1, 1, 2, 8, 1, 1, 4]
def baseStart_122091 : Nat := 118140960795 + 122091 * 2 ^ 59
def prefixEnd_122091 : Nat := 4983230072969 + 3 ^ 40 * 122091 * 2
def baseEnd_122091 : Nat := 55725659189499601867573

theorem tailTrace_122091 : CollatzResearch.WordTrace tailWord_122091 prefixEnd_122091 55725659189499601867573 := by
  unfold tailWord_122091
  simp only [CollatzResearch.WordTrace]
  refine ⟨4453024600692633327838127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2968683067128422218558751 4453024600692633327838127)
  ·
    refine ⟨6679536901038949991757191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4453024600692633327838127 6679536901038949991757191)
    ·
      refine ⟨10019305351558424987635787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6679536901038949991757191 10019305351558424987635787)
      ·
        refine ⟨15028958027337637481453681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10019305351558424987635787 15028958027337637481453681)
        ·
          refine ⟨11271718520503228111090261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15028958027337637481453681 11271718520503228111090261)
          ·
            refine ⟨132090451412147204426839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 11271718520503228111090261 132090451412147204426839)
            ·
              refine ⟨198135677118220806640259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132090451412147204426839 198135677118220806640259)
              ·
                refine ⟨297203515677331209960389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198135677118220806640259 297203515677331209960389)
                ·
                  refine ⟨55725659189499601867573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 297203515677331209960389 55725659189499601867573)
                  ·
                    rfl

theorem cell20_122091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 4].length) (baseStart_122091 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122091 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122091 prefixEnd_122091 := by exact prefixLift 122091
  have htrace : WordTrace (prefixWord ++ tailWord_122091) baseStart_122091 baseEnd_122091 := by
    simpa [prefixWord, tailWord_122091, baseEnd_122091] using wordTrace_append hprefix tailTrace_122091
  have hstable : (prefixWord ++ tailWord_122091).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122091).length < 2 ^ (prefixWord ++ tailWord_122091).sum := by decide
  have hdescent : baseEnd_122091 < baseStart_122091 := by decide
  rcases family_descends (prefixWord ++ tailWord_122091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122105 : List Nat := [1, 2, 1, 3, 1, 1, 5, 3, 3]
def baseStart_122105 : Nat := 118140960795 + 122105 * 2 ^ 59
def prefixEnd_122105 : Nat := 4983230072969 + 3 ^ 40 * 122105 * 2
def baseEnd_122105 : Nat := 55732049170977775400849

theorem tailTrace_122105 : CollatzResearch.WordTrace tailWord_122105 prefixEnd_122105 55732049170977775400849 := by
  unfold tailWord_122105
  simp only [CollatzResearch.WordTrace]
  refine ⟨4453535222641913718847769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2969023481761275812565179 4453535222641913718847769)
  ·
    refine ⟨3340151416981435289135827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4453535222641913718847769 3340151416981435289135827)
    ·
      refine ⟨5010227125472152933703741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3340151416981435289135827 5010227125472152933703741)
      ·
        refine ⟨1878835172052057350138903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5010227125472152933703741 1878835172052057350138903)
        ·
          refine ⟨2818252758078086025208355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1878835172052057350138903 2818252758078086025208355)
          ·
            refine ⟨4227379137117129037812533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2818252758078086025208355 4227379137117129037812533)
            ·
              refine ⟨396316794104730847294925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4227379137117129037812533 396316794104730847294925)
              ·
                refine ⟨148618797789274067735597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 396316794104730847294925 148618797789274067735597)
                ·
                  refine ⟨55732049170977775400849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148618797789274067735597 55732049170977775400849)
                  ·
                    rfl

theorem cell20_122105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 3].length) (baseStart_122105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122105 prefixEnd_122105 := by exact prefixLift 122105
  have htrace : WordTrace (prefixWord ++ tailWord_122105) baseStart_122105 baseEnd_122105 := by
    simpa [prefixWord, tailWord_122105, baseEnd_122105] using wordTrace_append hprefix tailTrace_122105
  have hstable : (prefixWord ++ tailWord_122105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122105).length < 2 ^ (prefixWord ++ tailWord_122105).sum := by decide
  have hdescent : baseEnd_122105 < baseStart_122105 := by decide
  rcases family_descends (prefixWord ++ tailWord_122105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122129 : List Nat := [1, 2, 2, 1, 1, 4, 2, 5, 2]
def baseStart_122129 : Nat := 118140960795 + 122129 * 2 ^ 59
def prefixEnd_122129 : Nat := 4983230072969 + 3 ^ 40 * 122129 * 2
def baseEnd_122129 : Nat := 55743003424940358600751

theorem tailTrace_122129 : CollatzResearch.WordTrace tailWord_122129 prefixEnd_122129 55743003424940358600751 := by
  unfold tailWord_122129
  simp only [CollatzResearch.WordTrace]
  refine ⟨4454410574554965817721441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2969607049703310545147627 4454410574554965817721441)
  ·
    refine ⟨3340807930916224363291081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4454410574554965817721441 3340807930916224363291081)
    ·
      refine ⟨2505605948187168272468311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3340807930916224363291081 2505605948187168272468311)
      ·
        refine ⟨3758408922280752408702467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2505605948187168272468311 3758408922280752408702467)
        ·
          refine ⟨5637613383421128613053701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3758408922280752408702467 5637613383421128613053701)
          ·
            refine ⟨1057052509391461614947569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5637613383421128613053701 1057052509391461614947569)
            ·
              refine ⟨792789382043596211210677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1057052509391461614947569 792789382043596211210677)
              ·
                refine ⟨74324004566587144801001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 792789382043596211210677 74324004566587144801001)
                ·
                  refine ⟨55743003424940358600751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74324004566587144801001 55743003424940358600751)
                  ·
                    rfl

theorem cell20_122129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 5, 2].length) (baseStart_122129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122129 prefixEnd_122129 := by exact prefixLift 122129
  have htrace : WordTrace (prefixWord ++ tailWord_122129) baseStart_122129 baseEnd_122129 := by
    simpa [prefixWord, tailWord_122129, baseEnd_122129] using wordTrace_append hprefix tailTrace_122129
  have hstable : (prefixWord ++ tailWord_122129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122129).length < 2 ^ (prefixWord ++ tailWord_122129).sum := by decide
  have hdescent : baseEnd_122129 < baseStart_122129 := by decide
  rcases family_descends (prefixWord ++ tailWord_122129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122142 : List Nat := [4, 3, 2, 1, 2, 1, 1, 4, 2]
def baseStart_122142 : Nat := 118140960795 + 122142 * 2 ^ 59
def prefixEnd_122142 : Nat := 4983230072969 + 3 ^ 40 * 122142 * 2
def baseEnd_122142 : Nat := 55748936979170091167365

theorem tailTrace_122142 : CollatzResearch.WordTrace tailWord_122142 prefixEnd_122142 55748936979170091167365 := by
  unfold tailWord_122142
  simp only [CollatzResearch.WordTrace]
  refine ⟨556860590438483629743085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2969923149005246025296453 556860590438483629743085)
  ·
    refine ⟨208822721414431361153657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 556860590438483629743085 208822721414431361153657)
    ·
      refine ⟨156617041060823520865243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208822721414431361153657 156617041060823520865243)
      ·
        refine ⟨234925561591235281297865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156617041060823520865243 234925561591235281297865)
        ·
          refine ⟨176194171193426460973399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234925561591235281297865 176194171193426460973399)
          ·
            refine ⟨264291256790139691460099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176194171193426460973399 264291256790139691460099)
            ·
              refine ⟨396436885185209537190149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264291256790139691460099 396436885185209537190149)
              ·
                refine ⟨74331915972226788223153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 396436885185209537190149 74331915972226788223153)
                ·
                  refine ⟨55748936979170091167365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74331915972226788223153 55748936979170091167365)
                  ·
                    rfl

theorem cell20_122142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_122142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122142 prefixEnd_122142 := by exact prefixLift 122142
  have htrace : WordTrace (prefixWord ++ tailWord_122142) baseStart_122142 baseEnd_122142 := by
    simpa [prefixWord, tailWord_122142, baseEnd_122142] using wordTrace_append hprefix tailTrace_122142
  have hstable : (prefixWord ++ tailWord_122142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122142).length < 2 ^ (prefixWord ++ tailWord_122142).sum := by decide
  have hdescent : baseEnd_122142 < baseStart_122142 := by decide
  rcases family_descends (prefixWord ++ tailWord_122142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122215 : List Nat := [1, 1, 5, 1, 4, 1, 3, 1, 3]
def baseStart_122215 : Nat := 118140960795 + 122215 * 2 ^ 59
def prefixEnd_122215 : Nat := 4983230072969 + 3 ^ 40 * 122215 * 2
def baseEnd_122215 : Nat := 55782256168306281733733

theorem tailTrace_122215 : CollatzResearch.WordTrace tailWord_122215 prefixEnd_122215 55782256168306281733733 := by
  unfold tailWord_122215
  simp only [CollatzResearch.WordTrace]
  refine ⟨4457547252243402505352099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2971698168162268336901399 4457547252243402505352099)
  ·
    refine ⟨6686320878365103758028149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4457547252243402505352099 6686320878365103758028149)
    ·
      refine ⟨626842582346728477315139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6686320878365103758028149 626842582346728477315139)
      ·
        refine ⟨940263873520092715972709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626842582346728477315139 940263873520092715972709)
        ·
          refine ⟨176299476285017384244883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 940263873520092715972709 176299476285017384244883)
          ·
            refine ⟨264449214427526076367325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176299476285017384244883 264449214427526076367325)
            ·
              refine ⟨99168455410322278637747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264449214427526076367325 99168455410322278637747)
              ·
                refine ⟨148752683115483417956621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99168455410322278637747 148752683115483417956621)
                ·
                  refine ⟨55782256168306281733733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148752683115483417956621 55782256168306281733733)
                  ·
                    rfl

theorem cell20_122215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 3].length) (baseStart_122215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122215 prefixEnd_122215 := by exact prefixLift 122215
  have htrace : WordTrace (prefixWord ++ tailWord_122215) baseStart_122215 baseEnd_122215 := by
    simpa [prefixWord, tailWord_122215, baseEnd_122215] using wordTrace_append hprefix tailTrace_122215
  have hstable : (prefixWord ++ tailWord_122215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122215).length < 2 ^ (prefixWord ++ tailWord_122215).sum := by decide
  have hdescent : baseEnd_122215 < baseStart_122215 := by decide
  rcases family_descends (prefixWord ++ tailWord_122215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122226 : List Nat := [3, 2, 1, 2, 1, 2, 1, 4, 4]
def baseStart_122226 : Nat := 118140960795 + 122226 * 2 ^ 59
def prefixEnd_122226 : Nat := 4983230072969 + 3 ^ 40 * 122226 * 2
def baseEnd_122226 : Nat := 55787276868039132367021

theorem tailTrace_122226 : CollatzResearch.WordTrace tailWord_122226 prefixEnd_122226 55787276868039132367021 := by
  unfold tailWord_122226
  simp only [CollatzResearch.WordTrace]
  refine ⟨1114487113800887846000633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2971965636802367589335021 1114487113800887846000633)
  ·
    refine ⟨835865335350665884500475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1114487113800887846000633 835865335350665884500475)
    ·
      refine ⟨1253798003025998826750713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 835865335350665884500475 1253798003025998826750713)
      ·
        refine ⟨940348502269499120063035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1253798003025998826750713 940348502269499120063035)
        ·
          refine ⟨1410522753404248680094553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 940348502269499120063035 1410522753404248680094553)
          ·
            refine ⟨1057892065053186510070915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1410522753404248680094553 1057892065053186510070915)
            ·
              refine ⟨1586838097579779765106373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1057892065053186510070915 1586838097579779765106373)
              ·
                refine ⟨297532143296208705957445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1586838097579779765106373 297532143296208705957445)
                ·
                  refine ⟨55787276868039132367021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 297532143296208705957445 55787276868039132367021)
                  ·
                    rfl

theorem cell20_122226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_122226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122226 prefixEnd_122226 := by exact prefixLift 122226
  have htrace : WordTrace (prefixWord ++ tailWord_122226) baseStart_122226 baseEnd_122226 := by
    simpa [prefixWord, tailWord_122226, baseEnd_122226] using wordTrace_append hprefix tailTrace_122226
  have hstable : (prefixWord ++ tailWord_122226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122226).length < 2 ^ (prefixWord ++ tailWord_122226).sum := by decide
  have hdescent : baseEnd_122226 < baseStart_122226 := by decide
  rcases family_descends (prefixWord ++ tailWord_122226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122260 : List Nat := [2, 4, 2, 1, 2, 3, 1, 1, 4]
def baseStart_122260 : Nat := 118140960795 + 122260 * 2 ^ 59
def prefixEnd_122260 : Nat := 4983230072969 + 3 ^ 40 * 122260 * 2
def baseEnd_122260 : Nat := 55802795394486125233549

theorem tailTrace_122260 : CollatzResearch.WordTrace tailWord_122260 prefixEnd_122260 55802795394486125233549 := by
  unfold tailWord_122260
  simp only [CollatzResearch.WordTrace]
  refine ⟨2229594268540187595370117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2972792358053583460493489 2229594268540187595370117)
  ·
    refine ⟨418048925351285174131897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2229594268540187595370117 418048925351285174131897)
    ·
      refine ⟨313536694013463880598923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418048925351285174131897 313536694013463880598923)
      ·
        refine ⟨470305041020195820898385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313536694013463880598923 470305041020195820898385)
        ·
          refine ⟨352728780765146865673789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470305041020195820898385 352728780765146865673789)
          ·
            refine ⟨132273292786930074627671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352728780765146865673789 132273292786930074627671)
            ·
              refine ⟨198409939180395111941507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132273292786930074627671 198409939180395111941507)
              ·
                refine ⟨297614908770592667912261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198409939180395111941507 297614908770592667912261)
                ·
                  refine ⟨55802795394486125233549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 297614908770592667912261 55802795394486125233549)
                  ·
                    rfl

theorem cell20_122260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_122260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122260 prefixEnd_122260 := by exact prefixLift 122260
  have htrace : WordTrace (prefixWord ++ tailWord_122260) baseStart_122260 baseEnd_122260 := by
    simpa [prefixWord, tailWord_122260, baseEnd_122260] using wordTrace_append hprefix tailTrace_122260
  have hstable : (prefixWord ++ tailWord_122260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122260).length < 2 ^ (prefixWord ++ tailWord_122260).sum := by decide
  have hdescent : baseEnd_122260 < baseStart_122260 := by decide
  rcases family_descends (prefixWord ++ tailWord_122260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122271 : List Nat := [1, 1, 2, 5, 1, 2, 1, 7]
def baseStart_122271 : Nat := 118140960795 + 122271 * 2 ^ 59
def prefixEnd_122271 : Nat := 4983230072969 + 3 ^ 40 * 122271 * 2
def baseEnd_122271 : Nat := 18602605364739658622279

theorem tailTrace_122271 : CollatzResearch.WordTrace tailWord_122271 prefixEnd_122271 18602605364739658622279 := by
  unfold tailWord_122271
  simp only [CollatzResearch.WordTrace]
  refine ⟨4459589740040524069390667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2973059826693682712927111 4459589740040524069390667)
  ·
    refine ⟨6689384610060786104086001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4459589740040524069390667 6689384610060786104086001)
    ·
      refine ⟨5017038457545589578064501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6689384610060786104086001 5017038457545589578064501)
      ·
        refine ⟨470347355394899022943547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5017038457545589578064501 470347355394899022943547)
        ·
          refine ⟨705521033092348534415321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470347355394899022943547 705521033092348534415321)
          ·
            refine ⟨529140774819261400811491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 705521033092348534415321 529140774819261400811491)
            ·
              refine ⟨793711162228892101217237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 529140774819261400811491 793711162228892101217237)
              ·
                refine ⟨18602605364739658622279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 793711162228892101217237 18602605364739658622279)
                ·
                  rfl

theorem cell20_122271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 7].length) (baseStart_122271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122271 prefixEnd_122271 := by exact prefixLift 122271
  have htrace : WordTrace (prefixWord ++ tailWord_122271) baseStart_122271 baseEnd_122271 := by
    simpa [prefixWord, tailWord_122271, baseEnd_122271] using wordTrace_append hprefix tailTrace_122271
  have hstable : (prefixWord ++ tailWord_122271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122271).length < 2 ^ (prefixWord ++ tailWord_122271).sum := by decide
  have hdescent : baseEnd_122271 < baseStart_122271 := by decide
  rcases family_descends (prefixWord ++ tailWord_122271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122274 : List Nat := [3, 3, 1, 2, 1, 3, 1, 3, 3]
def baseStart_122274 : Nat := 118140960795 + 122274 * 2 ^ 59
def prefixEnd_122274 : Nat := 4983230072969 + 3 ^ 40 * 122274 * 2
def baseEnd_122274 : Nat := 55809185375964298766825

theorem tailTrace_122274 : CollatzResearch.WordTrace tailWord_122274 prefixEnd_122274 55809185375964298766825 := by
  unfold tailWord_122274
  simp only [CollatzResearch.WordTrace]
  refine ⟨1114924789757413895437469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2973132772686437054499917 1114924789757413895437469)
  ·
    refine ⟨418096796159030210789051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1114924789757413895437469 418096796159030210789051)
    ·
      refine ⟨627145194238545316183577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418096796159030210789051 627145194238545316183577)
      ·
        refine ⟨470358895678908987137683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 627145194238545316183577 470358895678908987137683)
        ·
          refine ⟨705538343518363480706525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470358895678908987137683 705538343518363480706525)
          ·
            refine ⟨264576878819386305264947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 705538343518363480706525 264576878819386305264947)
            ·
              refine ⟨396865318229079457897421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264576878819386305264947 396865318229079457897421)
              ·
                refine ⟨148824494335904796711533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 396865318229079457897421 148824494335904796711533)
                ·
                  refine ⟨55809185375964298766825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148824494335904796711533 55809185375964298766825)
                  ·
                    rfl

theorem cell20_122274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_122274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122274 prefixEnd_122274 := by exact prefixLift 122274
  have htrace : WordTrace (prefixWord ++ tailWord_122274) baseStart_122274 baseEnd_122274 := by
    simpa [prefixWord, tailWord_122274, baseEnd_122274] using wordTrace_append hprefix tailTrace_122274
  have hstable : (prefixWord ++ tailWord_122274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122274).length < 2 ^ (prefixWord ++ tailWord_122274).sum := by decide
  have hdescent : baseEnd_122274 < baseStart_122274 := by decide
  rcases family_descends (prefixWord ++ tailWord_122274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122361 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 8]
def baseStart_122361 : Nat := 118140960795 + 122361 * 2 ^ 59
def prefixEnd_122361 : Nat := 4983230072969 + 3 ^ 40 * 122361 * 2
def baseEnd_122361 : Nat := 55848894546578662866469

theorem tailTrace_122361 : CollatzResearch.WordTrace tailWord_122361 prefixEnd_122361 55848894546578662866469 := by
  unfold tailWord_122361
  simp only [CollatzResearch.WordTrace]
  refine ⟨4462872309714469440166937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2975248206476312960111291 4462872309714469440166937)
  ·
    refine ⟨3347154232285852080125203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4462872309714469440166937 3347154232285852080125203)
    ·
      refine ⟨5020731348428778120187805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3347154232285852080125203 5020731348428778120187805)
      ·
        refine ⟨1882774255660791795070427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5020731348428778120187805 1882774255660791795070427)
        ·
          refine ⟨2824161383491187692605641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1882774255660791795070427 2824161383491187692605641)
          ·
            refine ⟨2118121037618390769454231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2824161383491187692605641 2118121037618390769454231)
            ·
              refine ⟨3177181556427586154181347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2118121037618390769454231 3177181556427586154181347)
              ·
                refine ⟨4765772334641379231272021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3177181556427586154181347 4765772334641379231272021)
                ·
                  refine ⟨55848894546578662866469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4765772334641379231272021 55848894546578662866469)
                  ·
                    rfl

theorem cell20_122361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_122361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122361 prefixEnd_122361 := by exact prefixLift 122361
  have htrace : WordTrace (prefixWord ++ tailWord_122361) baseStart_122361 baseEnd_122361 := by
    simpa [prefixWord, tailWord_122361, baseEnd_122361] using wordTrace_append hprefix tailTrace_122361
  have hstable : (prefixWord ++ tailWord_122361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122361).length < 2 ^ (prefixWord ++ tailWord_122361).sum := by decide
  have hdescent : baseEnd_122361 < baseStart_122361 := by decide
  rcases family_descends (prefixWord ++ tailWord_122361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122378 : List Nat := [3, 1, 2, 2, 2, 2, 1, 3, 4]
def baseStart_122378 : Nat := 118140960795 + 122378 * 2 ^ 59
def prefixEnd_122378 : Nat := 4983230072969 + 3 ^ 40 * 122378 * 2
def baseEnd_122378 : Nat := 55856653809802159299733

theorem tailTrace_122378 : CollatzResearch.WordTrace tailWord_122378 prefixEnd_122378 55856653809802159299733 := by
  unfold tailWord_122378
  simp only [CollatzResearch.WordTrace]
  refine ⟨1115873087663220335883947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2975661567101920895690525 1115873087663220335883947)
  ·
    refine ⟨1673809631494830503825921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1115873087663220335883947 1673809631494830503825921)
    ·
      refine ⟨1255357223621122877869441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1673809631494830503825921 1255357223621122877869441)
      ·
        refine ⟨941517917715842158402081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1255357223621122877869441 941517917715842158402081)
        ·
          refine ⟨706138438286881618801561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 941517917715842158402081 706138438286881618801561)
          ·
            refine ⟨529603828715161214101171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 706138438286881618801561 529603828715161214101171)
            ·
              refine ⟨794405743072741821151757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 529603828715161214101171 794405743072741821151757)
              ·
                refine ⟨297902153652278182931909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 794405743072741821151757 297902153652278182931909)
                ·
                  refine ⟨55856653809802159299733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 297902153652278182931909 55856653809802159299733)
                  ·
                    rfl

theorem cell20_122378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_122378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122378 prefixEnd_122378 := by exact prefixLift 122378
  have htrace : WordTrace (prefixWord ++ tailWord_122378) baseStart_122378 baseEnd_122378 := by
    simpa [prefixWord, tailWord_122378, baseEnd_122378] using wordTrace_append hprefix tailTrace_122378
  have hstable : (prefixWord ++ tailWord_122378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122378).length < 2 ^ (prefixWord ++ tailWord_122378).sum := by decide
  have hdescent : baseEnd_122378 < baseStart_122378 := by decide
  rcases family_descends (prefixWord ++ tailWord_122378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122402 : List Nat := [3, 3, 1, 1, 1, 1, 6, 4]
def baseStart_122402 : Nat := 118140960795 + 122402 * 2 ^ 59
def prefixEnd_122402 : Nat := 4983230072969 + 3 ^ 40 * 122402 * 2
def baseEnd_122402 : Nat := 18622536021254914166545

theorem tailTrace_122402 : CollatzResearch.WordTrace tailWord_122402 prefixEnd_122402 18622536021254914166545 := by
  unfold tailWord_122402
  simp only [CollatzResearch.WordTrace]
  refine ⟨1116091925641483360602365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2976245135043955628272973 1116091925641483360602365)
  ·
    refine ⟨418534472115556260225887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1116091925641483360602365 418534472115556260225887)
    ·
      refine ⟨627801708173334390338831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418534472115556260225887 627801708173334390338831)
      ·
        refine ⟨941702562260001585508247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627801708173334390338831 941702562260001585508247)
        ·
          refine ⟨1412553843390002378262371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941702562260001585508247 1412553843390002378262371)
          ·
            refine ⟨2118830765085003567393557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1412553843390002378262371 2118830765085003567393557)
            ·
              refine ⟨99320192113359542221573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2118830765085003567393557 99320192113359542221573)
              ·
                refine ⟨18622536021254914166545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99320192113359542221573 18622536021254914166545)
                ·
                  rfl

theorem cell20_122402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_122402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122402 prefixEnd_122402 := by exact prefixLift 122402
  have htrace : WordTrace (prefixWord ++ tailWord_122402) baseStart_122402 baseEnd_122402 := by
    simpa [prefixWord, tailWord_122402, baseEnd_122402] using wordTrace_append hprefix tailTrace_122402
  have hstable : (prefixWord ++ tailWord_122402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122402).length < 2 ^ (prefixWord ++ tailWord_122402).sum := by decide
  have hdescent : baseEnd_122402 < baseStart_122402 := by decide
  rcases family_descends (prefixWord ++ tailWord_122402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122408 : List Nat := [2, 1, 5, 2, 3, 1, 1, 3, 2]
def baseStart_122408 : Nat := 118140960795 + 122408 * 2 ^ 59
def prefixEnd_122408 : Nat := 4983230072969 + 3 ^ 40 * 122408 * 2
def baseEnd_122408 : Nat := 55870346627255388299611

theorem tailTrace_122408 : CollatzResearch.WordTrace tailWord_122408 prefixEnd_122408 55870346627255388299611 := by
  unfold tailWord_122408
  simp only [CollatzResearch.WordTrace]
  refine ⟨2232293270272098233563939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2976391027029464311418585 2232293270272098233563939)
  ·
    refine ⟨3348439905408147350345909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2232293270272098233563939 3348439905408147350345909)
    ·
      refine ⟨313916241132013814094929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3348439905408147350345909 313916241132013814094929)
      ·
        refine ⟨235437180849010360571197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313916241132013814094929 235437180849010360571197)
        ·
          refine ⟨88288942818378885214199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235437180849010360571197 88288942818378885214199)
          ·
            refine ⟨132433414227568327821299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88288942818378885214199 132433414227568327821299)
            ·
              refine ⟨198650121341352491731949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132433414227568327821299 198650121341352491731949)
              ·
                refine ⟨74493795503007184399481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198650121341352491731949 74493795503007184399481)
                ·
                  refine ⟨55870346627255388299611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74493795503007184399481 55870346627255388299611)
                  ·
                    rfl

theorem cell20_122408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 3, 2].length) (baseStart_122408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122408 prefixEnd_122408 := by exact prefixLift 122408
  have htrace : WordTrace (prefixWord ++ tailWord_122408) baseStart_122408 baseEnd_122408 := by
    simpa [prefixWord, tailWord_122408, baseEnd_122408] using wordTrace_append hprefix tailTrace_122408
  have hstable : (prefixWord ++ tailWord_122408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122408).length < 2 ^ (prefixWord ++ tailWord_122408).sum := by decide
  have hdescent : baseEnd_122408 < baseStart_122408 := by decide
  rcases family_descends (prefixWord ++ tailWord_122408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122423 : List Nat := [1, 1, 3, 1, 2, 6, 6]
def baseStart_122423 : Nat := 118140960795 + 122423 * 2 ^ 59
def prefixEnd_122423 : Nat := 4983230072969 + 3 ^ 40 * 122423 * 2
def baseEnd_122423 : Nat := 6208577003998000311061

theorem tailTrace_122423 : CollatzResearch.WordTrace tailWord_122423 prefixEnd_122423 6208577003998000311061 := by
  unfold tailWord_122423
  simp only [CollatzResearch.WordTrace]
  refine ⟨4465133635489854028923923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2976755756993236019282615 4465133635489854028923923)
  ·
    refine ⟨6697700453234781043385885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4465133635489854028923923 6697700453234781043385885)
    ·
      refine ⟨2511637669963042891269707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6697700453234781043385885 2511637669963042891269707)
      ·
        refine ⟨3767456504944564336904561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2511637669963042891269707 3767456504944564336904561)
        ·
          refine ⟨2825592378708423252678421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3767456504944564336904561 2825592378708423252678421)
          ·
            refine ⟨132449642751957339969301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2825592378708423252678421 132449642751957339969301)
            ·
              refine ⟨6208577003998000311061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 132449642751957339969301 6208577003998000311061)
              ·
                rfl

theorem cell20_122423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 6].length) (baseStart_122423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122423 prefixEnd_122423 := by exact prefixLift 122423
  have htrace : WordTrace (prefixWord ++ tailWord_122423) baseStart_122423 baseEnd_122423 := by
    simpa [prefixWord, tailWord_122423, baseEnd_122423] using wordTrace_append hprefix tailTrace_122423
  have hstable : (prefixWord ++ tailWord_122423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122423).length < 2 ^ (prefixWord ++ tailWord_122423).sum := by decide
  have hdescent : baseEnd_122423 < baseStart_122423 := by decide
  rcases family_descends (prefixWord ++ tailWord_122423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122429 : List Nat := [1, 4, 1, 3, 3, 1, 3, 2, 2]
def baseStart_122429 : Nat := 118140960795 + 122429 * 2 ^ 59
def prefixEnd_122429 : Nat := 4983230072969 + 3 ^ 40 * 122429 * 2
def baseEnd_122429 : Nat := 55879931599472648599525

theorem tailTrace_122429 : CollatzResearch.WordTrace tailWord_122429 prefixEnd_122429 55879931599472648599525 := by
  unfold tailWord_122429
  simp only [CollatzResearch.WordTrace]
  refine ⟨4465352473468117053642341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2976901648978744702428227 4465352473468117053642341)
  ·
    refine ⟨837253588775271947557939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4465352473468117053642341 837253588775271947557939)
    ·
      refine ⟨1255880383162907921336909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 837253588775271947557939 1255880383162907921336909)
      ·
        refine ⟨470955143686090470501341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1255880383162907921336909 470955143686090470501341)
        ·
          refine ⟨176608178882283926438003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 470955143686090470501341 176608178882283926438003)
          ·
            refine ⟨264912268323425889657005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176608178882283926438003 264912268323425889657005)
            ·
              refine ⟨99342100621284708621377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264912268323425889657005 99342100621284708621377)
              ·
                refine ⟨74506575465963531466033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99342100621284708621377 74506575465963531466033)
                ·
                  refine ⟨55879931599472648599525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74506575465963531466033 55879931599472648599525)
                  ·
                    rfl

theorem cell20_122429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_122429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122429 prefixEnd_122429 := by exact prefixLift 122429
  have htrace : WordTrace (prefixWord ++ tailWord_122429) baseStart_122429 baseEnd_122429 := by
    simpa [prefixWord, tailWord_122429, baseEnd_122429] using wordTrace_append hprefix tailTrace_122429
  have hstable : (prefixWord ++ tailWord_122429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122429).length < 2 ^ (prefixWord ++ tailWord_122429).sum := by decide
  have hdescent : baseEnd_122429 < baseStart_122429 := by decide
  rcases family_descends (prefixWord ++ tailWord_122429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122478 : List Nat := [4, 1, 2, 2, 4, 7]
def baseStart_122478 : Nat := 118140960795 + 122478 * 2 ^ 59
def prefixEnd_122478 : Nat := 4983230072969 + 3 ^ 40 * 122478 * 2
def baseEnd_122478 : Nat := 2070455427209120591333

theorem tailTrace_122478 : CollatzResearch.WordTrace tailWord_122478 prefixEnd_122478 2070455427209120591333 := by
  unfold tailWord_122478
  simp only [CollatzResearch.WordTrace]
  refine ⟨558392456286324802772011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2978093100193732281450725 558392456286324802772011)
  ·
    refine ⟨837588684429487204158017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 558392456286324802772011 837588684429487204158017)
    ·
      refine ⟨628191513322115403118513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 837588684429487204158017 628191513322115403118513)
      ·
        refine ⟨471143634991586552338885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 628191513322115403118513 471143634991586552338885)
        ·
          refine ⟨88339431560922478563541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 471143634991586552338885 88339431560922478563541)
          ·
            refine ⟨2070455427209120591333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 88339431560922478563541 2070455427209120591333)
            ·
              rfl

theorem cell20_122478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 7].length) (baseStart_122478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122478 prefixEnd_122478 := by exact prefixLift 122478
  have htrace : WordTrace (prefixWord ++ tailWord_122478) baseStart_122478 baseEnd_122478 := by
    simpa [prefixWord, tailWord_122478, baseEnd_122478] using wordTrace_append hprefix tailTrace_122478
  have hstable : (prefixWord ++ tailWord_122478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122478).length < 2 ^ (prefixWord ++ tailWord_122478).sum := by decide
  have hdescent : baseEnd_122478 < baseStart_122478 := by decide
  rcases family_descends (prefixWord ++ tailWord_122478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122526 : List Nat := [4, 3, 1, 1, 1, 2, 1, 5, 2]
def baseStart_122526 : Nat := 118140960795 + 122526 * 2 ^ 59
def prefixEnd_122526 : Nat := 4983230072969 + 3 ^ 40 * 122526 * 2
def baseEnd_122526 : Nat := 55924205042571422365795

theorem tailTrace_122526 : CollatzResearch.WordTrace tailWord_122526 prefixEnd_122526 55924205042571422365795 := by
  unfold tailWord_122526
  simp only [CollatzResearch.WordTrace]
  refine ⟨558611294264587827490429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2979260236077801746615621 558611294264587827490429)
  ·
    refine ⟨209479235349220435308911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 558611294264587827490429 209479235349220435308911)
    ·
      refine ⟨314218853023830652963367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209479235349220435308911 314218853023830652963367)
      ·
        refine ⟨471328279535745979445051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314218853023830652963367 471328279535745979445051)
        ·
          refine ⟨706992419303618969167577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471328279535745979445051 706992419303618969167577)
          ·
            refine ⟨530244314477714226875683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 706992419303618969167577 530244314477714226875683)
            ·
              refine ⟨795366471716571340313525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530244314477714226875683 795366471716571340313525)
              ·
                refine ⟨74565606723428563154393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 795366471716571340313525 74565606723428563154393)
                ·
                  refine ⟨55924205042571422365795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74565606723428563154393 55924205042571422365795)
                  ·
                    rfl

theorem cell20_122526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_122526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122526 prefixEnd_122526 := by exact prefixLift 122526
  have htrace : WordTrace (prefixWord ++ tailWord_122526) baseStart_122526 baseEnd_122526 := by
    simpa [prefixWord, tailWord_122526, baseEnd_122526] using wordTrace_append hprefix tailTrace_122526
  have hstable : (prefixWord ++ tailWord_122526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122526).length < 2 ^ (prefixWord ++ tailWord_122526).sum := by decide
  have hdescent : baseEnd_122526 < baseStart_122526 := by decide
  rcases family_descends (prefixWord ++ tailWord_122526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122585 : List Nat := [1, 2, 1, 2, 3, 3, 3, 3, 2]
def baseStart_122585 : Nat := 118140960795 + 122585 * 2 ^ 59
def prefixEnd_122585 : Nat := 4983230072969 + 3 ^ 40 * 122585 * 2
def baseEnd_122585 : Nat := 55951134250229439398887

theorem tailTrace_122585 : CollatzResearch.WordTrace tailWord_122585 prefixEnd_122585 55951134250229439398887 := by
  unfold tailWord_122585
  simp only [CollatzResearch.WordTrace]
  refine ⟨4471042260902955696321209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2980694840601970464214139 4471042260902955696321209)
  ·
    refine ⟨3353281695677216772240907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4471042260902955696321209 3353281695677216772240907)
    ·
      refine ⟨5029922543515825158361361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3353281695677216772240907 5029922543515825158361361)
      ·
        refine ⟨3772441907636868868771021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5029922543515825158361361 3772441907636868868771021)
        ·
          refine ⟨1414665715363825825789133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3772441907636868868771021 1414665715363825825789133)
          ·
            refine ⟨530499643261434684670925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1414665715363825825789133 530499643261434684670925)
            ·
              refine ⟨198937366223038006751597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 530499643261434684670925 198937366223038006751597)
              ·
                refine ⟨74601512333639252531849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198937366223038006751597 74601512333639252531849)
                ·
                  refine ⟨55951134250229439398887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74601512333639252531849 55951134250229439398887)
                  ·
                    rfl

theorem cell20_122585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 3, 2].length) (baseStart_122585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122585 prefixEnd_122585 := by exact prefixLift 122585
  have htrace : WordTrace (prefixWord ++ tailWord_122585) baseStart_122585 baseEnd_122585 := by
    simpa [prefixWord, tailWord_122585, baseEnd_122585] using wordTrace_append hprefix tailTrace_122585
  have hstable : (prefixWord ++ tailWord_122585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122585).length < 2 ^ (prefixWord ++ tailWord_122585).sum := by decide
  have hdescent : baseEnd_122585 < baseStart_122585 := by decide
  rcases family_descends (prefixWord ++ tailWord_122585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122612 : List Nat := [2, 6, 1, 1, 1, 1, 4, 1, 3]
def baseStart_122612 : Nat := 118140960795 + 122612 * 2 ^ 59
def prefixEnd_122612 : Nat := 4983230072969 + 3 ^ 40 * 122612 * 2
def baseEnd_122612 : Nat := 55963457785937345498777

theorem tailTrace_122612 : CollatzResearch.WordTrace tailWord_122612 prefixEnd_122612 55963457785937345498777 := by
  unfold tailWord_122612
  simp only [CollatzResearch.WordTrace]
  refine ⟨2236013515902569653777045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2981351354536759538369393 2236013515902569653777045)
  ·
    refine ⟨104813133557932952520799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2236013515902569653777045 104813133557932952520799)
    ·
      refine ⟨157219700336899428781199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104813133557932952520799 157219700336899428781199)
      ·
        refine ⟨235829550505349143171799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157219700336899428781199 235829550505349143171799)
        ·
          refine ⟨353744325758023714757699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235829550505349143171799 353744325758023714757699)
          ·
            refine ⟨530616488637035572136549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353744325758023714757699 530616488637035572136549)
            ·
              refine ⟨99490591619444169775603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 530616488637035572136549 99490591619444169775603)
              ·
                refine ⟨149235887429166254663405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99490591619444169775603 149235887429166254663405)
                ·
                  refine ⟨55963457785937345498777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149235887429166254663405 55963457785937345498777)
                  ·
                    rfl

theorem cell20_122612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_122612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122612 prefixEnd_122612 := by exact prefixLift 122612
  have htrace : WordTrace (prefixWord ++ tailWord_122612) baseStart_122612 baseEnd_122612 := by
    simpa [prefixWord, tailWord_122612, baseEnd_122612] using wordTrace_append hprefix tailTrace_122612
  have hstable : (prefixWord ++ tailWord_122612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122612).length < 2 ^ (prefixWord ++ tailWord_122612).sum := by decide
  have hdescent : baseEnd_122612 < baseStart_122612 := by decide
  rcases family_descends (prefixWord ++ tailWord_122612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122627 : List Nat := [1, 1, 1, 3, 2, 2, 2, 4, 4]
def baseStart_122627 : Nat := 118140960795 + 122627 * 2 ^ 59
def prefixEnd_122627 : Nat := 4983230072969 + 3 ^ 40 * 122627 * 2
def baseEnd_122627 : Nat := 55970304194663959998715

theorem tailTrace_122627 : CollatzResearch.WordTrace tailWord_122627 prefixEnd_122627 55970304194663959998715 := by
  unfold tailWord_122627
  simp only [CollatzResearch.WordTrace]
  refine ⟨4472574126750796869350135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2981716084500531246233423 4472574126750796869350135)
  ·
    refine ⟨6708861190126195304025203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4472574126750796869350135 6708861190126195304025203)
    ·
      refine ⟨10063291785189292956037805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6708861190126195304025203 10063291785189292956037805)
      ·
        refine ⟨3773734419445984858514177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10063291785189292956037805 3773734419445984858514177)
        ·
          refine ⟨2830300814584488643885633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3773734419445984858514177 2830300814584488643885633)
          ·
            refine ⟨2122725610938366482914225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2830300814584488643885633 2122725610938366482914225)
            ·
              refine ⟨1592044208203774862185669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2122725610938366482914225 1592044208203774862185669)
              ·
                refine ⟨298508289038207786659813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1592044208203774862185669 298508289038207786659813)
                ·
                  refine ⟨55970304194663959998715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 298508289038207786659813 55970304194663959998715)
                  ·
                    rfl

theorem cell20_122627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 4].length) (baseStart_122627 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122627 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122627 prefixEnd_122627 := by exact prefixLift 122627
  have htrace : WordTrace (prefixWord ++ tailWord_122627) baseStart_122627 baseEnd_122627 := by
    simpa [prefixWord, tailWord_122627, baseEnd_122627] using wordTrace_append hprefix tailTrace_122627
  have hstable : (prefixWord ++ tailWord_122627).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122627).length < 2 ^ (prefixWord ++ tailWord_122627).sum := by decide
  have hdescent : baseEnd_122627 < baseStart_122627 := by decide
  rcases family_descends (prefixWord ++ tailWord_122627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122661 : List Nat := [1, 3, 1, 2, 3, 3, 1, 4, 2]
def baseStart_122661 : Nat := 118140960795 + 122661 * 2 ^ 59
def prefixEnd_122661 : Nat := 4983230072969 + 3 ^ 40 * 122661 * 2
def baseEnd_122661 : Nat := 55985822721110952865243

theorem tailTrace_122661 : CollatzResearch.WordTrace tailWord_122661 prefixEnd_122661 55985822721110952865243 := by
  unfold tailWord_122661
  simp only [CollatzResearch.WordTrace]
  refine ⟨4473814208627620676087837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2982542805751747117391891 4473814208627620676087837)
  ·
    refine ⟨1677680328235357753532939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4473814208627620676087837 1677680328235357753532939)
    ·
      refine ⟨2516520492353036630299409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1677680328235357753532939 2516520492353036630299409)
      ·
        refine ⟨1887390369264777472724557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2516520492353036630299409 1887390369264777472724557)
        ·
          refine ⟨707771388474291552271709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1887390369264777472724557 707771388474291552271709)
          ·
            refine ⟨265414270677859332101891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 707771388474291552271709 265414270677859332101891)
            ·
              refine ⟨398121406016788998152837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265414270677859332101891 398121406016788998152837)
              ·
                refine ⟨74647763628147937153657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 398121406016788998152837 74647763628147937153657)
                ·
                  refine ⟨55985822721110952865243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74647763628147937153657 55985822721110952865243)
                  ·
                    rfl

theorem cell20_122661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 4, 2].length) (baseStart_122661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122661 prefixEnd_122661 := by exact prefixLift 122661
  have htrace : WordTrace (prefixWord ++ tailWord_122661) baseStart_122661 baseEnd_122661 := by
    simpa [prefixWord, tailWord_122661, baseEnd_122661] using wordTrace_append hprefix tailTrace_122661
  have hstable : (prefixWord ++ tailWord_122661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122661).length < 2 ^ (prefixWord ++ tailWord_122661).sum := by decide
  have hdescent : baseEnd_122661 < baseStart_122661 := by decide
  rcases family_descends (prefixWord ++ tailWord_122661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122682 : List Nat := [3, 1, 1, 1, 5, 2, 1, 2, 4]
def baseStart_122682 : Nat := 118140960795 + 122682 * 2 ^ 59
def prefixEnd_122682 : Nat := 4983230072969 + 3 ^ 40 * 122682 * 2
def baseEnd_122682 : Nat := 55995407693328213165157

theorem tailTrace_122682 : CollatzResearch.WordTrace tailWord_122682 prefixEnd_122682 55995407693328213165157 := by
  unfold tailWord_122682
  simp only [CollatzResearch.WordTrace]
  refine ⟨1118645035387885315650575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2983053427701027508401533 1118645035387885315650575)
  ·
    refine ⟨1677967553081827973475863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1118645035387885315650575 1677967553081827973475863)
    ·
      refine ⟨2516951329622741960213795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1677967553081827973475863 2516951329622741960213795)
      ·
        refine ⟨3775426994434112940320693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2516951329622741960213795 3775426994434112940320693)
        ·
          refine ⟨353946280728198088155065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3775426994434112940320693 353946280728198088155065)
          ·
            refine ⟨265459710546148566116299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353946280728198088155065 265459710546148566116299)
            ·
              refine ⟨398189565819222849174449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265459710546148566116299 398189565819222849174449)
              ·
                refine ⟨298642174364417136880837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 398189565819222849174449 298642174364417136880837)
                ·
                  refine ⟨55995407693328213165157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 298642174364417136880837 55995407693328213165157)
                  ·
                    rfl

theorem cell20_122682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_122682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122682 prefixEnd_122682 := by exact prefixLift 122682
  have htrace : WordTrace (prefixWord ++ tailWord_122682) baseStart_122682 baseEnd_122682 := by
    simpa [prefixWord, tailWord_122682, baseEnd_122682] using wordTrace_append hprefix tailTrace_122682
  have hstable : (prefixWord ++ tailWord_122682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122682).length < 2 ^ (prefixWord ++ tailWord_122682).sum := by decide
  have hdescent : baseEnd_122682 < baseStart_122682 := by decide
  rcases family_descends (prefixWord ++ tailWord_122682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122720 : List Nat := [2, 1, 1, 3, 3, 3, 2, 1, 4]
def baseStart_122720 : Nat := 118140960795 + 122720 * 2 ^ 59
def prefixEnd_122720 : Nat := 4983230072969 + 3 ^ 40 * 122720 * 2
def baseEnd_122720 : Nat := 56012751928768969898335

theorem tailTrace_122720 : CollatzResearch.WordTrace tailWord_122720 prefixEnd_122720 56012751928768969898335 := by
  unfold tailWord_122720
  simp only [CollatzResearch.WordTrace]
  refine ⟨2237983057706936876242807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2983977410275915834990409 2237983057706936876242807)
  ·
    refine ⟨3356974586560405314364211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2237983057706936876242807 3356974586560405314364211)
    ·
      refine ⟨5035461879840607971546317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3356974586560405314364211 5035461879840607971546317)
      ·
        refine ⟨1888298204940227989329869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5035461879840607971546317 1888298204940227989329869)
        ·
          refine ⟨708111826852585495998701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1888298204940227989329869 708111826852585495998701)
          ·
            refine ⟨265541935069719560999513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 708111826852585495998701 265541935069719560999513)
            ·
              refine ⟨199156451302289670749635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265541935069719560999513 199156451302289670749635)
              ·
                refine ⟨298734676953434506124453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199156451302289670749635 298734676953434506124453)
                ·
                  refine ⟨56012751928768969898335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 298734676953434506124453 56012751928768969898335)
                  ·
                    rfl

theorem cell20_122720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_122720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122720 prefixEnd_122720 := by exact prefixLift 122720
  have htrace : WordTrace (prefixWord ++ tailWord_122720) baseStart_122720 baseEnd_122720 := by
    simpa [prefixWord, tailWord_122720, baseEnd_122720] using wordTrace_append hprefix tailTrace_122720
  have hstable : (prefixWord ++ tailWord_122720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122720).length < 2 ^ (prefixWord ++ tailWord_122720).sum := by decide
  have hdescent : baseEnd_122720 < baseStart_122720 := by decide
  rcases family_descends (prefixWord ++ tailWord_122720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122785 : List Nat := [1, 2, 3, 4, 2, 2, 2, 1, 3]
def baseStart_122785 : Nat := 118140960795 + 122785 * 2 ^ 59
def prefixEnd_122785 : Nat := 4983230072969 + 3 ^ 40 * 122785 * 2
def baseEnd_122785 : Nat := 56042419699917632731403

theorem tailTrace_122785 : CollatzResearch.WordTrace tailWord_122785 prefixEnd_122785 56042419699917632731403 := by
  unfold tailWord_122785
  simp only [CollatzResearch.WordTrace]
  refine ⟨4478336860178389853601809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2985557906785593235734539 4478336860178389853601809)
  ·
    refine ⟨3358752645133792390201357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4478336860178389853601809 3358752645133792390201357)
    ·
      refine ⟨1259532241925172146325509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3358752645133792390201357 1259532241925172146325509)
      ·
        refine ⟨236162295360969777436033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1259532241925172146325509 236162295360969777436033)
        ·
          refine ⟨177121721520727333077025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236162295360969777436033 177121721520727333077025)
          ·
            refine ⟨132841291140545499807769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177121721520727333077025 132841291140545499807769)
            ·
              refine ⟨99630968355409124855827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132841291140545499807769 99630968355409124855827)
              ·
                refine ⟨149446452533113687283741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99630968355409124855827 149446452533113687283741)
                ·
                  refine ⟨56042419699917632731403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149446452533113687283741 56042419699917632731403)
                  ·
                    rfl

theorem cell20_122785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 3].length) (baseStart_122785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122785 prefixEnd_122785 := by exact prefixLift 122785
  have htrace : WordTrace (prefixWord ++ tailWord_122785) baseStart_122785 baseEnd_122785 := by
    simpa [prefixWord, tailWord_122785, baseEnd_122785] using wordTrace_append hprefix tailTrace_122785
  have hstable : (prefixWord ++ tailWord_122785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122785).length < 2 ^ (prefixWord ++ tailWord_122785).sum := by decide
  have hdescent : baseEnd_122785 < baseStart_122785 := by decide
  rcases family_descends (prefixWord ++ tailWord_122785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122793 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 7]
def baseStart_122793 : Nat := 118140960795 + 122793 * 2 ^ 59
def prefixEnd_122793 : Nat := 4983230072969 + 3 ^ 40 * 122793 * 2
def baseEnd_122793 : Nat := 56046071117905160464703

theorem tailTrace_122793 : CollatzResearch.WordTrace tailWord_122793 prefixEnd_122793 56046071117905160464703 := by
  unfold tailWord_122793
  simp only [CollatzResearch.WordTrace]
  refine ⟨4478628644149407219893033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2985752429432938146595355 4478628644149407219893033)
  ·
    refine ⟨3358971483112055414919775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4478628644149407219893033 3358971483112055414919775)
    ·
      refine ⟨5038457224668083122379663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3358971483112055414919775 5038457224668083122379663)
      ·
        refine ⟨7557685837002124683569495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5038457224668083122379663 7557685837002124683569495)
        ·
          refine ⟨11336528755503187025354243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7557685837002124683569495 11336528755503187025354243)
          ·
            refine ⟨17004793133254780538031365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11336528755503187025354243 17004793133254780538031365)
            ·
              refine ⟨3188398712485271350880881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17004793133254780538031365 3188398712485271350880881)
              ·
                refine ⟨2391299034363953513160661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3188398712485271350880881 2391299034363953513160661)
                ·
                  refine ⟨56046071117905160464703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2391299034363953513160661 56046071117905160464703)
                  ·
                    rfl

theorem cell20_122793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_122793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122793 prefixEnd_122793 := by exact prefixLift 122793
  have htrace : WordTrace (prefixWord ++ tailWord_122793) baseStart_122793 baseEnd_122793 := by
    simpa [prefixWord, tailWord_122793, baseEnd_122793] using wordTrace_append hprefix tailTrace_122793
  have hstable : (prefixWord ++ tailWord_122793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122793).length < 2 ^ (prefixWord ++ tailWord_122793).sum := by decide
  have hdescent : baseEnd_122793 < baseStart_122793 := by decide
  rcases family_descends (prefixWord ++ tailWord_122793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122824 : List Nat := [2, 1, 3, 1, 4, 9]
def baseStart_122824 : Nat := 118140960795 + 122824 * 2 ^ 59
def prefixEnd_122824 : Nat := 4983230072969 + 3 ^ 40 * 122824 * 2
def baseEnd_122824 : Nat := 2076304457874327053009

theorem tailTrace_122824 : CollatzResearch.WordTrace tailWord_122824 prefixEnd_122824 2076304457874327053009 := by
  unfold tailWord_122824
  simp only [CollatzResearch.WordTrace]
  refine ⟨2239879653518549757135763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2986506204691399676181017 2239879653518549757135763)
  ·
    refine ⟨3359819480277824635703645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2239879653518549757135763 3359819480277824635703645)
    ·
      refine ⟨1259932305104184238388867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3359819480277824635703645 1259932305104184238388867)
      ·
        refine ⟨1889898457656276357583301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1259932305104184238388867 1889898457656276357583301)
        ·
          refine ⟨354355960810551817046869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1889898457656276357583301 354355960810551817046869)
          ·
            refine ⟨2076304457874327053009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 354355960810551817046869 2076304457874327053009)
            ·
              rfl

theorem cell20_122824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 9].length) (baseStart_122824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122824 prefixEnd_122824 := by exact prefixLift 122824
  have htrace : WordTrace (prefixWord ++ tailWord_122824) baseStart_122824 baseEnd_122824 := by
    simpa [prefixWord, tailWord_122824, baseEnd_122824] using wordTrace_append hprefix tailTrace_122824
  have hstable : (prefixWord ++ tailWord_122824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122824).length < 2 ^ (prefixWord ++ tailWord_122824).sum := by decide
  have hdescent : baseEnd_122824 < baseStart_122824 := by decide
  rcases family_descends (prefixWord ++ tailWord_122824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122872 : List Nat := [2, 1, 2, 1, 1, 3, 3, 5, 2]
def baseStart_122872 : Nat := 118140960795 + 122872 * 2 ^ 59
def prefixEnd_122872 : Nat := 4983230072969 + 3 ^ 40 * 122872 * 2
def baseEnd_122872 : Nat := 56082128870531996831047

theorem tailTrace_122872 : CollatzResearch.WordTrace tailWord_122872 prefixEnd_122872 56082128870531996831047 := by
  unfold tailWord_122872
  simp only [CollatzResearch.WordTrace]
  refine ⟨2240755005431601856009435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2987673340575469141345913 2240755005431601856009435)
  ·
    refine ⟨3361132508147402784014153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2240755005431601856009435 3361132508147402784014153)
    ·
      refine ⟨2520849381110552088010615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3361132508147402784014153 2520849381110552088010615)
      ·
        refine ⟨3781274071665828132015923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2520849381110552088010615 3781274071665828132015923)
        ·
          refine ⟨5671911107498742198023885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3781274071665828132015923 5671911107498742198023885)
          ·
            refine ⟨2126966665312028324258957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5671911107498742198023885 2126966665312028324258957)
            ·
              refine ⟨797612499492010621597109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2126966665312028324258957 797612499492010621597109)
              ·
                refine ⟨74776171827375995774729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 797612499492010621597109 74776171827375995774729)
                ·
                  refine ⟨56082128870531996831047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74776171827375995774729 56082128870531996831047)
                  ·
                    rfl

theorem cell20_122872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 5, 2].length) (baseStart_122872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122872 prefixEnd_122872 := by exact prefixLift 122872
  have htrace : WordTrace (prefixWord ++ tailWord_122872) baseStart_122872 baseEnd_122872 := by
    simpa [prefixWord, tailWord_122872, baseEnd_122872] using wordTrace_append hprefix tailTrace_122872
  have hstable : (prefixWord ++ tailWord_122872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122872).length < 2 ^ (prefixWord ++ tailWord_122872).sum := by decide
  have hdescent : baseEnd_122872 < baseStart_122872 := by decide
  rcases family_descends (prefixWord ++ tailWord_122872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122913 : List Nat := [1, 2, 3, 2, 5, 1, 2, 4]
def baseStart_122913 : Nat := 118140960795 + 122913 * 2 ^ 59
def prefixEnd_122913 : Nat := 4983230072969 + 3 ^ 40 * 122913 * 2
def baseEnd_122913 : Nat := 18700280795906025488071

theorem tailTrace_122913 : CollatzResearch.WordTrace tailWord_122913 prefixEnd_122913 18700280795906025488071 := by
  unfold tailWord_122913
  simp only [CollatzResearch.WordTrace]
  refine ⟨4483005403714667714261393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2988670269143111809507595 4483005403714667714261393)
  ·
    refine ⟨3362254052786000785696045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4483005403714667714261393 3362254052786000785696045)
    ·
      refine ⟨1260845269794750294636017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3362254052786000785696045 1260845269794750294636017)
      ·
        refine ⟨945633952346062720977013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1260845269794750294636017 945633952346062720977013)
        ·
          refine ⟨88653183032443380091595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 945633952346062720977013 88653183032443380091595)
          ·
            refine ⟨132979774548665070137393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88653183032443380091595 132979774548665070137393)
            ·
              refine ⟨99734830911498802603045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132979774548665070137393 99734830911498802603045)
              ·
                refine ⟨18700280795906025488071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99734830911498802603045 18700280795906025488071)
                ·
                  rfl

theorem cell20_122913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 4].length) (baseStart_122913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122913 prefixEnd_122913 := by exact prefixLift 122913
  have htrace : WordTrace (prefixWord ++ tailWord_122913) baseStart_122913 baseEnd_122913 := by
    simpa [prefixWord, tailWord_122913, baseEnd_122913] using wordTrace_append hprefix tailTrace_122913
  have hstable : (prefixWord ++ tailWord_122913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122913).length < 2 ^ (prefixWord ++ tailWord_122913).sum := by decide
  have hdescent : baseEnd_122913 < baseStart_122913 := by decide
  rcases family_descends (prefixWord ++ tailWord_122913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122917 : List Nat := [1, 3, 1, 2, 2, 3, 4, 4]
def baseStart_122917 : Nat := 118140960795 + 122917 * 2 ^ 59
def prefixEnd_122917 : Nat := 4983230072969 + 3 ^ 40 * 122917 * 2
def baseEnd_122917 : Nat := 18700889365570613443621

theorem tailTrace_122917 : CollatzResearch.WordTrace tailWord_122917 prefixEnd_122917 18700889365570613443621 := by
  unfold tailWord_122917
  simp only [CollatzResearch.WordTrace]
  refine ⟨4483151295700176397407005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2988767530466784264938003 4483151295700176397407005)
  ·
    refine ⟨1681181735887566149027627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4483151295700176397407005 1681181735887566149027627)
    ·
      refine ⟨2521772603831349223541441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1681181735887566149027627 2521772603831349223541441)
      ·
        refine ⟨1891329452873511917656081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2521772603831349223541441 1891329452873511917656081)
        ·
          refine ⟨1418497089655133938242061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1891329452873511917656081 1418497089655133938242061)
          ·
            refine ⟨531936408620675226840773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1418497089655133938242061 531936408620675226840773)
            ·
              refine ⟨99738076616376605032645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 531936408620675226840773 99738076616376605032645)
              ·
                refine ⟨18700889365570613443621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99738076616376605032645 18700889365570613443621)
                ·
                  rfl

theorem cell20_122917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 4].length) (baseStart_122917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122917 prefixEnd_122917 := by exact prefixLift 122917
  have htrace : WordTrace (prefixWord ++ tailWord_122917) baseStart_122917 baseEnd_122917 := by
    simpa [prefixWord, tailWord_122917, baseEnd_122917] using wordTrace_append hprefix tailTrace_122917
  have hstable : (prefixWord ++ tailWord_122917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122917).length < 2 ^ (prefixWord ++ tailWord_122917).sum := by decide
  have hdescent : baseEnd_122917 < baseStart_122917 := by decide
  rcases family_descends (prefixWord ++ tailWord_122917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122958 : List Nat := [4, 1, 1, 1, 1, 6, 2, 1, 3]
def baseStart_122958 : Nat := 118140960795 + 122958 * 2 ^ 59
def prefixEnd_122958 : Nat := 4983230072969 + 3 ^ 40 * 122958 * 2
def baseEnd_122958 : Nat := 56121381613897919964029

theorem tailTrace_122958 : CollatzResearch.WordTrace tailWord_122958 prefixEnd_122958 56121381613897919964029 := by
  unfold tailWord_122958
  simp only [CollatzResearch.WordTrace]
  refine ⟨560580836068955049956191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2989764459034426933099685 560580836068955049956191)
  ·
    refine ⟨840871254103432574934287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 560580836068955049956191 840871254103432574934287)
    ·
      refine ⟨1261306881155148862401431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 840871254103432574934287 1261306881155148862401431)
      ·
        refine ⟨1891960321732723293602147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1261306881155148862401431 1891960321732723293602147)
        ·
          refine ⟨2837940482599084940403221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1891960321732723293602147 2837940482599084940403221)
          ·
            refine ⟨133028460121832106581401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2837940482599084940403221 133028460121832106581401)
            ·
              refine ⟨99771345091374079936051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133028460121832106581401 99771345091374079936051)
              ·
                refine ⟨149657017637061119904077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99771345091374079936051 149657017637061119904077)
                ·
                  refine ⟨56121381613897919964029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149657017637061119904077 56121381613897919964029)
                  ·
                    rfl

theorem cell20_122958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_122958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122958 prefixEnd_122958 := by exact prefixLift 122958
  have htrace : WordTrace (prefixWord ++ tailWord_122958) baseStart_122958 baseEnd_122958 := by
    simpa [prefixWord, tailWord_122958, baseEnd_122958] using wordTrace_append hprefix tailTrace_122958
  have hstable : (prefixWord ++ tailWord_122958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122958).length < 2 ^ (prefixWord ++ tailWord_122958).sum := by decide
  have hdescent : baseEnd_122958 < baseStart_122958 := by decide
  rcases family_descends (prefixWord ++ tailWord_122958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122976 : List Nat := [2, 1, 1, 3, 2, 3, 2, 6]
def baseStart_122976 : Nat := 118140960795 + 122976 * 2 ^ 59
def prefixEnd_122976 : Nat := 4983230072969 + 3 ^ 40 * 122976 * 2
def baseEnd_122976 : Nat := 18709865768123285787985

theorem tailTrace_122976 : CollatzResearch.WordTrace tailWord_122976 prefixEnd_122976 18709865768123285787985 := by
  unfold tailWord_122976
  simp only [CollatzResearch.WordTrace]
  refine ⟨2242651601243214736902391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2990202134990952982536521 2242651601243214736902391)
  ·
    refine ⟨3363977401864822105353587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2242651601243214736902391 3363977401864822105353587)
    ·
      refine ⟨5045966102797233158030381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3363977401864822105353587 5045966102797233158030381)
      ·
        refine ⟨1892237288548962434261393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5045966102797233158030381 1892237288548962434261393)
        ·
          refine ⟨1419177966411721825696045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1892237288548962434261393 1419177966411721825696045)
          ·
            refine ⟨532191737404395684636017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1419177966411721825696045 532191737404395684636017)
            ·
              refine ⟨399143803053296763477013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 532191737404395684636017 399143803053296763477013)
              ·
                refine ⟨18709865768123285787985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 399143803053296763477013 18709865768123285787985)
                ·
                  rfl

theorem cell20_122976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 6].length) (baseStart_122976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_122976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_122976 prefixEnd_122976 := by exact prefixLift 122976
  have htrace : WordTrace (prefixWord ++ tailWord_122976) baseStart_122976 baseEnd_122976 := by
    simpa [prefixWord, tailWord_122976, baseEnd_122976] using wordTrace_append hprefix tailTrace_122976
  have hstable : (prefixWord ++ tailWord_122976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122976).length < 2 ^ (prefixWord ++ tailWord_122976).sum := by decide
  have hdescent : baseEnd_122976 < baseStart_122976 := by decide
  rcases family_descends (prefixWord ++ tailWord_122976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123041 : List Nat := [1, 2, 3, 3, 1, 3, 2, 3, 2]
def baseStart_123041 : Nat := 118140960795 + 123041 * 2 ^ 59
def prefixEnd_123041 : Nat := 4983230072969 + 3 ^ 40 * 123041 * 2
def baseEnd_123041 : Nat := 56159265075518520197023

theorem tailTrace_123041 : CollatzResearch.WordTrace tailWord_123041 prefixEnd_123041 56159265075518520197023 := by
  unfold tailWord_123041
  simp only [CollatzResearch.WordTrace]
  refine ⟨4487673947250945574920977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2991782631500630383280651 4487673947250945574920977)
  ·
    refine ⟨3365755460438209181190733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4487673947250945574920977 3365755460438209181190733)
    ·
      refine ⟨1262158297664328442946525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3365755460438209181190733 1262158297664328442946525)
      ·
        refine ⟨473309361624123166104947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1262158297664328442946525 473309361624123166104947)
        ·
          refine ⟨709964042436184749157421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473309361624123166104947 709964042436184749157421)
          ·
            refine ⟨266236515913569280934033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 709964042436184749157421 266236515913569280934033)
            ·
              refine ⟨199677386935176960700525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266236515913569280934033 199677386935176960700525)
              ·
                refine ⟨74879020100691360262697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199677386935176960700525 74879020100691360262697)
                ·
                  refine ⟨56159265075518520197023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74879020100691360262697 56159265075518520197023)
                  ·
                    rfl

theorem cell20_123041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3, 2].length) (baseStart_123041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123041 prefixEnd_123041 := by exact prefixLift 123041
  have htrace : WordTrace (prefixWord ++ tailWord_123041) baseStart_123041 baseEnd_123041 := by
    simpa [prefixWord, tailWord_123041, baseEnd_123041] using wordTrace_append hprefix tailTrace_123041
  have hstable : (prefixWord ++ tailWord_123041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123041).length < 2 ^ (prefixWord ++ tailWord_123041).sum := by decide
  have hdescent : baseEnd_123041 < baseStart_123041 := by decide
  rcases family_descends (prefixWord ++ tailWord_123041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123086 : List Nat := [4, 1, 1, 1, 4, 3, 2, 4]
def baseStart_123086 : Nat := 118140960795 + 123086 * 2 ^ 59
def prefixEnd_123086 : Nat := 4983230072969 + 3 ^ 40 * 123086 * 2
def baseEnd_123086 : Nat := 18726601433899454565613

theorem tailTrace_123086 : CollatzResearch.WordTrace tailWord_123086 prefixEnd_123086 18726601433899454565613 := by
  unfold tailWord_123086
  simp only [CollatzResearch.WordTrace]
  refine ⟨561164404010989782538639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2992876821391945506872741 561164404010989782538639)
  ·
    refine ⟨841746606016484673807959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 561164404010989782538639 841746606016484673807959)
    ·
      refine ⟨1262619909024727010711939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 841746606016484673807959 1262619909024727010711939)
      ·
        refine ⟨1893929863537090516067909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1262619909024727010711939 1893929863537090516067909)
        ·
          refine ⟨355111849413204471762733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1893929863537090516067909 355111849413204471762733)
          ·
            refine ⟨133166943529951676911025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 355111849413204471762733 133166943529951676911025)
            ·
              refine ⟨99875207647463757683269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133166943529951676911025 99875207647463757683269)
              ·
                refine ⟨18726601433899454565613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99875207647463757683269 18726601433899454565613)
                ·
                  rfl

theorem cell20_123086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_123086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123086 prefixEnd_123086 := by exact prefixLift 123086
  have htrace : WordTrace (prefixWord ++ tailWord_123086) baseStart_123086 baseEnd_123086 := by
    simpa [prefixWord, tailWord_123086, baseEnd_123086] using wordTrace_append hprefix tailTrace_123086
  have hstable : (prefixWord ++ tailWord_123086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123086).length < 2 ^ (prefixWord ++ tailWord_123086).sum := by decide
  have hdescent : baseEnd_123086 < baseStart_123086 := by decide
  rcases family_descends (prefixWord ++ tailWord_123086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123097 : List Nat := [1, 2, 1, 2, 3, 1, 3, 2, 5]
def baseStart_123097 : Nat := 118140960795 + 123097 * 2 ^ 59
def prefixEnd_123097 : Nat := 4983230072969 + 3 ^ 40 * 123097 * 2
def baseEnd_123097 : Nat := 56184825001431214330127

theorem tailTrace_123097 : CollatzResearch.WordTrace tailWord_123097 prefixEnd_123097 56184825001431214330127 := by
  unfold tailWord_123097
  simp only [CollatzResearch.WordTrace]
  refine ⟨4489716435048067138959545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2993144290032044759306363 4489716435048067138959545)
  ·
    refine ⟨3367287326286050354219659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4489716435048067138959545 3367287326286050354219659)
    ·
      refine ⟨5050930989429075531329489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3367287326286050354219659 5050930989429075531329489)
      ·
        refine ⟨3788198242071806648497117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5050930989429075531329489 3788198242071806648497117)
        ·
          refine ⟨1420574340776927493186419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3788198242071806648497117 1420574340776927493186419)
          ·
            refine ⟨2130861511165391239779629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420574340776927493186419 2130861511165391239779629)
            ·
              refine ⟨799073066687021714917361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2130861511165391239779629 799073066687021714917361)
              ·
                refine ⟨599304800015266286188021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 799073066687021714917361 599304800015266286188021)
                ·
                  refine ⟨56184825001431214330127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 599304800015266286188021 56184825001431214330127)
                  ·
                    rfl

theorem cell20_123097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_123097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123097 prefixEnd_123097 := by exact prefixLift 123097
  have htrace : WordTrace (prefixWord ++ tailWord_123097) baseStart_123097 baseEnd_123097 := by
    simpa [prefixWord, tailWord_123097, baseEnd_123097] using wordTrace_append hprefix tailTrace_123097
  have hstable : (prefixWord ++ tailWord_123097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123097).length < 2 ^ (prefixWord ++ tailWord_123097).sum := by decide
  have hdescent : baseEnd_123097 < baseStart_123097 := by decide
  rcases family_descends (prefixWord ++ tailWord_123097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123114 : List Nat := [3, 1, 3, 1, 1, 2, 2, 4, 3]
def baseStart_123114 : Nat := 118140960795 + 123114 * 2 ^ 59
def prefixEnd_123114 : Nat := 4983230072969 + 3 ^ 40 * 123114 * 2
def baseEnd_123114 : Nat := 56192584264654710763391

theorem tailTrace_123114 : CollatzResearch.WordTrace tailWord_123114 prefixEnd_123114 56192584264654710763391 := by
  unfold tailWord_123114
  simp only [CollatzResearch.WordTrace]
  refine ⟨1122584118996619760582099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2993557650657652694885597 1122584118996619760582099)
  ·
    refine ⟨1683876178494929640873149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1122584118996619760582099 1683876178494929640873149)
    ·
      refine ⟨631453566935598615327431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1683876178494929640873149 631453566935598615327431)
      ·
        refine ⟨947180350403397922991147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631453566935598615327431 947180350403397922991147)
        ·
          refine ⟨1420770525605096884486721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947180350403397922991147 1420770525605096884486721)
          ·
            refine ⟨1065577894203822663365041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1420770525605096884486721 1065577894203822663365041)
            ·
              refine ⟨799183420652866997523781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1065577894203822663365041 799183420652866997523781)
              ·
                refine ⟨149846891372412562035709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 799183420652866997523781 149846891372412562035709)
                ·
                  refine ⟨56192584264654710763391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149846891372412562035709 56192584264654710763391)
                  ·
                    rfl

theorem cell20_123114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_123114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123114 prefixEnd_123114 := by exact prefixLift 123114
  have htrace : WordTrace (prefixWord ++ tailWord_123114) baseStart_123114 baseEnd_123114 := by
    simpa [prefixWord, tailWord_123114, baseEnd_123114] using wordTrace_append hprefix tailTrace_123114
  have hstable : (prefixWord ++ tailWord_123114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123114).length < 2 ^ (prefixWord ++ tailWord_123114).sum := by decide
  have hdescent : baseEnd_123114 < baseStart_123114 := by decide
  rcases family_descends (prefixWord ++ tailWord_123114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123117 : List Nat := [1, 5, 1, 2, 3, 2, 1, 1, 4]
def baseStart_123117 : Nat := 118140960795 + 123117 * 2 ^ 59
def prefixEnd_123117 : Nat := 4983230072969 + 3 ^ 40 * 123117 * 2
def baseEnd_123117 : Nat := 56193953546400033663379

theorem tailTrace_123117 : CollatzResearch.WordTrace tailWord_123117 prefixEnd_123117 56193953546400033663379 := by
  unfold tailWord_123117
  simp only [CollatzResearch.WordTrace]
  refine ⟨4490445894975610554687605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2993630596650407036458403 4490445894975610554687605)
  ·
    refine ⟨420979302653963489501963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4490445894975610554687605 420979302653963489501963)
    ·
      refine ⟨631468953980945234252945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420979302653963489501963 631468953980945234252945)
      ·
        refine ⟨473601715485708925689709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 631468953980945234252945 473601715485708925689709)
        ·
          refine ⟨177600643307140847133641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 473601715485708925689709 177600643307140847133641)
          ·
            refine ⟨133200482480355635350231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177600643307140847133641 133200482480355635350231)
            ·
              refine ⟨199800723720533453025347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133200482480355635350231 199800723720533453025347)
              ·
                refine ⟨299701085580800179538021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199800723720533453025347 299701085580800179538021)
                ·
                  refine ⟨56193953546400033663379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 299701085580800179538021 56193953546400033663379)
                  ·
                    rfl

theorem cell20_123117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_123117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123117 prefixEnd_123117 := by exact prefixLift 123117
  have htrace : WordTrace (prefixWord ++ tailWord_123117) baseStart_123117 baseEnd_123117 := by
    simpa [prefixWord, tailWord_123117, baseEnd_123117] using wordTrace_append hprefix tailTrace_123117
  have hstable : (prefixWord ++ tailWord_123117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123117).length < 2 ^ (prefixWord ++ tailWord_123117).sum := by decide
  have hdescent : baseEnd_123117 < baseStart_123117 := by decide
  rcases family_descends (prefixWord ++ tailWord_123117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123121 : List Nat := [1, 2, 2, 2, 2, 1, 5, 1, 4]
def baseStart_123121 : Nat := 118140960795 + 123121 * 2 ^ 59
def prefixEnd_123121 : Nat := 4983230072969 + 3 ^ 40 * 123121 * 2
def baseEnd_123121 : Nat := 56195779255393797530029

theorem tailTrace_123121 : CollatzResearch.WordTrace tailWord_123121 prefixEnd_123121 56195779255393797530029 := by
  unfold tailWord_123121
  simp only [CollatzResearch.WordTrace]
  refine ⟨4490591786961119237833217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2993727857974079491888811 4490591786961119237833217)
  ·
    refine ⟨3367943840220839428374913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4490591786961119237833217 3367943840220839428374913)
    ·
      refine ⟨2525957880165629571281185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3367943840220839428374913 2525957880165629571281185)
      ·
        refine ⟨1894468410124222178460889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2525957880165629571281185 1894468410124222178460889)
        ·
          refine ⟨1420851307593166633845667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1894468410124222178460889 1420851307593166633845667)
          ·
            refine ⟨2131276961389749950768501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420851307593166633845667 2131276961389749950768501)
            ·
              refine ⟨199807215130289057884547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2131276961389749950768501 199807215130289057884547)
              ·
                refine ⟨299710822695433586826821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199807215130289057884547 299710822695433586826821)
                ·
                  refine ⟨56195779255393797530029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 299710822695433586826821 56195779255393797530029)
                  ·
                    rfl

theorem cell20_123121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_123121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123121 prefixEnd_123121 := by exact prefixLift 123121
  have htrace : WordTrace (prefixWord ++ tailWord_123121) baseStart_123121 baseEnd_123121 := by
    simpa [prefixWord, tailWord_123121, baseEnd_123121] using wordTrace_append hprefix tailTrace_123121
  have hstable : (prefixWord ++ tailWord_123121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123121).length < 2 ^ (prefixWord ++ tailWord_123121).sum := by decide
  have hdescent : baseEnd_123121 < baseStart_123121 := by decide
  rcases family_descends (prefixWord ++ tailWord_123121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123172 : List Nat := [2, 3, 1, 3, 1, 4, 2, 2, 2]
def baseStart_123172 : Nat := 118140960795 + 123172 * 2 ^ 59
def prefixEnd_123172 : Nat := 4983230072969 + 3 ^ 40 * 123172 * 2
def baseEnd_123172 : Nat := 56219057045064286829821

theorem tailTrace_123172 : CollatzResearch.WordTrace tailWord_123172 prefixEnd_123172 56219057045064286829821 := by
  unfold tailWord_123172
  simp only [CollatzResearch.WordTrace]
  refine ⟨2246225954888177473969885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2994967939850903298626513 2246225954888177473969885)
  ·
    refine ⟨842334733083066552738707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2246225954888177473969885 842334733083066552738707)
    ·
      refine ⟨1263502099624599829108061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 842334733083066552738707 1263502099624599829108061)
      ·
        refine ⟨473813287359224935915523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1263502099624599829108061 473813287359224935915523)
        ·
          refine ⟨710719931038837403873285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473813287359224935915523 710719931038837403873285)
          ·
            refine ⟨133259987069782013226241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 710719931038837403873285 133259987069782013226241)
            ·
              refine ⟨99944990302336509919681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133259987069782013226241 99944990302336509919681)
              ·
                refine ⟨74958742726752382439761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99944990302336509919681 74958742726752382439761)
                ·
                  refine ⟨56219057045064286829821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74958742726752382439761 56219057045064286829821)
                  ·
                    rfl

theorem cell20_123172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_123172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123172 prefixEnd_123172 := by exact prefixLift 123172
  have htrace : WordTrace (prefixWord ++ tailWord_123172) baseStart_123172 baseEnd_123172 := by
    simpa [prefixWord, tailWord_123172, baseEnd_123172] using wordTrace_append hprefix tailTrace_123172
  have hstable : (prefixWord ++ tailWord_123172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123172).length < 2 ^ (prefixWord ++ tailWord_123172).sum := by decide
  have hdescent : baseEnd_123172 < baseStart_123172 := by decide
  rcases family_descends (prefixWord ++ tailWord_123172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123235 : List Nat := [1, 1, 1, 5, 2, 1, 4, 1, 4]
def baseStart_123235 : Nat := 118140960795 + 123235 * 2 ^ 59
def prefixEnd_123235 : Nat := 4983230072969 + 3 ^ 40 * 123235 * 2
def baseEnd_123235 : Nat := 56247811961716067729563

theorem tailTrace_123235 : CollatzResearch.WordTrace tailWord_123235 prefixEnd_123235 56247811961716067729563 := by
  unfold tailWord_123235
  simp only [CollatzResearch.WordTrace]
  refine ⟨4494749708548116707483159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2996499805698744471655439 4494749708548116707483159)
  ·
    refine ⟨6742124562822175061224739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4494749708548116707483159 6742124562822175061224739)
    ·
      refine ⟨10113186844233262591837109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6742124562822175061224739 10113186844233262591837109)
      ·
        refine ⟨948111266646868367984729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10113186844233262591837109 948111266646868367984729)
        ·
          refine ⟨711083449985151275988547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 948111266646868367984729 711083449985151275988547)
          ·
            refine ⟨1066625174977726913982821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711083449985151275988547 1066625174977726913982821)
            ·
              refine ⟨199992220308323796371779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1066625174977726913982821 199992220308323796371779)
              ·
                refine ⟨299988330462485694557669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199992220308323796371779 299988330462485694557669)
                ·
                  refine ⟨56247811961716067729563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 299988330462485694557669 56247811961716067729563)
                  ·
                    rfl

theorem cell20_123235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 4].length) (baseStart_123235 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123235 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123235 prefixEnd_123235 := by exact prefixLift 123235
  have htrace : WordTrace (prefixWord ++ tailWord_123235) baseStart_123235 baseEnd_123235 := by
    simpa [prefixWord, tailWord_123235, baseEnd_123235] using wordTrace_append hprefix tailTrace_123235
  have hstable : (prefixWord ++ tailWord_123235).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123235).length < 2 ^ (prefixWord ++ tailWord_123235).sum := by decide
  have hdescent : baseEnd_123235 < baseStart_123235 := by decide
  rcases family_descends (prefixWord ++ tailWord_123235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123245 : List Nat := [1, 5, 1, 1, 1, 2, 5, 1, 3]
def baseStart_123245 : Nat := 118140960795 + 123245 * 2 ^ 59
def prefixEnd_123245 : Nat := 4983230072969 + 3 ^ 40 * 123245 * 2
def baseEnd_123245 : Nat := 56252376234200477396189

theorem tailTrace_123245 : CollatzResearch.WordTrace tailWord_123245 prefixEnd_123245 56252376234200477396189 := by
  unfold tailWord_123245
  simp only [CollatzResearch.WordTrace]
  refine ⟨4495114438511888415347189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2996742959007925610231459 4495114438511888415347189)
  ·
    refine ⟨421416978610489538938799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4495114438511888415347189 421416978610489538938799)
    ·
      refine ⟨632125467915734308408199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421416978610489538938799 632125467915734308408199)
      ·
        refine ⟨948188201873601462612299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632125467915734308408199 948188201873601462612299)
        ·
          refine ⟨1422282302810402193918449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948188201873601462612299 1422282302810402193918449)
          ·
            refine ⟨1066711727107801645438837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1422282302810402193918449 1066711727107801645438837)
            ·
              refine ⟨100004224416356404259891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1066711727107801645438837 100004224416356404259891)
              ·
                refine ⟨150006336624534606389837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100004224416356404259891 150006336624534606389837)
                ·
                  refine ⟨56252376234200477396189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150006336624534606389837 56252376234200477396189)
                  ·
                    rfl

theorem cell20_123245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_123245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123245 prefixEnd_123245 := by exact prefixLift 123245
  have htrace : WordTrace (prefixWord ++ tailWord_123245) baseStart_123245 baseEnd_123245 := by
    simpa [prefixWord, tailWord_123245, baseEnd_123245] using wordTrace_append hprefix tailTrace_123245
  have hstable : (prefixWord ++ tailWord_123245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123245).length < 2 ^ (prefixWord ++ tailWord_123245).sum := by decide
  have hdescent : baseEnd_123245 < baseStart_123245 := by decide
  rcases family_descends (prefixWord ++ tailWord_123245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123259 : List Nat := [1, 1, 1, 1, 1, 9, 2, 4]
def baseStart_123259 : Nat := 118140960795 + 123259 * 2 ^ 59
def prefixEnd_123259 : Nat := 4983230072969 + 3 ^ 40 * 123259 * 2
def baseEnd_123259 : Nat := 18752922071892883643155

theorem tailTrace_123259 : CollatzResearch.WordTrace tailWord_123259 prefixEnd_123259 18752922071892883643155 := by
  unfold tailWord_123259
  simp only [CollatzResearch.WordTrace]
  refine ⟨4495625060461168806356831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2997083373640779204237887 4495625060461168806356831)
  ·
    refine ⟨6743437590691753209535247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4495625060461168806356831 6743437590691753209535247)
    ·
      refine ⟨10115156386037629814302871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6743437590691753209535247 10115156386037629814302871)
      ·
        refine ⟨15172734579056444721454307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10115156386037629814302871 15172734579056444721454307)
        ·
          refine ⟨22759101868584667082181461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15172734579056444721454307 22759101868584667082181461)
          ·
            refine ⟨133354112511238283684657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 22759101868584667082181461 133354112511238283684657)
            ·
              refine ⟨100015584383428712763493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133354112511238283684657 100015584383428712763493)
              ·
                refine ⟨18752922071892883643155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100015584383428712763493 18752922071892883643155)
                ·
                  rfl

theorem cell20_123259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 4].length) (baseStart_123259 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123259 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123259 prefixEnd_123259 := by exact prefixLift 123259
  have htrace : WordTrace (prefixWord ++ tailWord_123259) baseStart_123259 baseEnd_123259 := by
    simpa [prefixWord, tailWord_123259, baseEnd_123259] using wordTrace_append hprefix tailTrace_123259
  have hstable : (prefixWord ++ tailWord_123259).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123259).length < 2 ^ (prefixWord ++ tailWord_123259).sum := by decide
  have hdescent : baseEnd_123259 < baseStart_123259 := by decide
  rcases family_descends (prefixWord ++ tailWord_123259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123263 : List Nat := [1, 1, 2, 2, 1, 1, 2, 10]
def baseStart_123263 : Nat := 118140960795 + 123263 * 2 ^ 59
def prefixEnd_123263 : Nat := 4983230072969 + 3 ^ 40 * 123263 * 2
def baseEnd_123263 : Nat := 18753530641557471598705

theorem tailTrace_123263 : CollatzResearch.WordTrace tailWord_123263 prefixEnd_123263 18753530641557471598705 := by
  unfold tailWord_123263
  simp only [CollatzResearch.WordTrace]
  refine ⟨4495770952446677489502443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2997180634964451659668295 4495770952446677489502443)
  ·
    refine ⟨6743656428670016234253665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4495770952446677489502443 6743656428670016234253665)
    ·
      refine ⟨5057742321502512175690249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6743656428670016234253665 5057742321502512175690249)
      ·
        refine ⟨3793306741126884131767687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5057742321502512175690249 3793306741126884131767687)
        ·
          refine ⟨5689960111690326197651531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3793306741126884131767687 5689960111690326197651531)
          ·
            refine ⟨8534940167535489296477297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5689960111690326197651531 8534940167535489296477297)
            ·
              refine ⟨6401205125651616972357973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8534940167535489296477297 6401205125651616972357973)
              ·
                refine ⟨18753530641557471598705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6401205125651616972357973 18753530641557471598705)
                ·
                  rfl

theorem cell20_123263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 10].length) (baseStart_123263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123263 prefixEnd_123263 := by exact prefixLift 123263
  have htrace : WordTrace (prefixWord ++ tailWord_123263) baseStart_123263 baseEnd_123263 := by
    simpa [prefixWord, tailWord_123263, baseEnd_123263] using wordTrace_append hprefix tailTrace_123263
  have hstable : (prefixWord ++ tailWord_123263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123263).length < 2 ^ (prefixWord ++ tailWord_123263).sum := by decide
  have hdescent : baseEnd_123263 < baseStart_123263 := by decide
  rcases family_descends (prefixWord ++ tailWord_123263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123287 : List Nat := [1, 1, 3, 3, 1, 1, 4, 1, 5]
def baseStart_123287 : Nat := 118140960795 + 123287 * 2 ^ 59
def prefixEnd_123287 : Nat := 4983230072969 + 3 ^ 40 * 123287 * 2
def baseEnd_123287 : Nat := 56271546178634997996017

theorem tailTrace_123287 : CollatzResearch.WordTrace tailWord_123287 prefixEnd_123287 56271546178634997996017 := by
  unfold tailWord_123287
  simp only [CollatzResearch.WordTrace]
  refine ⟨4496646304359729588376115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2997764202906486392250743 4496646304359729588376115)
  ·
    refine ⟨6744969456539594382564173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4496646304359729588376115 6744969456539594382564173)
    ·
      refine ⟨2529363546202347893461565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6744969456539594382564173 2529363546202347893461565)
      ·
        refine ⟨948511329825880460048087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2529363546202347893461565 948511329825880460048087)
        ·
          refine ⟨1422766994738820690072131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948511329825880460048087 1422766994738820690072131)
          ·
            refine ⟨2134150492108231035108197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1422766994738820690072131 2134150492108231035108197)
            ·
              refine ⟨400153217270293319082787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2134150492108231035108197 400153217270293319082787)
              ·
                refine ⟨600229825905439978624181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400153217270293319082787 600229825905439978624181)
                ·
                  refine ⟨56271546178634997996017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 600229825905439978624181 56271546178634997996017)
                  ·
                    rfl

theorem cell20_123287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 5].length) (baseStart_123287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123287 prefixEnd_123287 := by exact prefixLift 123287
  have htrace : WordTrace (prefixWord ++ tailWord_123287) baseStart_123287 baseEnd_123287 := by
    simpa [prefixWord, tailWord_123287, baseEnd_123287] using wordTrace_append hprefix tailTrace_123287
  have hstable : (prefixWord ++ tailWord_123287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123287).length < 2 ^ (prefixWord ++ tailWord_123287).sum := by decide
  have hdescent : baseEnd_123287 < baseStart_123287 := by decide
  rcases family_descends (prefixWord ++ tailWord_123287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123290 : List Nat := [3, 1, 1, 4, 1, 4, 1, 1, 4]
def baseStart_123290 : Nat := 118140960795 + 123290 * 2 ^ 59
def prefixEnd_123290 : Nat := 4983230072969 + 3 ^ 40 * 123290 * 2
def baseEnd_123290 : Nat := 56272915460380320896005

theorem tailTrace_123290 : CollatzResearch.WordTrace tailWord_123290 prefixEnd_123290 56272915460380320896005 := by
  unfold tailWord_123290
  simp only [CollatzResearch.WordTrace]
  refine ⟨1124188930837215275183831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2997837148899240733823549 1124188930837215275183831)
  ·
    refine ⟨1686283396255822912775747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1124188930837215275183831 1686283396255822912775747)
    ·
      refine ⟨2529425094383734369163621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1686283396255822912775747 2529425094383734369163621)
      ·
        refine ⟨474267205196950194218179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2529425094383734369163621 474267205196950194218179)
        ·
          refine ⟨711400807795425291327269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474267205196950194218179 711400807795425291327269)
          ·
            refine ⟨133387651461642242123863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 711400807795425291327269 133387651461642242123863)
            ·
              refine ⟨200081477192463363185795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133387651461642242123863 200081477192463363185795)
              ·
                refine ⟨300122215788695044778693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200081477192463363185795 300122215788695044778693)
                ·
                  refine ⟨56272915460380320896005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 300122215788695044778693 56272915460380320896005)
                  ·
                    rfl

theorem cell20_123290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_123290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123290 prefixEnd_123290 := by exact prefixLift 123290
  have htrace : WordTrace (prefixWord ++ tailWord_123290) baseStart_123290 baseEnd_123290 := by
    simpa [prefixWord, tailWord_123290, baseEnd_123290] using wordTrace_append hprefix tailTrace_123290
  have hstable : (prefixWord ++ tailWord_123290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123290).length < 2 ^ (prefixWord ++ tailWord_123290).sum := by decide
  have hdescent : baseEnd_123290 < baseStart_123290 := by decide
  rcases family_descends (prefixWord ++ tailWord_123290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123401 : List Nat := [1, 2, 1, 1, 3, 1, 2, 6, 3]
def baseStart_123401 : Nat := 118140960795 + 123401 * 2 ^ 59
def prefixEnd_123401 : Nat := 4983230072969 + 3 ^ 40 * 123401 * 2
def baseEnd_123401 : Nat := 56323578884957268195551

theorem tailTrace_123401 : CollatzResearch.WordTrace tailWord_123401 prefixEnd_123401 56323578884957268195551 := by
  unfold tailWord_123401
  simp only [CollatzResearch.WordTrace]
  refine ⟨4500804225946727058026057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3000536150631151372017371 4500804225946727058026057)
  ·
    refine ⟨3375603169460045293519543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4500804225946727058026057 3375603169460045293519543)
    ·
      refine ⟨5063404754190067940279315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3375603169460045293519543 5063404754190067940279315)
      ·
        refine ⟨7595107131285101910418973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5063404754190067940279315 7595107131285101910418973)
        ·
          refine ⟨2848165174231913216407115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7595107131285101910418973 2848165174231913216407115)
          ·
            refine ⟨4272247761347869824610673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2848165174231913216407115 4272247761347869824610673)
            ·
              refine ⟨3204185821010902368458005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4272247761347869824610673 3204185821010902368458005)
              ·
                refine ⟨150196210359886048521469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3204185821010902368458005 150196210359886048521469)
                ·
                  refine ⟨56323578884957268195551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150196210359886048521469 56323578884957268195551)
                  ·
                    rfl

theorem cell20_123401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 3].length) (baseStart_123401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123401 prefixEnd_123401 := by exact prefixLift 123401
  have htrace : WordTrace (prefixWord ++ tailWord_123401) baseStart_123401 baseEnd_123401 := by
    simpa [prefixWord, tailWord_123401, baseEnd_123401] using wordTrace_append hprefix tailTrace_123401
  have hstable : (prefixWord ++ tailWord_123401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123401).length < 2 ^ (prefixWord ++ tailWord_123401).sum := by decide
  have hdescent : baseEnd_123401 < baseStart_123401 := by decide
  rcases family_descends (prefixWord ++ tailWord_123401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123404 : List Nat := [2, 2, 1, 2, 4, 1, 2, 4, 2]
def baseStart_123404 : Nat := 118140960795 + 123404 * 2 ^ 59
def prefixEnd_123404 : Nat := 4983230072969 + 3 ^ 40 * 123404 * 2
def baseEnd_123404 : Nat := 56324948166702591095539

theorem tailTrace_123404 : CollatzResearch.WordTrace tailWord_123404 prefixEnd_123404 56324948166702591095539 := by
  unfold tailWord_123404
  simp only [CollatzResearch.WordTrace]
  refine ⟨2250456822467929285192633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3000609096623905713590177 2250456822467929285192633)
  ·
    refine ⟨1687842616850946963894475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2250456822467929285192633 1687842616850946963894475)
    ·
      refine ⟨2531763925276420445841713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1687842616850946963894475 2531763925276420445841713)
      ·
        refine ⟨1898822943957315334381285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2531763925276420445841713 1898822943957315334381285)
        ·
          refine ⟨356029301991996625196491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1898822943957315334381285 356029301991996625196491)
          ·
            refine ⟨534043952987994937794737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356029301991996625196491 534043952987994937794737)
            ·
              refine ⟨400532964740996203346053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 534043952987994937794737 400532964740996203346053)
              ·
                refine ⟨75099930888936788127385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 400532964740996203346053 75099930888936788127385)
                ·
                  refine ⟨56324948166702591095539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75099930888936788127385 56324948166702591095539)
                  ·
                    rfl

theorem cell20_123404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 4, 2].length) (baseStart_123404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123404 prefixEnd_123404 := by exact prefixLift 123404
  have htrace : WordTrace (prefixWord ++ tailWord_123404) baseStart_123404 baseEnd_123404 := by
    simpa [prefixWord, tailWord_123404, baseEnd_123404] using wordTrace_append hprefix tailTrace_123404
  have hstable : (prefixWord ++ tailWord_123404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123404).length < 2 ^ (prefixWord ++ tailWord_123404).sum := by decide
  have hdescent : baseEnd_123404 < baseStart_123404 := by decide
  rcases family_descends (prefixWord ++ tailWord_123404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123438 : List Nat := [4, 1, 3, 1, 3, 2, 1, 3, 2]
def baseStart_123438 : Nat := 118140960795 + 123438 * 2 ^ 59
def prefixEnd_123438 : Nat := 4983230072969 + 3 ^ 40 * 123438 * 2
def baseEnd_123438 : Nat := 56340466693149583962067

theorem tailTrace_123438 : CollatzResearch.WordTrace tailWord_123438 prefixEnd_123438 56340466693149583962067 := by
  unfold tailWord_123438
  simp only [CollatzResearch.WordTrace]
  refine ⟨562769215851585297140371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3001435817875121584748645 562769215851585297140371)
  ·
    refine ⟨844153823777377945710557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 562769215851585297140371 844153823777377945710557)
    ·
      refine ⟨316557683916516729641459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 844153823777377945710557 316557683916516729641459)
      ·
        refine ⟨474836525874775094462189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316557683916516729641459 474836525874775094462189)
        ·
          refine ⟨178063697203040660423321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 474836525874775094462189 178063697203040660423321)
          ·
            refine ⟨133547772902280495317491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178063697203040660423321 133547772902280495317491)
            ·
              refine ⟨200321659353420742976237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133547772902280495317491 200321659353420742976237)
              ·
                refine ⟨75120622257532778616089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200321659353420742976237 75120622257532778616089)
                ·
                  refine ⟨56340466693149583962067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75120622257532778616089 56340466693149583962067)
                  ·
                    rfl

theorem cell20_123438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_123438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123438 prefixEnd_123438 := by exact prefixLift 123438
  have htrace : WordTrace (prefixWord ++ tailWord_123438) baseStart_123438 baseEnd_123438 := by
    simpa [prefixWord, tailWord_123438, baseEnd_123438] using wordTrace_append hprefix tailTrace_123438
  have hstable : (prefixWord ++ tailWord_123438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123438).length < 2 ^ (prefixWord ++ tailWord_123438).sum := by decide
  have hdescent : baseEnd_123438 < baseStart_123438 := by decide
  rcases family_descends (prefixWord ++ tailWord_123438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123442 : List Nat := [3, 2, 1, 1, 2, 1, 5, 3, 2]
def baseStart_123442 : Nat := 118140960795 + 123442 * 2 ^ 59
def prefixEnd_123442 : Nat := 4983230072969 + 3 ^ 40 * 123442 * 2
def baseEnd_123442 : Nat := 56342292402143347828717

theorem tailTrace_123442 : CollatzResearch.WordTrace tailWord_123442 prefixEnd_123442 56342292402143347828717 := by
  unfold tailWord_123442
  simp only [CollatzResearch.WordTrace]
  refine ⟨1125574904699547765067145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3001533079198794040179053 1125574904699547765067145)
  ·
    refine ⟨844181178524660823800359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1125574904699547765067145 844181178524660823800359)
    ·
      refine ⟨1266271767786991235700539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 844181178524660823800359 1266271767786991235700539)
      ·
        refine ⟨1899407651680486853550809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1266271767786991235700539 1899407651680486853550809)
        ·
          refine ⟨1424555738760365140163107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1899407651680486853550809 1424555738760365140163107)
          ·
            refine ⟨2136833608140547710244661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424555738760365140163107 2136833608140547710244661)
            ·
              refine ⟨200328150763176347835437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2136833608140547710244661 200328150763176347835437)
              ·
                refine ⟨75123056536191130438289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200328150763176347835437 75123056536191130438289)
                ·
                  refine ⟨56342292402143347828717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75123056536191130438289 56342292402143347828717)
                  ·
                    rfl

theorem cell20_123442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_123442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123442 prefixEnd_123442 := by exact prefixLift 123442
  have htrace : WordTrace (prefixWord ++ tailWord_123442) baseStart_123442 baseEnd_123442 := by
    simpa [prefixWord, tailWord_123442, baseEnd_123442] using wordTrace_append hprefix tailTrace_123442
  have hstable : (prefixWord ++ tailWord_123442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123442).length < 2 ^ (prefixWord ++ tailWord_123442).sum := by decide
  have hdescent : baseEnd_123442 < baseStart_123442 := by decide
  rcases family_descends (prefixWord ++ tailWord_123442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123463 : List Nat := [1, 1, 4, 1, 4, 1, 3, 1, 4]
def baseStart_123463 : Nat := 118140960795 + 123463 * 2 ^ 59
def prefixEnd_123463 : Nat := 4983230072969 + 3 ^ 40 * 123463 * 2
def baseEnd_123463 : Nat := 56351877374360608128631

theorem tailTrace_123463 : CollatzResearch.WordTrace tailWord_123463 prefixEnd_123463 56351877374360608128631 := by
  unfold tailWord_123463
  simp only [CollatzResearch.WordTrace]
  refine ⟨4503065551722111646783043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3002043701148074431188695 4503065551722111646783043)
  ·
    refine ⟨6754598327583167470174565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4503065551722111646783043 6754598327583167470174565)
    ·
      refine ⟨1266487186421843900657731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6754598327583167470174565 1266487186421843900657731)
      ·
        refine ⟨1899730779632765850986597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1266487186421843900657731 1899730779632765850986597)
        ·
          refine ⟨356199521181143597059987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1899730779632765850986597 356199521181143597059987)
          ·
            refine ⟨534299281771715395589981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356199521181143597059987 534299281771715395589981)
            ·
              refine ⟨200362230664393273346243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 534299281771715395589981 200362230664393273346243)
              ·
                refine ⟨300543345996589910019365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200362230664393273346243 300543345996589910019365)
                ·
                  refine ⟨56351877374360608128631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 300543345996589910019365 56351877374360608128631)
                  ·
                    rfl

theorem cell20_123463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 4].length) (baseStart_123463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123463 prefixEnd_123463 := by exact prefixLift 123463
  have htrace : WordTrace (prefixWord ++ tailWord_123463) baseStart_123463 baseEnd_123463 := by
    simpa [prefixWord, tailWord_123463, baseEnd_123463] using wordTrace_append hprefix tailTrace_123463
  have hstable : (prefixWord ++ tailWord_123463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123463).length < 2 ^ (prefixWord ++ tailWord_123463).sum := by decide
  have hdescent : baseEnd_123463 < baseStart_123463 := by decide
  rcases family_descends (prefixWord ++ tailWord_123463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123473 : List Nat := [1, 2, 2, 1, 3, 5, 2, 1, 3]
def baseStart_123473 : Nat := 118140960795 + 123473 * 2 ^ 59
def prefixEnd_123473 : Nat := 4983230072969 + 3 ^ 40 * 123473 * 2
def baseEnd_123473 : Nat := 56356441646845017795257

theorem tailTrace_123473 : CollatzResearch.WordTrace tailWord_123473 prefixEnd_123473 56356441646845017795257 := by
  unfold tailWord_123473
  simp only [CollatzResearch.WordTrace]
  refine ⟨4503430281685883354647073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3002286854457255569764715 4503430281685883354647073)
  ·
    refine ⟨3377572711264412515985305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4503430281685883354647073 3377572711264412515985305)
    ·
      refine ⟨2533179533448309386988979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3377572711264412515985305 2533179533448309386988979)
      ·
        refine ⟨3799769300172464080483469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2533179533448309386988979 3799769300172464080483469)
        ·
          refine ⟨1424913487564674030181301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3799769300172464080483469 1424913487564674030181301)
          ·
            refine ⟨133585639459188190329497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1424913487564674030181301 133585639459188190329497)
            ·
              refine ⟨100189229594391142747123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133585639459188190329497 100189229594391142747123)
              ·
                refine ⟨150283844391586714120685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100189229594391142747123 150283844391586714120685)
                ·
                  refine ⟨56356441646845017795257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150283844391586714120685 56356441646845017795257)
                  ·
                    rfl

theorem cell20_123473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 3].length) (baseStart_123473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123473 prefixEnd_123473 := by exact prefixLift 123473
  have htrace : WordTrace (prefixWord ++ tailWord_123473) baseStart_123473 baseEnd_123473 := by
    simpa [prefixWord, tailWord_123473, baseEnd_123473] using wordTrace_append hprefix tailTrace_123473
  have hstable : (prefixWord ++ tailWord_123473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123473).length < 2 ^ (prefixWord ++ tailWord_123473).sum := by decide
  have hdescent : baseEnd_123473 < baseStart_123473 := by decide
  rcases family_descends (prefixWord ++ tailWord_123473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123491 : List Nat := [1, 1, 1, 5, 1, 2, 1, 8]
def baseStart_123491 : Nat := 118140960795 + 123491 * 2 ^ 59
def prefixEnd_123491 : Nat := 4983230072969 + 3 ^ 40 * 123491 * 2
def baseEnd_123491 : Nat := 18788219112438985065061

theorem tailTrace_123491 : CollatzResearch.WordTrace tailWord_123491 prefixEnd_123491 18788219112438985065061 := by
  unfold tailWord_123491
  simp only [CollatzResearch.WordTrace]
  refine ⟨4504086795620672428802327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3002724530413781619201551 4504086795620672428802327)
  ·
    refine ⟨6756130193431008643203491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4504086795620672428802327 6756130193431008643203491)
    ·
      refine ⟨10134195290146512964805237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6756130193431008643203491 10134195290146512964805237)
      ·
        refine ⟨950080808451235590450491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10134195290146512964805237 950080808451235590450491)
        ·
          refine ⟨1425121212676853385675737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 950080808451235590450491 1425121212676853385675737)
          ·
            refine ⟨1068840909507640039256803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1425121212676853385675737 1068840909507640039256803)
            ·
              refine ⟨1603261364261460058885205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068840909507640039256803 1603261364261460058885205)
              ·
                refine ⟨18788219112438985065061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1603261364261460058885205 18788219112438985065061)
                ·
                  rfl

theorem cell20_123491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 8].length) (baseStart_123491 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123491 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123491 prefixEnd_123491 := by exact prefixLift 123491
  have htrace : WordTrace (prefixWord ++ tailWord_123491) baseStart_123491 baseEnd_123491 := by
    simpa [prefixWord, tailWord_123491, baseEnd_123491] using wordTrace_append hprefix tailTrace_123491
  have hstable : (prefixWord ++ tailWord_123491).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123491).length < 2 ^ (prefixWord ++ tailWord_123491).sum := by decide
  have hdescent : baseEnd_123491 < baseStart_123491 := by decide
  rcases family_descends (prefixWord ++ tailWord_123491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123536 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 9]
def baseStart_123536 : Nat := 118140960795 + 123536 * 2 ^ 59
def prefixEnd_123536 : Nat := 4983230072969 + 3 ^ 40 * 123536 * 2
def baseEnd_123536 : Nat := 56385196563496798694999

theorem tailTrace_123536 : CollatzResearch.WordTrace tailWord_123536 prefixEnd_123536 56385196563496798694999 := by
  unfold tailWord_123536
  simp only [CollatzResearch.WordTrace]
  refine ⟨2252864040228822557095231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3003818720305096742793641 2252864040228822557095231)
  ·
    refine ⟨3379296060343233835642847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2252864040228822557095231 3379296060343233835642847)
    ·
      refine ⟨5068944090514850753464271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3379296060343233835642847 5068944090514850753464271)
      ·
        refine ⟨7603416135772276130196407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5068944090514850753464271 7603416135772276130196407)
        ·
          refine ⟨11405124203658414195294611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7603416135772276130196407 11405124203658414195294611)
          ·
            refine ⟨17107686305487621292941917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11405124203658414195294611 17107686305487621292941917)
            ·
              refine ⟨6415382364557857984853219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17107686305487621292941917 6415382364557857984853219)
              ·
                refine ⟨9623073546836786977279829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6415382364557857984853219 9623073546836786977279829)
                ·
                  refine ⟨56385196563496798694999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9623073546836786977279829 56385196563496798694999)
                  ·
                    rfl

theorem cell20_123536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_123536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123536 prefixEnd_123536 := by exact prefixLift 123536
  have htrace : WordTrace (prefixWord ++ tailWord_123536) baseStart_123536 baseEnd_123536 := by
    simpa [prefixWord, tailWord_123536, baseEnd_123536] using wordTrace_append hprefix tailTrace_123536
  have hstable : (prefixWord ++ tailWord_123536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123536).length < 2 ^ (prefixWord ++ tailWord_123536).sum := by decide
  have hdescent : baseEnd_123536 < baseStart_123536 := by decide
  rcases family_descends (prefixWord ++ tailWord_123536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123556 : List Nat := [2, 3, 1, 2, 2, 1, 4, 3, 2]
def baseStart_123556 : Nat := 118140960795 + 123556 * 2 ^ 59
def prefixEnd_123556 : Nat := 4983230072969 + 3 ^ 40 * 123556 * 2
def baseEnd_123556 : Nat := 56394325108465618028251

theorem tailTrace_123556 : CollatzResearch.WordTrace tailWord_123556 prefixEnd_123556 56394325108465618028251 := by
  unfold tailWord_123556
  simp only [CollatzResearch.WordTrace]
  refine ⟨2253228770192594264959261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3004305026923459019945681 2253228770192594264959261)
  ·
    refine ⟨844960788822222849359723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2253228770192594264959261 844960788822222849359723)
    ·
      refine ⟨1267441183233334274039585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 844960788822222849359723 1267441183233334274039585)
      ·
        refine ⟨950580887425000705529689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1267441183233334274039585 950580887425000705529689)
        ·
          refine ⟨712935665568750529147267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 950580887425000705529689 712935665568750529147267)
          ·
            refine ⟨1069403498353125793720901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712935665568750529147267 1069403498353125793720901)
            ·
              refine ⟨200513155941211086322669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1069403498353125793720901 200513155941211086322669)
              ·
                refine ⟨75192433477954157371001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200513155941211086322669 75192433477954157371001)
                ·
                  refine ⟨56394325108465618028251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75192433477954157371001 56394325108465618028251)
                  ·
                    rfl

theorem cell20_123556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_123556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123556 prefixEnd_123556 := by exact prefixLift 123556
  have htrace : WordTrace (prefixWord ++ tailWord_123556) baseStart_123556 baseEnd_123556 := by
    simpa [prefixWord, tailWord_123556, baseEnd_123556] using wordTrace_append hprefix tailTrace_123556
  have hstable : (prefixWord ++ tailWord_123556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123556).length < 2 ^ (prefixWord ++ tailWord_123556).sum := by decide
  have hdescent : baseEnd_123556 < baseStart_123556 := by decide
  rcases family_descends (prefixWord ++ tailWord_123556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123566 : List Nat := [4, 1, 4, 1, 1, 3, 1, 2, 3]
def baseStart_123566 : Nat := 118140960795 + 123566 * 2 ^ 59
def prefixEnd_123566 : Nat := 4983230072969 + 3 ^ 40 * 123566 * 2
def baseEnd_123566 : Nat := 56398889380950027694877

theorem tailTrace_123566 : CollatzResearch.WordTrace tailWord_123566 prefixEnd_123566 56398889380950027694877 := by
  unfold tailWord_123566
  simp only [CollatzResearch.WordTrace]
  refine ⟨563352783793620029722819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3004548180232640158521701 563352783793620029722819)
  ·
    refine ⟨845029175690430044584229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 563352783793620029722819 845029175690430044584229)
    ·
      refine ⟨158442970441955633359543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 845029175690430044584229 158442970441955633359543)
      ·
        refine ⟨237664455662933450039315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158442970441955633359543 237664455662933450039315)
        ·
          refine ⟨356496683494400175058973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237664455662933450039315 356496683494400175058973)
          ·
            refine ⟨133686256310400065647115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 356496683494400175058973 133686256310400065647115)
            ·
              refine ⟨200529384465600098470673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133686256310400065647115 200529384465600098470673)
              ·
                refine ⟨150397038349200073853005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200529384465600098470673 150397038349200073853005)
                ·
                  refine ⟨56398889380950027694877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150397038349200073853005 56398889380950027694877)
                  ·
                    rfl

theorem cell20_123566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_123566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123566 prefixEnd_123566 := by exact prefixLift 123566
  have htrace : WordTrace (prefixWord ++ tailWord_123566) baseStart_123566 baseEnd_123566 := by
    simpa [prefixWord, tailWord_123566, baseEnd_123566] using wordTrace_append hprefix tailTrace_123566
  have hstable : (prefixWord ++ tailWord_123566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123566).length < 2 ^ (prefixWord ++ tailWord_123566).sum := by decide
  have hdescent : baseEnd_123566 < baseStart_123566 := by decide
  rcases family_descends (prefixWord ++ tailWord_123566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123567 : List Nat := [1, 1, 2, 1, 2, 6, 7]
def baseStart_123567 : Nat := 118140960795 + 123567 * 2 ^ 59
def prefixEnd_123567 : Nat := 4983230072969 + 3 ^ 40 * 123567 * 2
def baseEnd_123567 : Nat := 6266593978688718740171

theorem tailTrace_123567 : CollatzResearch.WordTrace tailWord_123567 prefixEnd_123567 6266593978688718740171 := by
  unfold tailWord_123567
  simp only [CollatzResearch.WordTrace]
  refine ⟨4506858743345337408568955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3004572495563558272379303 4506858743345337408568955)
  ·
    refine ⟨6760288115018006112853433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4506858743345337408568955 6760288115018006112853433)
    ·
      refine ⟨5070216086263504584640075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6760288115018006112853433 5070216086263504584640075)
      ·
        refine ⟨7605324129395256876960113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5070216086263504584640075 7605324129395256876960113)
        ·
          refine ⟨5703993097046442657720085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7605324129395256876960113 5703993097046442657720085)
          ·
            refine ⟨267374676424051999580629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5703993097046442657720085 267374676424051999580629)
            ·
              refine ⟨6266593978688718740171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 267374676424051999580629 6266593978688718740171)
              ·
                rfl

theorem cell20_123567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 7].length) (baseStart_123567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123567 prefixEnd_123567 := by exact prefixLift 123567
  have htrace : WordTrace (prefixWord ++ tailWord_123567) baseStart_123567 baseEnd_123567 := by
    simpa [prefixWord, tailWord_123567, baseEnd_123567] using wordTrace_append hprefix tailTrace_123567
  have hstable : (prefixWord ++ tailWord_123567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123567).length < 2 ^ (prefixWord ++ tailWord_123567).sum := by decide
  have hdescent : baseEnd_123567 < baseStart_123567 := by decide
  rcases family_descends (prefixWord ++ tailWord_123567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123597 : List Nat := [1, 6, 2, 1, 2, 2, 2, 4]
def baseStart_123597 : Nat := 118140960795 + 123597 * 2 ^ 59
def prefixEnd_123597 : Nat := 4983230072969 + 3 ^ 40 * 123597 * 2
def baseEnd_123597 : Nat := 18804346208550565887139

theorem tailTrace_123597 : CollatzResearch.WordTrace tailWord_123597 prefixEnd_123597 18804346208550565887139 := by
  unfold tailWord_123597
  simp only [CollatzResearch.WordTrace]
  refine ⟨4507952933236652532161045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3005301955491101688107363 4507952933236652532161045)
  ·
    refine ⟨211310293745468087445049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4507952933236652532161045 211310293745468087445049)
    ·
      refine ⟨158482720309101065583787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211310293745468087445049 158482720309101065583787)
      ·
        refine ⟨237724080463651598375681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158482720309101065583787 237724080463651598375681)
        ·
          refine ⟨178293060347738698781761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237724080463651598375681 178293060347738698781761)
          ·
            refine ⟨133719795260804024086321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178293060347738698781761 133719795260804024086321)
            ·
              refine ⟨100289846445603018064741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133719795260804024086321 100289846445603018064741)
              ·
                refine ⟨18804346208550565887139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100289846445603018064741 18804346208550565887139)
                ·
                  rfl

theorem cell20_123597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 4].length) (baseStart_123597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123597 prefixEnd_123597 := by exact prefixLift 123597
  have htrace : WordTrace (prefixWord ++ tailWord_123597) baseStart_123597 baseEnd_123597 := by
    simpa [prefixWord, tailWord_123597, baseEnd_123597] using wordTrace_append hprefix tailTrace_123597
  have hstable : (prefixWord ++ tailWord_123597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123597).length < 2 ^ (prefixWord ++ tailWord_123597).sum := by decide
  have hdescent : baseEnd_123597 < baseStart_123597 := by decide
  rcases family_descends (prefixWord ++ tailWord_123597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123629 : List Nat := [1, 5, 1, 2, 1, 1, 1, 3, 5]
def baseStart_123629 : Nat := 118140960795 + 123629 * 2 ^ 59
def prefixEnd_123629 : Nat := 4983230072969 + 3 ^ 40 * 123629 * 2
def baseEnd_123629 : Nat := 56427644297601808594619

theorem tailTrace_123629 : CollatzResearch.WordTrace tailWord_123629 prefixEnd_123629 56427644297601808594619 := by
  unfold tailWord_123629
  simp only [CollatzResearch.WordTrace]
  refine ⟨4509120069120721997325941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3006080046080481331550627 4509120069120721997325941)
  ·
    refine ⟨422730006480067687249307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4509120069120721997325941 422730006480067687249307)
    ·
      refine ⟨634095009720101530873961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422730006480067687249307 634095009720101530873961)
      ·
        refine ⟨475571257290076148155471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 634095009720101530873961 475571257290076148155471)
        ·
          refine ⟨713356885935114222233207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475571257290076148155471 713356885935114222233207)
          ·
            refine ⟨1070035328902671333349811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713356885935114222233207 1070035328902671333349811)
            ·
              refine ⟨1605052993354007000024717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1070035328902671333349811 1605052993354007000024717)
              ·
                refine ⟨601894872507752625009269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1605052993354007000024717 601894872507752625009269)
                ·
                  refine ⟨56427644297601808594619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 601894872507752625009269 56427644297601808594619)
                  ·
                    rfl

theorem cell20_123629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_123629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123629 prefixEnd_123629 := by exact prefixLift 123629
  have htrace : WordTrace (prefixWord ++ tailWord_123629) baseStart_123629 baseEnd_123629 := by
    simpa [prefixWord, tailWord_123629, baseEnd_123629] using wordTrace_append hprefix tailTrace_123629
  have hstable : (prefixWord ++ tailWord_123629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123629).length < 2 ^ (prefixWord ++ tailWord_123629).sum := by decide
  have hdescent : baseEnd_123629 < baseStart_123629 := by decide
  rcases family_descends (prefixWord ++ tailWord_123629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123632 : List Nat := [2, 1, 1, 1, 3, 1, 7, 2, 2]
def baseStart_123632 : Nat := 118140960795 + 123632 * 2 ^ 59
def prefixEnd_123632 : Nat := 4983230072969 + 3 ^ 40 * 123632 * 2
def baseEnd_123632 : Nat := 56429013579347131494607

theorem tailTrace_123632 : CollatzResearch.WordTrace tailWord_123632 prefixEnd_123632 56429013579347131494607 := by
  unfold tailWord_123632
  simp only [CollatzResearch.WordTrace]
  refine ⟨2254614744054926754842575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3006152992073235673123433 2254614744054926754842575)
  ·
    refine ⟨3381922116082390132263863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2254614744054926754842575 3381922116082390132263863)
    ·
      refine ⟨5072883174123585198395795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3381922116082390132263863 5072883174123585198395795)
      ·
        refine ⟨7609324761185377797593693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5072883174123585198395795 7609324761185377797593693)
        ·
          refine ⟨2853496785444516674097635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7609324761185377797593693 2853496785444516674097635)
          ·
            refine ⟨4280245178166775011146453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2853496785444516674097635 4280245178166775011146453)
            ·
              refine ⟨100318246363283789323745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 4280245178166775011146453 100318246363283789323745)
              ·
                refine ⟨75238684772462841992809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100318246363283789323745 75238684772462841992809)
                ·
                  refine ⟨56429013579347131494607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75238684772462841992809 56429013579347131494607)
                  ·
                    rfl

theorem cell20_123632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 2, 2].length) (baseStart_123632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123632 prefixEnd_123632 := by exact prefixLift 123632
  have htrace : WordTrace (prefixWord ++ tailWord_123632) baseStart_123632 baseEnd_123632 := by
    simpa [prefixWord, tailWord_123632, baseEnd_123632] using wordTrace_append hprefix tailTrace_123632
  have hstable : (prefixWord ++ tailWord_123632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123632).length < 2 ^ (prefixWord ++ tailWord_123632).sum := by decide
  have hdescent : baseEnd_123632 < baseStart_123632 := by decide
  rcases family_descends (prefixWord ++ tailWord_123632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123677 : List Nat := [1, 4, 2, 4, 2, 7]
def baseStart_123677 : Nat := 118140960795 + 123677 * 2 ^ 59
def prefixEnd_123677 : Nat := 4983230072969 + 3 ^ 40 * 123677 * 2
def baseEnd_123677 : Nat := 2090724177982480555349

theorem tailTrace_123677 : CollatzResearch.WordTrace tailWord_123677 prefixEnd_123677 2090724177982480555349 := by
  unfold tailWord_123677
  simp only [CollatzResearch.WordTrace]
  refine ⟨4510870772946826195073285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3007247181964550796715523 4510870772946826195073285)
  ·
    refine ⟨845788269927529911576241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4510870772946826195073285 845788269927529911576241)
    ·
      refine ⟨634341202445647433682181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 845788269927529911576241 634341202445647433682181)
      ·
        refine ⟨118938975458558893815409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 634341202445647433682181 118938975458558893815409)
        ·
          refine ⟨89204231593919170361557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118938975458558893815409 89204231593919170361557)
          ·
            refine ⟨2090724177982480555349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 89204231593919170361557 2090724177982480555349)
            ·
              rfl

theorem cell20_123677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 7].length) (baseStart_123677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123677 prefixEnd_123677 := by exact prefixLift 123677
  have htrace : WordTrace (prefixWord ++ tailWord_123677) baseStart_123677 baseEnd_123677 := by
    simpa [prefixWord, tailWord_123677, baseEnd_123677] using wordTrace_append hprefix tailTrace_123677
  have hstable : (prefixWord ++ tailWord_123677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123677).length < 2 ^ (prefixWord ++ tailWord_123677).sum := by decide
  have hdescent : baseEnd_123677 < baseStart_123677 := by decide
  rcases family_descends (prefixWord ++ tailWord_123677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123746 : List Nat := [3, 3, 2, 1, 3, 1, 2, 1, 4]
def baseStart_123746 : Nat := 118140960795 + 123746 * 2 ^ 59
def prefixEnd_123746 : Nat := 4983230072969 + 3 ^ 40 * 123746 * 2
def baseEnd_123746 : Nat := 56481046285669401694141

theorem tailTrace_123746 : CollatzResearch.WordTrace tailWord_123746 prefixEnd_123746 56481046285669401694141 := by
  unfold tailWord_123746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1128346852424212744833773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3008924939797900652890061 1128346852424212744833773)
  ·
    refine ⟨423130069659079779312665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1128346852424212744833773 423130069659079779312665)
    ·
      refine ⟨317347552244309834484499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423130069659079779312665 317347552244309834484499)
      ·
        refine ⟨476021328366464751726749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317347552244309834484499 476021328366464751726749)
        ·
          refine ⟨178507998137424281897531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 476021328366464751726749 178507998137424281897531)
          ·
            refine ⟨267761997206136422846297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178507998137424281897531 267761997206136422846297)
            ·
              refine ⟨200821497904602317134723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267761997206136422846297 200821497904602317134723)
              ·
                refine ⟨301232246856903475702085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200821497904602317134723 301232246856903475702085)
                ·
                  refine ⟨56481046285669401694141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 301232246856903475702085 56481046285669401694141)
                  ·
                    rfl

theorem cell20_123746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_123746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123746 prefixEnd_123746 := by exact prefixLift 123746
  have htrace : WordTrace (prefixWord ++ tailWord_123746) baseStart_123746 baseEnd_123746 := by
    simpa [prefixWord, tailWord_123746, baseEnd_123746] using wordTrace_append hprefix tailTrace_123746
  have hstable : (prefixWord ++ tailWord_123746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123746).length < 2 ^ (prefixWord ++ tailWord_123746).sum := by decide
  have hdescent : baseEnd_123746 < baseStart_123746 := by decide
  rcases family_descends (prefixWord ++ tailWord_123746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123757 : List Nat := [1, 5, 1, 1, 1, 1, 1, 9]
def baseStart_123757 : Nat := 118140960795 + 123757 * 2 ^ 59
def prefixEnd_123757 : Nat := 4983230072969 + 3 ^ 40 * 123757 * 2
def baseEnd_123757 : Nat := 18828688995134084109143

theorem tailTrace_123757 : CollatzResearch.WordTrace tailWord_123757 prefixEnd_123757 18828688995134084109143 := by
  unfold tailWord_123757
  simp only [CollatzResearch.WordTrace]
  refine ⟨4513788612656999857985525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3009192408437999905323683 4513788612656999857985525)
  ·
    refine ⟨423167682436593736686143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4513788612656999857985525 423167682436593736686143)
    ·
      refine ⟨634751523654890605029215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423167682436593736686143 634751523654890605029215)
      ·
        refine ⟨952127285482335907543823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634751523654890605029215 952127285482335907543823)
        ·
          refine ⟨1428190928223503861315735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 952127285482335907543823 1428190928223503861315735)
          ·
            refine ⟨2142286392335255791973603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1428190928223503861315735 2142286392335255791973603)
            ·
              refine ⟨3213429588502883687960405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2142286392335255791973603 3213429588502883687960405)
              ·
                refine ⟨18828688995134084109143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3213429588502883687960405 18828688995134084109143)
                ·
                  rfl

theorem cell20_123757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 9].length) (baseStart_123757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123757 prefixEnd_123757 := by exact prefixLift 123757
  have htrace : WordTrace (prefixWord ++ tailWord_123757) baseStart_123757 baseEnd_123757 := by
    simpa [prefixWord, tailWord_123757, baseEnd_123757] using wordTrace_append hprefix tailTrace_123757
  have hstable : (prefixWord ++ tailWord_123757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123757).length < 2 ^ (prefixWord ++ tailWord_123757).sum := by decide
  have hdescent : baseEnd_123757 < baseStart_123757 := by decide
  rcases family_descends (prefixWord ++ tailWord_123757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123784 : List Nat := [2, 1, 3, 3, 2, 1, 3, 3, 2]
def baseStart_123784 : Nat := 118140960795 + 123784 * 2 ^ 59
def prefixEnd_123784 : Nat := 4983230072969 + 3 ^ 40 * 123784 * 2
def baseEnd_123784 : Nat := 56498390521110158427319

theorem tailTrace_123784 : CollatzResearch.WordTrace tailWord_123784 prefixEnd_123784 56498390521110158427319 := by
  unfold tailWord_123784
  simp only [CollatzResearch.WordTrace]
  refine ⟨2257386691779591734609203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3009848922372788979478937 2257386691779591734609203)
  ·
    refine ⟨3386080037669387601913805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2257386691779591734609203 3386080037669387601913805)
    ·
      refine ⟨1269780014126020350717677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3386080037669387601913805 1269780014126020350717677)
      ·
        refine ⟨476167505297257631519129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1269780014126020350717677 476167505297257631519129)
        ·
          refine ⟨357125628972943223639347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476167505297257631519129 357125628972943223639347)
          ·
            refine ⟨535688443459414835459021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357125628972943223639347 535688443459414835459021)
            ·
              refine ⟨200883166297280563297133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 535688443459414835459021 200883166297280563297133)
              ·
                refine ⟨75331187361480211236425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200883166297280563297133 75331187361480211236425)
                ·
                  refine ⟨56498390521110158427319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75331187361480211236425 56498390521110158427319)
                  ·
                    rfl

theorem cell20_123784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 3, 2].length) (baseStart_123784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123784 prefixEnd_123784 := by exact prefixLift 123784
  have htrace : WordTrace (prefixWord ++ tailWord_123784) baseStart_123784 baseEnd_123784 := by
    simpa [prefixWord, tailWord_123784, baseEnd_123784] using wordTrace_append hprefix tailTrace_123784
  have hstable : (prefixWord ++ tailWord_123784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123784).length < 2 ^ (prefixWord ++ tailWord_123784).sum := by decide
  have hdescent : baseEnd_123784 < baseStart_123784 := by decide
  rcases family_descends (prefixWord ++ tailWord_123784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123833 : List Nat := [1, 2, 1, 4, 2, 2, 2, 6]
def baseStart_123833 : Nat := 118140960795 + 123833 * 2 ^ 59
def prefixEnd_123833 : Nat := 4983230072969 + 3 ^ 40 * 123833 * 2
def baseEnd_123833 : Nat := 18840251818761255264595

theorem tailTrace_123833 : CollatzResearch.WordTrace tailWord_123833 prefixEnd_123833 18840251818761255264595 := by
  unfold tailWord_123833
  simp only [CollatzResearch.WordTrace]
  refine ⟨4516560560381664837752153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3011040373587776558501435 4516560560381664837752153)
  ·
    refine ⟨3387420420286248628314115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4516560560381664837752153 3387420420286248628314115)
    ·
      refine ⟨5081130630429372942471173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3387420420286248628314115 5081130630429372942471173)
      ·
        refine ⟨952711993205507426713345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5081130630429372942471173 952711993205507426713345)
        ·
          refine ⟨714533994904130570035009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 952711993205507426713345 714533994904130570035009)
          ·
            refine ⟨535900496178097927526257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 714533994904130570035009 535900496178097927526257)
            ·
              refine ⟨401925372133573445644693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 535900496178097927526257 401925372133573445644693)
              ·
                refine ⟨18840251818761255264595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 401925372133573445644693 18840251818761255264595)
                ·
                  rfl

theorem cell20_123833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 6].length) (baseStart_123833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123833 prefixEnd_123833 := by exact prefixLift 123833
  have htrace : WordTrace (prefixWord ++ tailWord_123833) baseStart_123833 baseEnd_123833 := by
    simpa [prefixWord, tailWord_123833, baseEnd_123833] using wordTrace_append hprefix tailTrace_123833
  have hstable : (prefixWord ++ tailWord_123833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123833).length < 2 ^ (prefixWord ++ tailWord_123833).sum := by decide
  have hdescent : baseEnd_123833 < baseStart_123833 := by decide
  rcases family_descends (prefixWord ++ tailWord_123833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123846 : List Nat := [6, 1, 3, 1, 9]
def baseStart_123846 : Nat := 118140960795 + 123846 * 2 ^ 59
def prefixEnd_123846 : Nat := 4983230072969 + 3 ^ 40 * 123846 * 2
def baseEnd_123846 : Nat := 697860358154487634079

theorem tailTrace_123846 : CollatzResearch.WordTrace tailWord_123846 prefixEnd_123846 697860358154487634079 := by
  unfold tailWord_123846
  simp only [CollatzResearch.WordTrace]
  refine ⟨141157334666705251811731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3011356472889712038650261 141157334666705251811731)
  ·
    refine ⟨211736002000057877717597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141157334666705251811731 211736002000057877717597)
    ·
      refine ⟨79401000750021704144099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211736002000057877717597 79401000750021704144099)
      ·
        refine ⟨119101501125032556216149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79401000750021704144099 119101501125032556216149)
        ·
          refine ⟨697860358154487634079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 119101501125032556216149 697860358154487634079)
          ·
            rfl

theorem cell20_123846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 9].length) (baseStart_123846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123846 prefixEnd_123846 := by exact prefixLift 123846
  have htrace : WordTrace (prefixWord ++ tailWord_123846) baseStart_123846 baseEnd_123846 := by
    simpa [prefixWord, tailWord_123846, baseEnd_123846] using wordTrace_append hprefix tailTrace_123846
  have hstable : (prefixWord ++ tailWord_123846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123846).length < 2 ^ (prefixWord ++ tailWord_123846).sum := by decide
  have hdescent : baseEnd_123846 < baseStart_123846 := by decide
  rcases family_descends (prefixWord ++ tailWord_123846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123857 : List Nat := [1, 2, 2, 1, 2, 1, 6, 2, 3]
def baseStart_123857 : Nat := 118140960795 + 123857 * 2 ^ 59
def prefixEnd_123857 : Nat := 4983230072969 + 3 ^ 40 * 123857 * 2
def baseEnd_123857 : Nat := 56531709710246348993687

theorem tailTrace_123857 : CollatzResearch.WordTrace tailWord_123857 prefixEnd_123857 56531709710246348993687 := by
  unfold tailWord_123857
  simp only [CollatzResearch.WordTrace]
  refine ⟨4517435912294716936625825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3011623941529811291083883 4517435912294716936625825)
  ·
    refine ⟨3388076934221037702469369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4517435912294716936625825 3388076934221037702469369)
    ·
      refine ⟨2541057700665778276852027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3388076934221037702469369 2541057700665778276852027)
      ·
        refine ⟨3811586550998667415278041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2541057700665778276852027 3811586550998667415278041)
        ·
          refine ⟨2858689913249000561458531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3811586550998667415278041 2858689913249000561458531)
          ·
            refine ⟨4288034869873500842187797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2858689913249000561458531 4288034869873500842187797)
            ·
              refine ⟨201001634525320351977553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4288034869873500842187797 201001634525320351977553)
              ·
                refine ⟨150751225893990263983165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201001634525320351977553 150751225893990263983165)
                ·
                  refine ⟨56531709710246348993687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150751225893990263983165 56531709710246348993687)
                  ·
                    rfl

theorem cell20_123857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 3].length) (baseStart_123857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123857 prefixEnd_123857 := by exact prefixLift 123857
  have htrace : WordTrace (prefixWord ++ tailWord_123857) baseStart_123857 baseEnd_123857 := by
    simpa [prefixWord, tailWord_123857, baseEnd_123857] using wordTrace_append hprefix tailTrace_123857
  have hstable : (prefixWord ++ tailWord_123857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123857).length < 2 ^ (prefixWord ++ tailWord_123857).sum := by decide
  have hdescent : baseEnd_123857 < baseStart_123857 := by decide
  rcases family_descends (prefixWord ++ tailWord_123857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123860 : List Nat := [2, 4, 1, 2, 1, 3, 1, 4, 2]
def baseStart_123860 : Nat := 118140960795 + 123860 * 2 ^ 59
def prefixEnd_123860 : Nat := 4983230072969 + 3 ^ 40 * 123860 * 2
def baseEnd_123860 : Nat := 56533078991991671893675

theorem tailTrace_123860 : CollatzResearch.WordTrace tailWord_123860 prefixEnd_123860 56533078991991671893675 := by
  unfold tailWord_123860
  simp only [CollatzResearch.WordTrace]
  refine ⟨2258772665641924224492517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3011696887522565632656689 2258772665641924224492517)
  ·
    refine ⟨423519874807860792092347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2258772665641924224492517 423519874807860792092347)
    ·
      refine ⟨635279812211791188138521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423519874807860792092347 635279812211791188138521)
      ·
        refine ⟨476459859158843391103891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 635279812211791188138521 476459859158843391103891)
        ·
          refine ⟨714689788738265086655837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476459859158843391103891 714689788738265086655837)
          ·
            refine ⟨268008670776849407495939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 714689788738265086655837 268008670776849407495939)
            ·
              refine ⟨402013006165274111243909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268008670776849407495939 402013006165274111243909)
              ·
                refine ⟨75377438655988895858233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 402013006165274111243909 75377438655988895858233)
                ·
                  refine ⟨56533078991991671893675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75377438655988895858233 56533078991991671893675)
                  ·
                    rfl

theorem cell20_123860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_123860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123860 prefixEnd_123860 := by exact prefixLift 123860
  have htrace : WordTrace (prefixWord ++ tailWord_123860) baseStart_123860 baseEnd_123860 := by
    simpa [prefixWord, tailWord_123860, baseEnd_123860] using wordTrace_append hprefix tailTrace_123860
  have hstable : (prefixWord ++ tailWord_123860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123860).length < 2 ^ (prefixWord ++ tailWord_123860).sum := by decide
  have hdescent : baseEnd_123860 < baseStart_123860 := by decide
  rcases family_descends (prefixWord ++ tailWord_123860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123912 : List Nat := [2, 1, 3, 2, 1, 5, 1, 2, 3]
def baseStart_123912 : Nat := 118140960795 + 123912 * 2 ^ 59
def prefixEnd_123912 : Nat := 4983230072969 + 3 ^ 40 * 123912 * 2
def baseEnd_123912 : Nat := 56556813208910602160129

theorem tailTrace_123912 : CollatzResearch.WordTrace tailWord_123912 prefixEnd_123912 56556813208910602160129 := by
  unfold tailWord_123912
  simp only [CollatzResearch.WordTrace]
  refine ⟨2259720963547730664938995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3012961284730307553251993 2259720963547730664938995)
  ·
    refine ⟨3389581445321595997408493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2259720963547730664938995 3389581445321595997408493)
    ·
      refine ⟨1271093041995598499028185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3389581445321595997408493 1271093041995598499028185)
      ·
        refine ⟨953319781496698874271139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1271093041995598499028185 953319781496698874271139)
        ·
          refine ⟨1429979672245048311406709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 953319781496698874271139 1429979672245048311406709)
          ·
            refine ⟨134060594272973279194379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1429979672245048311406709 134060594272973279194379)
            ·
              refine ⟨201090891409459918791569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134060594272973279194379 201090891409459918791569)
              ·
                refine ⟨150818168557094939093677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201090891409459918791569 150818168557094939093677)
                ·
                  refine ⟨56556813208910602160129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150818168557094939093677 56556813208910602160129)
                  ·
                    rfl

theorem cell20_123912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 3].length) (baseStart_123912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123912 prefixEnd_123912 := by exact prefixLift 123912
  have htrace : WordTrace (prefixWord ++ tailWord_123912) baseStart_123912 baseEnd_123912 := by
    simpa [prefixWord, tailWord_123912, baseEnd_123912] using wordTrace_append hprefix tailTrace_123912
  have hstable : (prefixWord ++ tailWord_123912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123912).length < 2 ^ (prefixWord ++ tailWord_123912).sum := by decide
  have hdescent : baseEnd_123912 < baseStart_123912 := by decide
  rcases family_descends (prefixWord ++ tailWord_123912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123943 : List Nat := [1, 1, 7, 1, 1, 1, 4, 4]
def baseStart_123943 : Nat := 118140960795 + 123943 * 2 ^ 59
def prefixEnd_123943 : Nat := 4983230072969 + 3 ^ 40 * 123943 * 2
def baseEnd_123943 : Nat := 18856987484537424042223

theorem tailTrace_123943 : CollatzResearch.WordTrace tailWord_123943 prefixEnd_123943 18856987484537424042223 := by
  unfold tailWord_123943
  simp only [CollatzResearch.WordTrace]
  refine ⟨4520572589983153624256483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3013715059988769082837655 4520572589983153624256483)
  ·
    refine ⟨6780858884974730436384725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4520572589983153624256483 6780858884974730436384725)
    ·
      refine ⟨158926380116595244602767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 6780858884974730436384725 158926380116595244602767)
      ·
        refine ⟨238389570174892866904151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158926380116595244602767 238389570174892866904151)
        ·
          refine ⟨357584355262339300356227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238389570174892866904151 357584355262339300356227)
          ·
            refine ⟨536376532893508950534341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357584355262339300356227 536376532893508950534341)
            ·
              refine ⟨100570599917532928225189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 536376532893508950534341 100570599917532928225189)
              ·
                refine ⟨18856987484537424042223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100570599917532928225189 18856987484537424042223)
                ·
                  rfl

theorem cell20_123943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 4].length) (baseStart_123943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123943 prefixEnd_123943 := by exact prefixLift 123943
  have htrace : WordTrace (prefixWord ++ tailWord_123943) baseStart_123943 baseEnd_123943 := by
    simpa [prefixWord, tailWord_123943, baseEnd_123943] using wordTrace_append hprefix tailTrace_123943
  have hstable : (prefixWord ++ tailWord_123943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123943).length < 2 ^ (prefixWord ++ tailWord_123943).sum := by decide
  have hdescent : baseEnd_123943 < baseStart_123943 := by decide
  rcases family_descends (prefixWord ++ tailWord_123943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123954 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 7]
def baseStart_123954 : Nat := 118140960795 + 123954 * 2 ^ 59
def prefixEnd_123954 : Nat := 4983230072969 + 3 ^ 40 * 123954 * 2
def baseEnd_123954 : Nat := 56575983153345122759957

theorem tailTrace_123954 : CollatzResearch.WordTrace tailWord_123954 prefixEnd_123954 56575983153345122759957 := by
  unfold tailWord_123954
  simp only [CollatzResearch.WordTrace]
  refine ⟨1130243448235825625726729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3013982528628868335271277 1130243448235825625726729)
  ·
    refine ⟨847682586176869219295047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1130243448235825625726729 847682586176869219295047)
    ·
      refine ⟨1271523879265303828942571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 847682586176869219295047 1271523879265303828942571)
      ·
        refine ⟨1907285818897955743413857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1271523879265303828942571 1907285818897955743413857)
        ·
          refine ⟨1430464364173466807560393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1907285818897955743413857 1430464364173466807560393)
          ·
            refine ⟨1072848273130100105670295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1430464364173466807560393 1072848273130100105670295)
            ·
              refine ⟨1609272409695150158505443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1072848273130100105670295 1609272409695150158505443)
              ·
                refine ⟨2413908614542725237758165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1609272409695150158505443 2413908614542725237758165)
                ·
                  refine ⟨56575983153345122759957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2413908614542725237758165 56575983153345122759957)
                  ·
                    rfl

theorem cell20_123954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_123954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123954 prefixEnd_123954 := by exact prefixLift 123954
  have htrace : WordTrace (prefixWord ++ tailWord_123954) baseStart_123954 baseEnd_123954 := by
    simpa [prefixWord, tailWord_123954, baseEnd_123954] using wordTrace_append hprefix tailTrace_123954
  have hstable : (prefixWord ++ tailWord_123954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123954).length < 2 ^ (prefixWord ++ tailWord_123954).sum := by decide
  have hdescent : baseEnd_123954 < baseStart_123954 := by decide
  rcases family_descends (prefixWord ++ tailWord_123954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123974 : List Nat := [6, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_123974 : Nat := 118140960795 + 123974 * 2 ^ 59
def prefixEnd_123974 : Nat := 4983230072969 + 3 ^ 40 * 123974 * 2
def baseEnd_123974 : Nat := 56585111698313942093209

theorem tailTrace_123974 : CollatzResearch.WordTrace tailWord_123974 prefixEnd_123974 56585111698313942093209 := by
  unfold tailWord_123974
  simp only [CollatzResearch.WordTrace]
  refine ⟨141303226652213934957343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3014468835247230612423317 141303226652213934957343)
  ·
    refine ⟨211954839978320902436015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141303226652213934957343 211954839978320902436015)
    ·
      refine ⟨317932259967481353654023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211954839978320902436015 317932259967481353654023)
      ·
        refine ⟨476898389951222030481035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317932259967481353654023 476898389951222030481035)
        ·
          refine ⟨715347584926833045721553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476898389951222030481035 715347584926833045721553)
          ·
            refine ⟨536510688695124784291165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 715347584926833045721553 536510688695124784291165)
            ·
              refine ⟨201191508260671794109187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 536510688695124784291165 201191508260671794109187)
              ·
                refine ⟨301787262391007691163781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201191508260671794109187 301787262391007691163781)
                ·
                  refine ⟨56585111698313942093209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 301787262391007691163781 56585111698313942093209)
                  ·
                    rfl

theorem cell20_123974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_123974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123974 prefixEnd_123974 := by exact prefixLift 123974
  have htrace : WordTrace (prefixWord ++ tailWord_123974) baseStart_123974 baseEnd_123974 := by
    simpa [prefixWord, tailWord_123974, baseEnd_123974] using wordTrace_append hprefix tailTrace_123974
  have hstable : (prefixWord ++ tailWord_123974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123974).length < 2 ^ (prefixWord ++ tailWord_123974).sum := by decide
  have hdescent : baseEnd_123974 < baseStart_123974 := by decide
  rcases family_descends (prefixWord ++ tailWord_123974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123978 : List Nat := [3, 1, 2, 1, 1, 2, 5, 1, 4]
def baseStart_123978 : Nat := 118140960795 + 123978 * 2 ^ 59
def prefixEnd_123978 : Nat := 4983230072969 + 3 ^ 40 * 123978 * 2
def baseEnd_123978 : Nat := 56586937407307705959859

theorem tailTrace_123978 : CollatzResearch.WordTrace tailWord_123978 prefixEnd_123978 56586937407307705959859 := by
  unfold tailWord_123978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1130462286214088650445147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3014566096570903067853725 1130462286214088650445147)
  ·
    refine ⟨1695693429321132975667721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1130462286214088650445147 1695693429321132975667721)
    ·
      refine ⟨1271770071990849731750791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1695693429321132975667721 1271770071990849731750791)
      ·
        refine ⟨1907655107986274597626187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1271770071990849731750791 1907655107986274597626187)
        ·
          refine ⟨2861482661979411896439281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1907655107986274597626187 2861482661979411896439281)
          ·
            refine ⟨2146111996484558922329461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2861482661979411896439281 2146111996484558922329461)
            ·
              refine ⟨201197999670427398968387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2146111996484558922329461 201197999670427398968387)
              ·
                refine ⟨301796999505641098452581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201197999670427398968387 301796999505641098452581)
                ·
                  refine ⟨56586937407307705959859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 301796999505641098452581 56586937407307705959859)
                  ·
                    rfl

theorem cell20_123978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_123978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123978 prefixEnd_123978 := by exact prefixLift 123978
  have htrace : WordTrace (prefixWord ++ tailWord_123978) baseStart_123978 baseEnd_123978 := by
    simpa [prefixWord, tailWord_123978, baseEnd_123978] using wordTrace_append hprefix tailTrace_123978
  have hstable : (prefixWord ++ tailWord_123978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123978).length < 2 ^ (prefixWord ++ tailWord_123978).sum := by decide
  have hdescent : baseEnd_123978 < baseStart_123978 := by decide
  rcases family_descends (prefixWord ++ tailWord_123978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123988 : List Nat := [2, 4, 1, 1, 1, 1, 6, 1, 3]
def baseStart_123988 : Nat := 118140960795 + 123988 * 2 ^ 59
def prefixEnd_123988 : Nat := 4983230072969 + 3 ^ 40 * 123988 * 2
def baseEnd_123988 : Nat := 56591501679792115626485

theorem tailTrace_123988 : CollatzResearch.WordTrace tailWord_123988 prefixEnd_123988 56591501679792115626485 := by
  unfold tailWord_123988
  simp only [CollatzResearch.WordTrace]
  refine ⟨2261106937410063154822309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3014809249880084206429745 2261106937410063154822309)
  ·
    refine ⟨423957550764386841529183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2261106937410063154822309 423957550764386841529183)
    ·
      refine ⟨635936326146580262293775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423957550764386841529183 635936326146580262293775)
      ·
        refine ⟨953904489219870393440663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635936326146580262293775 953904489219870393440663)
        ·
          refine ⟨1430856733829805590160995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 953904489219870393440663 1430856733829805590160995)
          ·
            refine ⟨2146285100744708385241493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1430856733829805590160995 2146285100744708385241493)
            ·
              refine ⟨100607114097408205558195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2146285100744708385241493 100607114097408205558195)
              ·
                refine ⟨150910671146112308337293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100607114097408205558195 150910671146112308337293)
                ·
                  refine ⟨56591501679792115626485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150910671146112308337293 56591501679792115626485)
                  ·
                    rfl

theorem cell20_123988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_123988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123988 prefixEnd_123988 := by exact prefixLift 123988
  have htrace : WordTrace (prefixWord ++ tailWord_123988) baseStart_123988 baseEnd_123988 := by
    simpa [prefixWord, tailWord_123988, baseEnd_123988] using wordTrace_append hprefix tailTrace_123988
  have hstable : (prefixWord ++ tailWord_123988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123988).length < 2 ^ (prefixWord ++ tailWord_123988).sum := by decide
  have hdescent : baseEnd_123988 < baseStart_123988 := by decide
  rcases family_descends (prefixWord ++ tailWord_123988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123999 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 6]
def baseStart_123999 : Nat := 118140960795 + 123999 * 2 ^ 59
def prefixEnd_123999 : Nat := 4983230072969 + 3 ^ 40 * 123999 * 2
def baseEnd_123999 : Nat := 56596522379524966259773

theorem tailTrace_123999 : CollatzResearch.WordTrace tailWord_123999 prefixEnd_123999 56596522379524966259773 := by
  unfold tailWord_123999
  simp only [CollatzResearch.WordTrace]
  refine ⟨4522615077780275188295051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3015076718520183458863367 4522615077780275188295051)
  ·
    refine ⟨6783922616670412782442577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4522615077780275188295051 6783922616670412782442577)
    ·
      refine ⟨5087941962502809586831933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6783922616670412782442577 5087941962502809586831933)
      ·
        refine ⟨1907978235938553595061975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5087941962502809586831933 1907978235938553595061975)
        ·
          refine ⟨2861967353907830392592963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1907978235938553595061975 2861967353907830392592963)
          ·
            refine ⟨4292951030861745588889445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2861967353907830392592963 4292951030861745588889445)
            ·
              refine ⟨804928318286577297916771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4292951030861745588889445 804928318286577297916771)
              ·
                refine ⟨1207392477429865946875157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 804928318286577297916771 1207392477429865946875157)
                ·
                  refine ⟨56596522379524966259773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1207392477429865946875157 56596522379524966259773)
                  ·
                    rfl

theorem cell20_123999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 6].length) (baseStart_123999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_123999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_123999 prefixEnd_123999 := by exact prefixLift 123999
  have htrace : WordTrace (prefixWord ++ tailWord_123999) baseStart_123999 baseEnd_123999 := by
    simpa [prefixWord, tailWord_123999, baseEnd_123999] using wordTrace_append hprefix tailTrace_123999
  have hstable : (prefixWord ++ tailWord_123999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123999).length < 2 ^ (prefixWord ++ tailWord_123999).sum := by decide
  have hdescent : baseEnd_123999 < baseStart_123999 := by decide
  rcases family_descends (prefixWord ++ tailWord_123999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124002 : List Nat := [3, 3, 2, 2, 1, 1, 2, 6]
def baseStart_124002 : Nat := 118140960795 + 124002 * 2 ^ 59
def prefixEnd_124002 : Nat := 4983230072969 + 3 ^ 40 * 124002 * 2
def baseEnd_124002 : Nat := 18865963887090096386587

theorem tailTrace_124002 : CollatzResearch.WordTrace tailWord_124002 prefixEnd_124002 18865963887090096386587 := by
  unfold tailWord_124002
  simp only [CollatzResearch.WordTrace]
  refine ⟨1130681124192351675163565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3015149664512937800436173 1130681124192351675163565)
  ·
    refine ⟨424005421572131878186337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1130681124192351675163565 424005421572131878186337)
    ·
      refine ⟨318004066179098908639753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424005421572131878186337 318004066179098908639753)
      ·
        refine ⟨238503049634324181479815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318004066179098908639753 238503049634324181479815)
        ·
          refine ⟨357754574451486272219723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238503049634324181479815 357754574451486272219723)
          ·
            refine ⟨536631861677229408329585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357754574451486272219723 536631861677229408329585)
            ·
              refine ⟨402473896257922056247189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 536631861677229408329585 402473896257922056247189)
              ·
                refine ⟨18865963887090096386587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 402473896257922056247189 18865963887090096386587)
                ·
                  rfl

theorem cell20_124002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_124002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124002 prefixEnd_124002 := by exact prefixLift 124002
  have htrace : WordTrace (prefixWord ++ tailWord_124002) baseStart_124002 baseEnd_124002 := by
    simpa [prefixWord, tailWord_124002, baseEnd_124002] using wordTrace_append hprefix tailTrace_124002
  have hstable : (prefixWord ++ tailWord_124002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124002).length < 2 ^ (prefixWord ++ tailWord_124002).sum := by decide
  have hdescent : baseEnd_124002 < baseStart_124002 := by decide
  rcases family_descends (prefixWord ++ tailWord_124002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124092 : List Nat := [2, 2, 2, 3, 2, 1, 1, 3, 4]
def baseStart_124092 : Nat := 118140960795 + 124092 * 2 ^ 59
def prefixEnd_124092 : Nat := 4983230072969 + 3 ^ 40 * 124092 * 2
def baseEnd_124092 : Nat := 56638970113629976159393

theorem tailTrace_124092 : CollatzResearch.WordTrace tailWord_124092 prefixEnd_124092 56638970113629976159393 := by
  unfold tailWord_124092
  simp only [CollatzResearch.WordTrace]
  refine ⟨2263003533221676035715265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3017338044295568047620353 2263003533221676035715265)
  ·
    refine ⟨1697252649916257026786449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2263003533221676035715265 1697252649916257026786449)
    ·
      refine ⟨1272939487437192770089837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1697252649916257026786449 1272939487437192770089837)
      ·
        refine ⟨477352307788947288783689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1272939487437192770089837 477352307788947288783689)
        ·
          refine ⟨358014230841710466587767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 477352307788947288783689 358014230841710466587767)
          ·
            refine ⟨537021346262565699881651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358014230841710466587767 537021346262565699881651)
            ·
              refine ⟨805532019393848549822477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537021346262565699881651 805532019393848549822477)
              ·
                refine ⟨302074507272693206183429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 805532019393848549822477 302074507272693206183429)
                ·
                  refine ⟨56638970113629976159393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 302074507272693206183429 56638970113629976159393)
                  ·
                    rfl

theorem cell20_124092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_124092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124092 prefixEnd_124092 := by exact prefixLift 124092
  have htrace : WordTrace (prefixWord ++ tailWord_124092) baseStart_124092 baseEnd_124092 := by
    simpa [prefixWord, tailWord_124092, baseEnd_124092] using wordTrace_append hprefix tailTrace_124092
  have hstable : (prefixWord ++ tailWord_124092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124092).length < 2 ^ (prefixWord ++ tailWord_124092).sum := by decide
  have hdescent : baseEnd_124092 < baseStart_124092 := by decide
  rcases family_descends (prefixWord ++ tailWord_124092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124161 : List Nat := [1, 2, 4, 1, 1, 4, 1, 3, 3]
def baseStart_124161 : Nat := 118140960795 + 124161 * 2 ^ 59
def prefixEnd_124161 : Nat := 4983230072969 + 3 ^ 40 * 124161 * 2
def baseEnd_124161 : Nat := 56670463593772402859111

theorem tailTrace_124161 : CollatzResearch.WordTrace tailWord_124161 prefixEnd_124161 56670463593772402859111 := by
  unfold tailWord_124161
  simp only [CollatzResearch.WordTrace]
  refine ⟨4528523703193376855692337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3019015802128917903794891 4528523703193376855692337)
  ·
    refine ⟨3396392777395032641769253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4528523703193376855692337 3396392777395032641769253)
    ·
      refine ⟨636823645761568620331735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3396392777395032641769253 636823645761568620331735)
      ·
        refine ⟨955235468642352930497603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636823645761568620331735 955235468642352930497603)
        ·
          refine ⟨1432853202963529395746405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 955235468642352930497603 1432853202963529395746405)
          ·
            refine ⟨268659975555661761702451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1432853202963529395746405 268659975555661761702451)
            ·
              refine ⟨402989963333492642553677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268659975555661761702451 402989963333492642553677)
              ·
                refine ⟨151121236250059740957629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 402989963333492642553677 151121236250059740957629)
                ·
                  refine ⟨56670463593772402859111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151121236250059740957629 56670463593772402859111)
                  ·
                    rfl

theorem cell20_124161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 3].length) (baseStart_124161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124161 prefixEnd_124161 := by exact prefixLift 124161
  have htrace : WordTrace (prefixWord ++ tailWord_124161) baseStart_124161 baseEnd_124161 := by
    simpa [prefixWord, tailWord_124161, baseEnd_124161] using wordTrace_append hprefix tailTrace_124161
  have hstable : (prefixWord ++ tailWord_124161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124161).length < 2 ^ (prefixWord ++ tailWord_124161).sum := by decide
  have hdescent : baseEnd_124161 < baseStart_124161 := by decide
  rcases family_descends (prefixWord ++ tailWord_124161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124202 : List Nat := [3, 1, 4, 2, 1, 2, 1, 4, 2]
def baseStart_124202 : Nat := 118140960795 + 124202 * 2 ^ 59
def prefixEnd_124202 : Nat := 4983230072969 + 3 ^ 40 * 124202 * 2
def baseEnd_124202 : Nat := 56689177110958482492277

theorem tailTrace_124202 : CollatzResearch.WordTrace tailWord_124202 prefixEnd_124202 56689177110958482492277 := by
  unfold tailWord_124202
  simp only [CollatzResearch.WordTrace]
  refine ⟨1132504774011210214483715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3020012730696560571956573 1132504774011210214483715)
  ·
    refine ⟨1698757161016815321725573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1132504774011210214483715 1698757161016815321725573)
    ·
      refine ⟨318516967690652872823545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1698757161016815321725573 318516967690652872823545)
      ·
        refine ⟨238887725767989654617659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318516967690652872823545 238887725767989654617659)
        ·
          refine ⟨358331588651984481926489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238887725767989654617659 358331588651984481926489)
          ·
            refine ⟨268748691488988361444867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358331588651984481926489 268748691488988361444867)
            ·
              refine ⟨403123037233482542167301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268748691488988361444867 403123037233482542167301)
              ·
                refine ⟨75585569481277976656369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 403123037233482542167301 75585569481277976656369)
                ·
                  refine ⟨56689177110958482492277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75585569481277976656369 56689177110958482492277)
                  ·
                    rfl

theorem cell20_124202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 4, 2].length) (baseStart_124202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124202 prefixEnd_124202 := by exact prefixLift 124202
  have htrace : WordTrace (prefixWord ++ tailWord_124202) baseStart_124202 baseEnd_124202 := by
    simpa [prefixWord, tailWord_124202, baseEnd_124202] using wordTrace_append hprefix tailTrace_124202
  have hstable : (prefixWord ++ tailWord_124202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124202).length < 2 ^ (prefixWord ++ tailWord_124202).sum := by decide
  have hdescent : baseEnd_124202 < baseStart_124202 := by decide
  rcases family_descends (prefixWord ++ tailWord_124202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124213 : List Nat := [1, 3, 3, 1, 2, 2, 3, 5]
def baseStart_124213 : Nat := 118140960795 + 124213 * 2 ^ 59
def prefixEnd_124213 : Nat := 4983230072969 + 3 ^ 40 * 124213 * 2
def baseEnd_124213 : Nat := 18898065936897111041855

theorem tailTrace_124213 : CollatzResearch.WordTrace tailWord_124213 prefixEnd_124213 18898065936897111041855 := by
  unfold tailWord_124213
  simp only [CollatzResearch.WordTrace]
  refine ⟨4530420299004989736585293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3020280199336659824390195 4530420299004989736585293)
  ·
    refine ⟨1698907612126871151219485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4530420299004989736585293 1698907612126871151219485)
    ·
      refine ⟨637090354547576681707307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1698907612126871151219485 637090354547576681707307)
      ·
        refine ⟨955635531821365022560961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637090354547576681707307 955635531821365022560961)
        ·
          refine ⟨716726648866023766920721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 955635531821365022560961 716726648866023766920721)
          ·
            refine ⟨537544986649517825190541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 716726648866023766920721 537544986649517825190541)
            ·
              refine ⟨201579369993569184446453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 537544986649517825190541 201579369993569184446453)
              ·
                refine ⟨18898065936897111041855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 201579369993569184446453 18898065936897111041855)
                ·
                  rfl

theorem cell20_124213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 5].length) (baseStart_124213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124213 prefixEnd_124213 := by exact prefixLift 124213
  have htrace : WordTrace (prefixWord ++ tailWord_124213) baseStart_124213 baseEnd_124213 := by
    simpa [prefixWord, tailWord_124213, baseEnd_124213] using wordTrace_append hprefix tailTrace_124213
  have hstable : (prefixWord ++ tailWord_124213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124213).length < 2 ^ (prefixWord ++ tailWord_124213).sum := by decide
  have hdescent : baseEnd_124213 < baseStart_124213 := by decide
  rcases family_descends (prefixWord ++ tailWord_124213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124234 : List Nat := [3, 1, 2, 1, 1, 1, 1, 10]
def baseStart_124234 : Nat := 118140960795 + 124234 * 2 ^ 59
def prefixEnd_124234 : Nat := 4983230072969 + 3 ^ 40 * 124234 * 2
def baseEnd_124234 : Nat := 18901260927636197808493

theorem tailTrace_124234 : CollatzResearch.WordTrace tailWord_124234 prefixEnd_124234 18901260927636197808493 := by
  unfold tailWord_124234
  simp only [CollatzResearch.WordTrace]
  refine ⟨1132796557982227580774939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3020790821285940215399837 1132796557982227580774939)
  ·
    refine ⟨1699194836973341371162409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1132796557982227580774939 1699194836973341371162409)
    ·
      refine ⟨1274396127730006028371807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1699194836973341371162409 1274396127730006028371807)
      ·
        refine ⟨1911594191595009042557711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1274396127730006028371807 1911594191595009042557711)
        ·
          refine ⟨2867391287392513563836567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1911594191595009042557711 2867391287392513563836567)
          ·
            refine ⟨4301086931088770345754851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2867391287392513563836567 4301086931088770345754851)
            ·
              refine ⟨6451630396633155518632277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4301086931088770345754851 6451630396633155518632277)
              ·
                refine ⟨18901260927636197808493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6451630396633155518632277 18901260927636197808493)
                ·
                  rfl

theorem cell20_124234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_124234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124234 prefixEnd_124234 := by exact prefixLift 124234
  have htrace : WordTrace (prefixWord ++ tailWord_124234) baseStart_124234 baseEnd_124234 := by
    simpa [prefixWord, tailWord_124234, baseEnd_124234] using wordTrace_append hprefix tailTrace_124234
  have hstable : (prefixWord ++ tailWord_124234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124234).length < 2 ^ (prefixWord ++ tailWord_124234).sum := by decide
  have hdescent : baseEnd_124234 < baseStart_124234 := by decide
  rcases family_descends (prefixWord ++ tailWord_124234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124246 : List Nat := [5, 2, 3, 1, 2, 1, 1, 2, 3]
def baseStart_124246 : Nat := 118140960795 + 124246 * 2 ^ 59
def prefixEnd_124246 : Nat := 4983230072969 + 3 ^ 40 * 124246 * 2
def baseEnd_124246 : Nat := 56709259909889885025431

theorem tailTrace_124246 : CollatzResearch.WordTrace tailWord_124246 prefixEnd_124246 56709259909889885025431 := by
  unfold tailWord_124246
  simp only [CollatzResearch.WordTrace]
  refine ⟨283226494242839773283537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3021082605256957581691061 283226494242839773283537)
  ·
    refine ⟨212419870682129829962653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283226494242839773283537 212419870682129829962653)
    ·
      refine ⟨79657451505798686235995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212419870682129829962653 79657451505798686235995)
      ·
        refine ⟨119486177258698029353993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79657451505798686235995 119486177258698029353993)
        ·
          refine ⟨89614632944023522015495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119486177258698029353993 89614632944023522015495)
          ·
            refine ⟨134421949416035283023243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89614632944023522015495 134421949416035283023243)
            ·
              refine ⟨201632924124052924534865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134421949416035283023243 201632924124052924534865)
              ·
                refine ⟨151224693093039693401149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201632924124052924534865 151224693093039693401149)
                ·
                  refine ⟨56709259909889885025431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151224693093039693401149 56709259909889885025431)
                  ·
                    rfl

theorem cell20_124246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_124246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124246 prefixEnd_124246 := by exact prefixLift 124246
  have htrace : WordTrace (prefixWord ++ tailWord_124246) baseStart_124246 baseEnd_124246 := by
    simpa [prefixWord, tailWord_124246, baseEnd_124246] using wordTrace_append hprefix tailTrace_124246
  have hstable : (prefixWord ++ tailWord_124246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124246).length < 2 ^ (prefixWord ++ tailWord_124246).sum := by decide
  have hdescent : baseEnd_124246 < baseStart_124246 := by decide
  rcases family_descends (prefixWord ++ tailWord_124246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124272 : List Nat := [2, 1, 1, 1, 4, 2, 2, 7]
def baseStart_124272 : Nat := 118140960795 + 124272 * 2 ^ 59
def prefixEnd_124272 : Nat := 4983230072969 + 3 ^ 40 * 124272 * 2
def baseEnd_124272 : Nat := 18907042339449783386219

theorem tailTrace_124272 : CollatzResearch.WordTrace tailWord_124272 prefixEnd_124272 18907042339449783386219 := by
  unfold tailWord_124272
  simp only [CollatzResearch.WordTrace]
  refine ⟨2266286102895621406491535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3021714803860828541988713 2266286102895621406491535)
  ·
    refine ⟨3399429154343432109737303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2266286102895621406491535 3399429154343432109737303)
    ·
      refine ⟨5099143731515148164605955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3399429154343432109737303 5099143731515148164605955)
      ·
        refine ⟨7648715597272722246908933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5099143731515148164605955 7648715597272722246908933)
        ·
          refine ⟨1434134174488635421295425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7648715597272722246908933 1434134174488635421295425)
          ·
            refine ⟨1075600630866476565971569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1434134174488635421295425 1075600630866476565971569)
            ·
              refine ⟨806700473149857424478677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1075600630866476565971569 806700473149857424478677)
              ·
                refine ⟨18907042339449783386219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 806700473149857424478677 18907042339449783386219)
                ·
                  rfl

theorem cell20_124272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 7].length) (baseStart_124272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124272 prefixEnd_124272 := by exact prefixLift 124272
  have htrace : WordTrace (prefixWord ++ tailWord_124272) baseStart_124272 baseEnd_124272 := by
    simpa [prefixWord, tailWord_124272, baseEnd_124272] using wordTrace_append hprefix tailTrace_124272
  have hstable : (prefixWord ++ tailWord_124272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124272).length < 2 ^ (prefixWord ++ tailWord_124272).sum := by decide
  have hdescent : baseEnd_124272 < baseStart_124272 := by decide
  rcases family_descends (prefixWord ++ tailWord_124272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124296 : List Nat := [2, 1, 3, 3, 1, 2, 1, 2, 5]
def baseStart_124296 : Nat := 118140960795 + 124296 * 2 ^ 59
def prefixEnd_124296 : Nat := 4983230072969 + 3 ^ 40 * 124296 * 2
def baseEnd_124296 : Nat := 56732081272311933358559

theorem tailTrace_124296 : CollatzResearch.WordTrace tailWord_124296 prefixEnd_124296 56732081272311933358559 := by
  unfold tailWord_124296
  simp only [CollatzResearch.WordTrace]
  refine ⟨2266723778852147455928371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3022298371802863274571161 2266723778852147455928371)
  ·
    refine ⟨3400085668278221183892557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2266723778852147455928371 3400085668278221183892557)
    ·
      refine ⟨1275032125604332943959709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3400085668278221183892557 1275032125604332943959709)
      ·
        refine ⟨478137047101624853984891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1275032125604332943959709 478137047101624853984891)
        ·
          refine ⟨717205570652437280977337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478137047101624853984891 717205570652437280977337)
          ·
            refine ⟨537904177989327960733003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 717205570652437280977337 537904177989327960733003)
            ·
              refine ⟨806856266983991941099505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537904177989327960733003 806856266983991941099505)
              ·
                refine ⟨605142200237993955824629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 806856266983991941099505 605142200237993955824629)
                ·
                  refine ⟨56732081272311933358559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 605142200237993955824629 56732081272311933358559)
                  ·
                    rfl

theorem cell20_124296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_124296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124296 prefixEnd_124296 := by exact prefixLift 124296
  have htrace : WordTrace (prefixWord ++ tailWord_124296) baseStart_124296 baseEnd_124296 := by
    simpa [prefixWord, tailWord_124296, baseEnd_124296] using wordTrace_append hprefix tailTrace_124296
  have hstable : (prefixWord ++ tailWord_124296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124296).length < 2 ^ (prefixWord ++ tailWord_124296).sum := by decide
  have hdescent : baseEnd_124296 < baseStart_124296 := by decide
  rcases family_descends (prefixWord ++ tailWord_124296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124316 : List Nat := [2, 2, 3, 4, 1, 2, 1, 1, 4]
def baseStart_124316 : Nat := 118140960795 + 124316 * 2 ^ 59
def prefixEnd_124316 : Nat := 4983230072969 + 3 ^ 40 * 124316 * 2
def baseEnd_124316 : Nat := 56741209817280752691811

theorem tailTrace_124316 : CollatzResearch.WordTrace tailWord_124316 prefixEnd_124316 56741209817280752691811 := by
  unfold tailWord_124316
  simp only [CollatzResearch.WordTrace]
  refine ⟨2267088508815919163792401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3022784678421225551723201 2267088508815919163792401)
  ·
    refine ⟨1700316381611939372844301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2267088508815919163792401 1700316381611939372844301)
    ·
      refine ⟨637618643104477264816613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1700316381611939372844301 637618643104477264816613)
      ·
        refine ⟨119553495582089487153115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 637618643104477264816613 119553495582089487153115)
        ·
          refine ⟨179330243373134230729673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119553495582089487153115 179330243373134230729673)
          ·
            refine ⟨134497682529850673047255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179330243373134230729673 134497682529850673047255)
            ·
              refine ⟨201746523794776009570883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134497682529850673047255 201746523794776009570883)
              ·
                refine ⟨302619785692164014356325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201746523794776009570883 302619785692164014356325)
                ·
                  refine ⟨56741209817280752691811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 302619785692164014356325 56741209817280752691811)
                  ·
                    rfl

theorem cell20_124316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_124316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124316 prefixEnd_124316 := by exact prefixLift 124316
  have htrace : WordTrace (prefixWord ++ tailWord_124316) baseStart_124316 baseEnd_124316 := by
    simpa [prefixWord, tailWord_124316, baseEnd_124316] using wordTrace_append hprefix tailTrace_124316
  have hstable : (prefixWord ++ tailWord_124316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124316).length < 2 ^ (prefixWord ++ tailWord_124316).sum := by decide
  have hdescent : baseEnd_124316 < baseStart_124316 := by decide
  rcases family_descends (prefixWord ++ tailWord_124316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124327 : List Nat := [1, 1, 6, 1, 1, 1, 4, 5]
def baseStart_124327 : Nat := 118140960795 + 124327 * 2 ^ 59
def prefixEnd_124327 : Nat := 4983230072969 + 3 ^ 40 * 124327 * 2
def baseEnd_124327 : Nat := 18915410172337867775033

theorem tailTrace_124327 : CollatzResearch.WordTrace tailWord_124327 prefixEnd_124327 18915410172337867775033 := by
  unfold tailWord_124327
  simp only [CollatzResearch.WordTrace]
  refine ⟨4534578220591987206235235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3023052147061324804156823 4534578220591987206235235)
  ·
    refine ⟨6801867330887980809352853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4534578220591987206235235 6801867330887980809352853)
    ·
      refine ⟨318837531135374100438415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6801867330887980809352853 318837531135374100438415)
      ·
        refine ⟨478256296703061150657623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318837531135374100438415 478256296703061150657623)
        ·
          refine ⟨717384445054591725986435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478256296703061150657623 717384445054591725986435)
          ·
            refine ⟨1076076667581887588979653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717384445054591725986435 1076076667581887588979653)
            ·
              refine ⟨201764375171603922933685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1076076667581887588979653 201764375171603922933685)
              ·
                refine ⟨18915410172337867775033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 201764375171603922933685 18915410172337867775033)
                ·
                  rfl

theorem cell20_124327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 5].length) (baseStart_124327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124327 prefixEnd_124327 := by exact prefixLift 124327
  have htrace : WordTrace (prefixWord ++ tailWord_124327) baseStart_124327 baseEnd_124327 := by
    simpa [prefixWord, tailWord_124327, baseEnd_124327] using wordTrace_append hprefix tailTrace_124327
  have hstable : (prefixWord ++ tailWord_124327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124327).length < 2 ^ (prefixWord ++ tailWord_124327).sum := by decide
  have hdescent : baseEnd_124327 < baseStart_124327 := by decide
  rcases family_descends (prefixWord ++ tailWord_124327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124355 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 7]
def baseStart_124355 : Nat := 118140960795 + 124355 * 2 ^ 59
def prefixEnd_124355 : Nat := 4983230072969 + 3 ^ 40 * 124355 * 2
def baseEnd_124355 : Nat := 56759010479969950391651

theorem tailTrace_124355 : CollatzResearch.WordTrace tailWord_124355 prefixEnd_124355 56759010479969950391651 := by
  unfold tailWord_124355
  simp only [CollatzResearch.WordTrace]
  refine ⟨4535599464490547988254519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3023732976327031992169679 4535599464490547988254519)
  ·
    refine ⟨6803399196735821982381779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4535599464490547988254519 6803399196735821982381779)
    ·
      refine ⟨10205098795103732973572669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6803399196735821982381779 10205098795103732973572669)
      ·
        refine ⟨3826912048163899865089751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10205098795103732973572669 3826912048163899865089751)
        ·
          refine ⟨5740368072245849797634627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3826912048163899865089751 5740368072245849797634627)
          ·
            refine ⟨8610552108368774696451941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5740368072245849797634627 8610552108368774696451941)
            ·
              refine ⟨1614478520319145255584739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8610552108368774696451941 1614478520319145255584739)
              ·
                refine ⟨2421717780478717883377109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1614478520319145255584739 2421717780478717883377109)
                ·
                  refine ⟨56759010479969950391651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2421717780478717883377109 56759010479969950391651)
                  ·
                    rfl

theorem cell20_124355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 7].length) (baseStart_124355 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124355 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124355 prefixEnd_124355 := by exact prefixLift 124355
  have htrace : WordTrace (prefixWord ++ tailWord_124355) baseStart_124355 baseEnd_124355 := by
    simpa [prefixWord, tailWord_124355, baseEnd_124355] using wordTrace_append hprefix tailTrace_124355
  have hstable : (prefixWord ++ tailWord_124355).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124355).length < 2 ^ (prefixWord ++ tailWord_124355).sum := by decide
  have hdescent : baseEnd_124355 < baseStart_124355 := by decide
  rcases family_descends (prefixWord ++ tailWord_124355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124389 : List Nat := [1, 3, 1, 5, 1, 1, 2, 3, 3]
def baseStart_124389 : Nat := 118140960795 + 124389 * 2 ^ 59
def prefixEnd_124389 : Nat := 4983230072969 + 3 ^ 40 * 124389 * 2
def baseEnd_124389 : Nat := 56774529006416943258179

theorem tailTrace_124389 : CollatzResearch.WordTrace tailWord_124389 prefixEnd_124389 56774529006416943258179 := by
  unfold tailWord_124389
  simp only [CollatzResearch.WordTrace]
  refine ⟨4536839546367371794992221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3024559697578247863328147 4536839546367371794992221)
  ·
    refine ⟨1701314829887764423122083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4536839546367371794992221 1701314829887764423122083)
    ·
      refine ⟨2551972244831646634683125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1701314829887764423122083 2551972244831646634683125)
      ·
        refine ⟨239247397952966872001543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2551972244831646634683125 239247397952966872001543)
        ·
          refine ⟨358871096929450308002315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239247397952966872001543 358871096929450308002315)
          ·
            refine ⟨538306645394175462003473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358871096929450308002315 538306645394175462003473)
            ·
              refine ⟨403729984045631596502605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538306645394175462003473 403729984045631596502605)
              ·
                refine ⟨151398744017111848688477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 403729984045631596502605 151398744017111848688477)
                ·
                  refine ⟨56774529006416943258179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151398744017111848688477 56774529006416943258179)
                  ·
                    rfl

theorem cell20_124389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_124389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124389 prefixEnd_124389 := by exact prefixLift 124389
  have htrace : WordTrace (prefixWord ++ tailWord_124389) baseStart_124389 baseEnd_124389 := by
    simpa [prefixWord, tailWord_124389, baseEnd_124389] using wordTrace_append hprefix tailTrace_124389
  have hstable : (prefixWord ++ tailWord_124389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124389).length < 2 ^ (prefixWord ++ tailWord_124389).sum := by decide
  have hdescent : baseEnd_124389 < baseStart_124389 := by decide
  rcases family_descends (prefixWord ++ tailWord_124389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124413 : List Nat := [1, 4, 1, 1, 1, 5, 2, 3, 2]
def baseStart_124413 : Nat := 118140960795 + 124413 * 2 ^ 59
def prefixEnd_124413 : Nat := 4983230072969 + 3 ^ 40 * 124413 * 2
def baseEnd_124413 : Nat := 56785483260379526458081

theorem tailTrace_124413 : CollatzResearch.WordTrace tailWord_124413 prefixEnd_124413 56785483260379526458081 := by
  unfold tailWord_124413
  simp only [CollatzResearch.WordTrace]
  refine ⟨4537714898280423893865893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3025143265520282595910595 4537714898280423893865893)
  ·
    refine ⟨850821543427579480099855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4537714898280423893865893 850821543427579480099855)
    ·
      refine ⟨1276232315141369220149783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 850821543427579480099855 1276232315141369220149783)
      ·
        refine ⟨1914348472712053830224675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1276232315141369220149783 1914348472712053830224675)
        ·
          refine ⟨2871522709068080745337013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1914348472712053830224675 2871522709068080745337013)
          ·
            refine ⟨269205253975132569875345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2871522709068080745337013 269205253975132569875345)
            ·
              refine ⟨201903940481349427406509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269205253975132569875345 201903940481349427406509)
              ·
                refine ⟨75713977680506035277441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201903940481349427406509 75713977680506035277441)
                ·
                  refine ⟨56785483260379526458081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75713977680506035277441 56785483260379526458081)
                  ·
                    rfl

theorem cell20_124413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_124413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124413 prefixEnd_124413 := by exact prefixLift 124413
  have htrace : WordTrace (prefixWord ++ tailWord_124413) baseStart_124413 baseEnd_124413 := by
    simpa [prefixWord, tailWord_124413, baseEnd_124413] using wordTrace_append hprefix tailTrace_124413
  have hstable : (prefixWord ++ tailWord_124413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124413).length < 2 ^ (prefixWord ++ tailWord_124413).sum := by decide
  have hdescent : baseEnd_124413 < baseStart_124413 := by decide
  rcases family_descends (prefixWord ++ tailWord_124413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124503 : List Nat := [1, 1, 3, 2, 2, 3, 4, 1, 3]
def baseStart_124503 : Nat := 118140960795 + 124503 * 2 ^ 59
def prefixEnd_124503 : Nat := 4983230072969 + 3 ^ 40 * 124503 * 2
def baseEnd_124503 : Nat := 56826561712739213457713

theorem tailTrace_124503 : CollatzResearch.WordTrace tailWord_124503 prefixEnd_124503 56826561712739213457713 := by
  unfold tailWord_124503
  simp only [CollatzResearch.WordTrace]
  refine ⟨4540997467954369264642163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3027331645302912843094775 4540997467954369264642163)
  ·
    refine ⟨6811496201931553896963245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4540997467954369264642163 6811496201931553896963245)
    ·
      refine ⟨2554311075724332711361217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6811496201931553896963245 2554311075724332711361217)
      ·
        refine ⟨1915733306793249533520913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2554311075724332711361217 1915733306793249533520913)
        ·
          refine ⟨1436799980094937150140685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1915733306793249533520913 1436799980094937150140685)
          ·
            refine ⟨538799992535601431302757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1436799980094937150140685 538799992535601431302757)
            ·
              refine ⟨101024998600425268369267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 538799992535601431302757 101024998600425268369267)
              ·
                refine ⟨151537497900637902553901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101024998600425268369267 151537497900637902553901)
                ·
                  refine ⟨56826561712739213457713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151537497900637902553901 56826561712739213457713)
                  ·
                    rfl

theorem cell20_124503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 3].length) (baseStart_124503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124503 prefixEnd_124503 := by exact prefixLift 124503
  have htrace : WordTrace (prefixWord ++ tailWord_124503) baseStart_124503 baseEnd_124503 := by
    simpa [prefixWord, tailWord_124503, baseEnd_124503] using wordTrace_append hprefix tailTrace_124503
  have hstable : (prefixWord ++ tailWord_124503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124503).length < 2 ^ (prefixWord ++ tailWord_124503).sum := by decide
  have hdescent : baseEnd_124503 < baseStart_124503 := by decide
  rcases family_descends (prefixWord ++ tailWord_124503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124541 : List Nat := [1, 4, 1, 1, 4, 2, 2, 2, 3]
def baseStart_124541 : Nat := 118140960795 + 124541 * 2 ^ 59
def prefixEnd_124541 : Nat := 4983230072969 + 3 ^ 40 * 124541 * 2
def baseEnd_124541 : Nat := 56843905948179970190891

theorem tailTrace_124541 : CollatzResearch.WordTrace tailWord_124541 prefixEnd_124541 56843905948179970190891 := by
  unfold tailWord_124541
  simp only [CollatzResearch.WordTrace]
  refine ⟨4542383441816701754525477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3028255627877801169683651 4542383441816701754525477)
  ·
    refine ⟨851696895340631578973527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4542383441816701754525477 851696895340631578973527)
    ·
      refine ⟨1277545343010947368460291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 851696895340631578973527 1277545343010947368460291)
      ·
        refine ⟨1916318014516421052690437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1277545343010947368460291 1916318014516421052690437)
        ·
          refine ⟨359309627721828947379457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1916318014516421052690437 359309627721828947379457)
          ·
            refine ⟨269482220791371710534593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359309627721828947379457 269482220791371710534593)
            ·
              refine ⟨202111665593528782900945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269482220791371710534593 202111665593528782900945)
              ·
                refine ⟨151583749195146587175709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202111665593528782900945 151583749195146587175709)
                ·
                  refine ⟨56843905948179970190891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151583749195146587175709 56843905948179970190891)
                  ·
                    rfl

theorem cell20_124541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_124541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124541 prefixEnd_124541 := by exact prefixLift 124541
  have htrace : WordTrace (prefixWord ++ tailWord_124541) baseStart_124541 baseEnd_124541 := by
    simpa [prefixWord, tailWord_124541, baseEnd_124541] using wordTrace_append hprefix tailTrace_124541
  have hstable : (prefixWord ++ tailWord_124541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124541).length < 2 ^ (prefixWord ++ tailWord_124541).sum := by decide
  have hdescent : baseEnd_124541 < baseStart_124541 := by decide
  rcases family_descends (prefixWord ++ tailWord_124541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124572 : List Nat := [2, 2, 3, 2, 3, 1, 3, 4]
def baseStart_124572 : Nat := 118140960795 + 124572 * 2 ^ 59
def prefixEnd_124572 : Nat := 4983230072969 + 3 ^ 40 * 124572 * 2
def baseEnd_124572 : Nat := 18952685064293880052477

theorem tailTrace_124572 : CollatzResearch.WordTrace tailWord_124572 prefixEnd_124572 18952685064293880052477 := by
  unfold tailWord_124572
  simp only [CollatzResearch.WordTrace]
  refine ⟨2271757052352197024451985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3029009403136262699269313 2271757052352197024451985)
  ·
    refine ⟨1703817789264147768338989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2271757052352197024451985 1703817789264147768338989)
    ·
      refine ⟨638931670974055413127121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1703817789264147768338989 638931670974055413127121)
      ·
        refine ⟨479198753230541559845341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 638931670974055413127121 479198753230541559845341)
        ·
          refine ⟨179699532461453084942003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 479198753230541559845341 179699532461453084942003)
          ·
            refine ⟨269549298692179627413005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179699532461453084942003 269549298692179627413005)
            ·
              refine ⟨101080987009567360279877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269549298692179627413005 101080987009567360279877)
              ·
                refine ⟨18952685064293880052477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101080987009567360279877 18952685064293880052477)
                ·
                  rfl

theorem cell20_124572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 4].length) (baseStart_124572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124572 prefixEnd_124572 := by exact prefixLift 124572
  have htrace : WordTrace (prefixWord ++ tailWord_124572) baseStart_124572 baseEnd_124572 := by
    simpa [prefixWord, tailWord_124572, baseEnd_124572] using wordTrace_append hprefix tailTrace_124572
  have hstable : (prefixWord ++ tailWord_124572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124572).length < 2 ^ (prefixWord ++ tailWord_124572).sum := by decide
  have hdescent : baseEnd_124572 < baseStart_124572 := by decide
  rcases family_descends (prefixWord ++ tailWord_124572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124607 : List Nat := [1, 1, 2, 2, 2, 3, 4, 1, 4]
def baseStart_124607 : Nat := 118140960795 + 124607 * 2 ^ 59
def prefixEnd_124607 : Nat := 4983230072969 + 3 ^ 40 * 124607 * 2
def baseEnd_124607 : Nat := 56874030146577073990621

theorem tailTrace_124607 : CollatzResearch.WordTrace tailWord_124607 prefixEnd_124607 56874030146577073990621 := by
  unfold tailWord_124607
  simp only [CollatzResearch.WordTrace]
  refine ⟨4544790659577595026428075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3029860439718396684285383 4544790659577595026428075)
  ·
    refine ⟨6817185989366392539642113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4544790659577595026428075 6817185989366392539642113)
    ·
      refine ⟨5112889492024794404731585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6817185989366392539642113 5112889492024794404731585)
      ·
        refine ⟨3834667119018595803548689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5112889492024794404731585 3834667119018595803548689)
        ·
          refine ⟨2876000339263946852661517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3834667119018595803548689 2876000339263946852661517)
          ·
            refine ⟨1078500127223980069748069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2876000339263946852661517 1078500127223980069748069)
            ·
              refine ⟨202218773854496263077763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1078500127223980069748069 202218773854496263077763)
              ·
                refine ⟨303328160781744394616645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202218773854496263077763 303328160781744394616645)
                ·
                  refine ⟨56874030146577073990621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 303328160781744394616645 56874030146577073990621)
                  ·
                    rfl

theorem cell20_124607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 4].length) (baseStart_124607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124607 prefixEnd_124607 := by exact prefixLift 124607
  have htrace : WordTrace (prefixWord ++ tailWord_124607) baseStart_124607 baseEnd_124607 := by
    simpa [prefixWord, tailWord_124607, baseEnd_124607] using wordTrace_append hprefix tailTrace_124607
  have hstable : (prefixWord ++ tailWord_124607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124607).length < 2 ^ (prefixWord ++ tailWord_124607).sum := by decide
  have hdescent : baseEnd_124607 < baseStart_124607 := by decide
  rcases family_descends (prefixWord ++ tailWord_124607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124637 : List Nat := [1, 4, 3, 3, 1, 2, 1, 3, 2]
def baseStart_124637 : Nat := 118140960795 + 124637 * 2 ^ 59
def prefixEnd_124637 : Nat := 4983230072969 + 3 ^ 40 * 124637 * 2
def baseEnd_124637 : Nat := 56887722964030302990499

theorem tailTrace_124637 : CollatzResearch.WordTrace tailWord_124637 prefixEnd_124637 56887722964030302990499 := by
  unfold tailWord_124637
  simp only [CollatzResearch.WordTrace]
  refine ⟨4545884849468910150020165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3030589899645940100013443 4545884849468910150020165)
  ·
    refine ⟨852353409275420653128781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4545884849468910150020165 852353409275420653128781)
    ·
      refine ⟨319632528478282744923293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 852353409275420653128781 319632528478282744923293)
      ·
        refine ⟨119862198179356029346235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319632528478282744923293 119862198179356029346235)
        ·
          refine ⟨179793297269034044019353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119862198179356029346235 179793297269034044019353)
          ·
            refine ⟨134844972951775533014515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179793297269034044019353 134844972951775533014515)
            ·
              refine ⟨202267459427663299521773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134844972951775533014515 202267459427663299521773)
              ·
                refine ⟨75850297285373737320665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202267459427663299521773 75850297285373737320665)
                ·
                  refine ⟨56887722964030302990499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75850297285373737320665 56887722964030302990499)
                  ·
                    rfl

theorem cell20_124637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_124637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124637 prefixEnd_124637 := by exact prefixLift 124637
  have htrace : WordTrace (prefixWord ++ tailWord_124637) baseStart_124637 baseEnd_124637 := by
    simpa [prefixWord, tailWord_124637, baseEnd_124637] using wordTrace_append hprefix tailTrace_124637
  have hstable : (prefixWord ++ tailWord_124637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124637).length < 2 ^ (prefixWord ++ tailWord_124637).sum := by decide
  have hdescent : baseEnd_124637 < baseStart_124637 := by decide
  rcases family_descends (prefixWord ++ tailWord_124637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124659 : List Nat := [1, 1, 1, 2, 2, 3, 4, 1, 5]
def baseStart_124659 : Nat := 118140960795 + 124659 * 2 ^ 59
def prefixEnd_124659 : Nat := 4983230072969 + 3 ^ 40 * 124659 * 2
def baseEnd_124659 : Nat := 56897764363496004257075

theorem tailTrace_124659 : CollatzResearch.WordTrace tailWord_124659 prefixEnd_124659 56897764363496004257075 := by
  unfold tailWord_124659
  simp only [CollatzResearch.WordTrace]
  refine ⟨4546687255389207907321031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3031124836926138604880687 4546687255389207907321031)
  ·
    refine ⟨6820030883083811860981547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4546687255389207907321031 6820030883083811860981547)
    ·
      refine ⟨10230046324625717791472321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6820030883083811860981547 10230046324625717791472321)
      ·
        refine ⟨7672534743469288343604241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10230046324625717791472321 7672534743469288343604241)
        ·
          refine ⟨5754401057601966257703181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7672534743469288343604241 5754401057601966257703181)
          ·
            refine ⟨2157900396600737346638693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5754401057601966257703181 2157900396600737346638693)
            ·
              refine ⟨404606324362638252494755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2157900396600737346638693 404606324362638252494755)
              ·
                refine ⟨606909486543957378742133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 404606324362638252494755 606909486543957378742133)
                ·
                  refine ⟨56897764363496004257075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 606909486543957378742133 56897764363496004257075)
                  ·
                    rfl

theorem cell20_124659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 5].length) (baseStart_124659 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124659 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124659 prefixEnd_124659 := by exact prefixLift 124659
  have htrace : WordTrace (prefixWord ++ tailWord_124659) baseStart_124659 baseEnd_124659 := by
    simpa [prefixWord, tailWord_124659, baseEnd_124659] using wordTrace_append hprefix tailTrace_124659
  have hstable : (prefixWord ++ tailWord_124659).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124659).length < 2 ^ (prefixWord ++ tailWord_124659).sum := by decide
  have hdescent : baseEnd_124659 < baseStart_124659 := by decide
  rcases family_descends (prefixWord ++ tailWord_124659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124662 : List Nat := [5, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_124662 : Nat := 118140960795 + 124662 * 2 ^ 59
def prefixEnd_124662 : Nat := 4983230072969 + 3 ^ 40 * 124662 * 2
def baseEnd_124662 : Nat := 56899133645241327157063

theorem tailTrace_124662 : CollatzResearch.WordTrace tailWord_124662 prefixEnd_124662 56899133645241327157063 := by
  unfold tailWord_124662
  simp only [CollatzResearch.WordTrace]
  refine ⟨284174792148646213730015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3031197782918892946453493 284174792148646213730015)
  ·
    refine ⟨426262188222969320595023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284174792148646213730015 426262188222969320595023)
    ·
      refine ⟨639393282334453980892535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426262188222969320595023 639393282334453980892535)
      ·
        refine ⟨959089923501680971338803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639393282334453980892535 959089923501680971338803)
        ·
          refine ⟨1438634885252521457008205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 959089923501680971338803 1438634885252521457008205)
          ·
            refine ⟨539488081969695546378077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1438634885252521457008205 539488081969695546378077)
            ·
              refine ⟨202308030738635829891779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 539488081969695546378077 202308030738635829891779)
              ·
                refine ⟨303462046107953744837669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202308030738635829891779 303462046107953744837669)
                ·
                  refine ⟨56899133645241327157063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 303462046107953744837669 56899133645241327157063)
                  ·
                    rfl

theorem cell20_124662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_124662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124662 prefixEnd_124662 := by exact prefixLift 124662
  have htrace : WordTrace (prefixWord ++ tailWord_124662) baseStart_124662 baseEnd_124662 := by
    simpa [prefixWord, tailWord_124662, baseEnd_124662] using wordTrace_append hprefix tailTrace_124662
  have hstable : (prefixWord ++ tailWord_124662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124662).length < 2 ^ (prefixWord ++ tailWord_124662).sum := by decide
  have hdescent : baseEnd_124662 < baseStart_124662 := by decide
  rcases family_descends (prefixWord ++ tailWord_124662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124700 : List Nat := [2, 2, 3, 1, 1, 2, 2, 5, 2]
def baseStart_124700 : Nat := 118140960795 + 124700 * 2 ^ 59
def prefixEnd_124700 : Nat := 4983230072969 + 3 ^ 40 * 124700 * 2
def baseEnd_124700 : Nat := 56916477880682083890241

theorem tailTrace_124700 : CollatzResearch.WordTrace tailWord_124700 prefixEnd_124700 56916477880682083890241 := by
  unfold tailWord_124700
  simp only [CollatzResearch.WordTrace]
  refine ⟨2274091324120335954781777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3032121765493781273042369 2274091324120335954781777)
  ·
    refine ⟨1705568493090251966086333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2274091324120335954781777 1705568493090251966086333)
    ·
      refine ⟨639588184908844487282375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1705568493090251966086333 639588184908844487282375)
      ·
        refine ⟨959382277363266730923563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639588184908844487282375 959382277363266730923563)
        ·
          refine ⟨1439073416044900096385345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 959382277363266730923563 1439073416044900096385345)
          ·
            refine ⟨1079305062033675072289009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1439073416044900096385345 1079305062033675072289009)
            ·
              refine ⟨809478796525256304216757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1079305062033675072289009 809478796525256304216757)
              ·
                refine ⟨75888637174242778520321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 809478796525256304216757 75888637174242778520321)
                ·
                  refine ⟨56916477880682083890241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75888637174242778520321 56916477880682083890241)
                  ·
                    rfl

theorem cell20_124700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 5, 2].length) (baseStart_124700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124700 prefixEnd_124700 := by exact prefixLift 124700
  have htrace : WordTrace (prefixWord ++ tailWord_124700) baseStart_124700 baseEnd_124700 := by
    simpa [prefixWord, tailWord_124700, baseEnd_124700] using wordTrace_append hprefix tailTrace_124700
  have hstable : (prefixWord ++ tailWord_124700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124700).length < 2 ^ (prefixWord ++ tailWord_124700).sum := by decide
  have hdescent : baseEnd_124700 < baseStart_124700 := by decide
  rcases family_descends (prefixWord ++ tailWord_124700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124711 : List Nat := [1, 1, 18]
def baseStart_124711 : Nat := 118140960795 + 124711 * 2 ^ 59
def prefixEnd_124711 : Nat := 4983230072969 + 3 ^ 40 * 124711 * 2
def baseEnd_124711 : Nat := 78081616708388113201

theorem tailTrace_124711 : CollatzResearch.WordTrace tailWord_124711 prefixEnd_124711 78081616708388113201 := by
  unfold tailWord_124711
  simp only [CollatzResearch.WordTrace]
  refine ⟨4548583851200820788213987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3032389234133880525475991 4548583851200820788213987)
  ·
    refine ⟨6822875776801231182320981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4548583851200820788213987 6822875776801231182320981)
    ·
      refine ⟨78081616708388113201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 18 6822875776801231182320981 78081616708388113201)
      ·
        rfl

theorem cell20_124711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 18].length) (baseStart_124711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124711 prefixEnd_124711 := by exact prefixLift 124711
  have htrace : WordTrace (prefixWord ++ tailWord_124711) baseStart_124711 baseEnd_124711 := by
    simpa [prefixWord, tailWord_124711, baseEnd_124711] using wordTrace_append hprefix tailTrace_124711
  have hstable : (prefixWord ++ tailWord_124711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124711).length < 2 ^ (prefixWord ++ tailWord_124711).sum := by decide
  have hdescent : baseEnd_124711 < baseStart_124711 := by decide
  rcases family_descends (prefixWord ++ tailWord_124711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124724 : List Nat := [2, 5, 1, 1, 2, 3, 1, 5]
def baseStart_124724 : Nat := 118140960795 + 124724 * 2 ^ 59
def prefixEnd_124724 : Nat := 4983230072969 + 3 ^ 40 * 124724 * 2
def baseEnd_124724 : Nat := 18975810711548222363381

theorem tailTrace_124724 : CollatzResearch.WordTrace tailWord_124724 prefixEnd_124724 18975810711548222363381 := by
  unfold tailWord_124724
  simp only [CollatzResearch.WordTrace]
  refine ⟨2274529000076862004218613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3032705333435816005624817 2274529000076862004218613)
  ·
    refine ⟨213237093757205812895495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2274529000076862004218613 213237093757205812895495)
    ·
      refine ⟨319855640635808719343243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213237093757205812895495 319855640635808719343243)
      ·
        refine ⟨479783460953713079014865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319855640635808719343243 479783460953713079014865)
        ·
          refine ⟨359837595715284809261149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479783460953713079014865 359837595715284809261149)
          ·
            refine ⟨134939098393231803472931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 359837595715284809261149 134939098393231803472931)
            ·
              refine ⟨202408647589847705209397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134939098393231803472931 202408647589847705209397)
              ·
                refine ⟨18975810711548222363381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 202408647589847705209397 18975810711548222363381)
                ·
                  rfl

theorem cell20_124724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 5].length) (baseStart_124724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124724 prefixEnd_124724 := by exact prefixLift 124724
  have htrace : WordTrace (prefixWord ++ tailWord_124724) baseStart_124724 baseEnd_124724 := by
    simpa [prefixWord, tailWord_124724, baseEnd_124724] using wordTrace_append hprefix tailTrace_124724
  have hstable : (prefixWord ++ tailWord_124724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124724).length < 2 ^ (prefixWord ++ tailWord_124724).sum := by decide
  have hdescent : baseEnd_124724 < baseStart_124724 := by decide
  rcases family_descends (prefixWord ++ tailWord_124724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124728 : List Nat := [2, 1, 2, 1, 3, 3, 3, 5]
def baseStart_124728 : Nat := 118140960795 + 124728 * 2 ^ 59
def prefixEnd_124728 : Nat := 4983230072969 + 3 ^ 40 * 124728 * 2
def baseEnd_124728 : Nat := 18976419281212810318931

theorem tailTrace_124728 : CollatzResearch.WordTrace tailWord_124728 prefixEnd_124728 18976419281212810318931 := by
  unfold tailWord_124728
  simp only [CollatzResearch.WordTrace]
  refine ⟨2274601946069616345791419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3032802594759488461055225 2274601946069616345791419)
  ·
    refine ⟨3411902919104424518687129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2274601946069616345791419 3411902919104424518687129)
    ·
      refine ⟨2558927189328318389015347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3411902919104424518687129 2558927189328318389015347)
      ·
        refine ⟨3838390783992477583523021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2558927189328318389015347 3838390783992477583523021)
        ·
          refine ⟨1439396543997179093821133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3838390783992477583523021 1439396543997179093821133)
          ·
            refine ⟨539773703998942160182925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1439396543997179093821133 539773703998942160182925)
            ·
              refine ⟨202415138999603310068597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 539773703998942160182925 202415138999603310068597)
              ·
                refine ⟨18976419281212810318931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 202415138999603310068597 18976419281212810318931)
                ·
                  rfl

theorem cell20_124728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 5].length) (baseStart_124728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124728 prefixEnd_124728 := by exact prefixLift 124728
  have htrace : WordTrace (prefixWord ++ tailWord_124728) baseStart_124728 baseEnd_124728 := by
    simpa [prefixWord, tailWord_124728, baseEnd_124728] using wordTrace_append hprefix tailTrace_124728
  have hstable : (prefixWord ++ tailWord_124728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124728).length < 2 ^ (prefixWord ++ tailWord_124728).sum := by decide
  have hdescent : baseEnd_124728 < baseStart_124728 := by decide
  rcases family_descends (prefixWord ++ tailWord_124728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124776 : List Nat := [2, 1, 4, 2, 1, 1, 1, 6, 2]
def baseStart_124776 : Nat := 118140960795 + 124776 * 2 ^ 59
def prefixEnd_124776 : Nat := 4983230072969 + 3 ^ 40 * 124776 * 2
def baseEnd_124776 : Nat := 56951166351563597356597

theorem tailTrace_124776 : CollatzResearch.WordTrace tailWord_124776 prefixEnd_124776 56951166351563597356597 := by
  unfold tailWord_124776
  simp only [CollatzResearch.WordTrace]
  refine ⟨2275477297982668444665091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3033969730643557926220121 2275477297982668444665091)
  ·
    refine ⟨3413215946974002666997637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2275477297982668444665091 3413215946974002666997637)
    ·
      refine ⟨639977990057625500062057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3413215946974002666997637 639977990057625500062057)
      ·
        refine ⟨479983492543219125046543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 639977990057625500062057 479983492543219125046543)
        ·
          refine ⟨719975238814828687569815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479983492543219125046543 719975238814828687569815)
          ·
            refine ⟨1079962858222243031354723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719975238814828687569815 1079962858222243031354723)
            ·
              refine ⟨1619944287333364547032085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1079962858222243031354723 1619944287333364547032085)
              ·
                refine ⟨75934888468751463142129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1619944287333364547032085 75934888468751463142129)
                ·
                  refine ⟨56951166351563597356597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75934888468751463142129 56951166351563597356597)
                  ·
                    rfl

theorem cell20_124776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 6, 2].length) (baseStart_124776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124776 prefixEnd_124776 := by exact prefixLift 124776
  have htrace : WordTrace (prefixWord ++ tailWord_124776) baseStart_124776 baseEnd_124776 := by
    simpa [prefixWord, tailWord_124776, baseEnd_124776] using wordTrace_append hprefix tailTrace_124776
  have hstable : (prefixWord ++ tailWord_124776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124776).length < 2 ^ (prefixWord ++ tailWord_124776).sum := by decide
  have hdescent : baseEnd_124776 < baseStart_124776 := by decide
  rcases family_descends (prefixWord ++ tailWord_124776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124787 : List Nat := [1, 1, 1, 2, 2, 1, 3, 9]
def baseStart_124787 : Nat := 118140960795 + 124787 * 2 ^ 59
def prefixEnd_124787 : Nat := 4983230072969 + 3 ^ 40 * 124787 * 2
def baseEnd_124787 : Nat := 18985395683765482663295

theorem tailTrace_124787 : CollatzResearch.WordTrace tailWord_124787 prefixEnd_124787 18985395683765482663295 := by
  unfold tailWord_124787
  simp only [CollatzResearch.WordTrace]
  refine ⟨4551355798925485767980615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3034237199283657178653743 4551355798925485767980615)
  ·
    refine ⟨6827033698388228651970923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4551355798925485767980615 6827033698388228651970923)
    ·
      refine ⟨10240550547582342977956385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6827033698388228651970923 10240550547582342977956385)
      ·
        refine ⟨7680412910686757233467289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10240550547582342977956385 7680412910686757233467289)
        ·
          refine ⟨5760309683015067925100467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7680412910686757233467289 5760309683015067925100467)
          ·
            refine ⟨8640464524522601887650701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5760309683015067925100467 8640464524522601887650701)
            ·
              refine ⟨3240174196695975707869013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8640464524522601887650701 3240174196695975707869013)
              ·
                refine ⟨18985395683765482663295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3240174196695975707869013 18985395683765482663295)
                ·
                  rfl

theorem cell20_124787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 9].length) (baseStart_124787 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124787 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124787 prefixEnd_124787 := by exact prefixLift 124787
  have htrace : WordTrace (prefixWord ++ tailWord_124787) baseStart_124787 baseEnd_124787 := by
    simpa [prefixWord, tailWord_124787, baseEnd_124787] using wordTrace_append hprefix tailTrace_124787
  have hstable : (prefixWord ++ tailWord_124787).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124787).length < 2 ^ (prefixWord ++ tailWord_124787).sum := by decide
  have hdescent : baseEnd_124787 < baseStart_124787 := by decide
  rcases family_descends (prefixWord ++ tailWord_124787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124810 : List Nat := [3, 1, 2, 4, 2, 2, 1, 3, 2]
def baseStart_124810 : Nat := 118140960795 + 124810 * 2 ^ 59
def prefixEnd_124810 : Nat := 4983230072969 + 3 ^ 40 * 124810 * 2
def baseEnd_124810 : Nat := 56966684878010590223125

theorem tailTrace_124810 : CollatzResearch.WordTrace tailWord_124810 prefixEnd_124810 56966684878010590223125 := by
  unfold tailWord_124810
  simp only [CollatzResearch.WordTrace]
  refine ⟨1138048669460540174016971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3034796451894773797378589 1138048669460540174016971)
  ·
    refine ⟨1707073004190810261025457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1138048669460540174016971 1707073004190810261025457)
    ·
      refine ⟨1280304753143107695769093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1707073004190810261025457 1280304753143107695769093)
      ·
        refine ⟨240057141214332692956705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1280304753143107695769093 240057141214332692956705)
        ·
          refine ⟨180042855910749519717529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240057141214332692956705 180042855910749519717529)
          ·
            refine ⟨135032141933062139788147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180042855910749519717529 135032141933062139788147)
            ·
              refine ⟨202548212899593209682221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135032141933062139788147 202548212899593209682221)
              ·
                refine ⟨75955579837347453630833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202548212899593209682221 75955579837347453630833)
                ·
                  refine ⟨56966684878010590223125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75955579837347453630833 56966684878010590223125)
                  ·
                    rfl

theorem cell20_124810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 3, 2].length) (baseStart_124810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124810 prefixEnd_124810 := by exact prefixLift 124810
  have htrace : WordTrace (prefixWord ++ tailWord_124810) baseStart_124810 baseEnd_124810 := by
    simpa [prefixWord, tailWord_124810, baseEnd_124810] using wordTrace_append hprefix tailTrace_124810
  have hstable : (prefixWord ++ tailWord_124810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124810).length < 2 ^ (prefixWord ++ tailWord_124810).sum := by decide
  have hdescent : baseEnd_124810 < baseStart_124810 := by decide
  rcases family_descends (prefixWord ++ tailWord_124810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124825 : List Nat := [1, 2, 1, 2, 1, 3, 10]
def baseStart_124825 : Nat := 118140960795 + 124825 * 2 ^ 59
def prefixEnd_124825 : Nat := 4983230072969 + 3 ^ 40 * 124825 * 2
def baseEnd_124825 : Nat := 6330392365193022747007

theorem tailTrace_124825 : CollatzResearch.WordTrace tailWord_124825 prefixEnd_124825 6330392365193022747007 := by
  unfold tailWord_124825
  simp only [CollatzResearch.WordTrace]
  refine ⟨4552741772787818257863929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3035161181858545505242619 4552741772787818257863929)
  ·
    refine ⟨3414556329590863693397947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4552741772787818257863929 3414556329590863693397947)
    ·
      refine ⟨5121834494386295540096921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3414556329590863693397947 5121834494386295540096921)
      ·
        refine ⟨3841375870789721655072691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5121834494386295540096921 3841375870789721655072691)
        ·
          refine ⟨5762063806184582482609037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3841375870789721655072691 5762063806184582482609037)
          ·
            refine ⟨2160773927319218430978389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5762063806184582482609037 2160773927319218430978389)
            ·
              refine ⟨6330392365193022747007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2160773927319218430978389 6330392365193022747007)
              ·
                rfl

theorem cell20_124825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 10].length) (baseStart_124825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124825 prefixEnd_124825 := by exact prefixLift 124825
  have htrace : WordTrace (prefixWord ++ tailWord_124825) baseStart_124825 baseEnd_124825 := by
    simpa [prefixWord, tailWord_124825, baseEnd_124825] using wordTrace_append hprefix tailTrace_124825
  have hstable : (prefixWord ++ tailWord_124825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124825).length < 2 ^ (prefixWord ++ tailWord_124825).sum := by decide
  have hdescent : baseEnd_124825 < baseStart_124825 := by decide
  rcases family_descends (prefixWord ++ tailWord_124825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124828 : List Nat := [2, 2, 3, 3, 1, 1, 2, 1, 5]
def baseStart_124828 : Nat := 118140960795 + 124828 * 2 ^ 59
def prefixEnd_124828 : Nat := 4983230072969 + 3 ^ 40 * 124828 * 2
def baseEnd_124828 : Nat := 56974900568482527623051

theorem tailTrace_124828 : CollatzResearch.WordTrace tailWord_124828 prefixEnd_124828 56974900568482527623051 := by
  unfold tailWord_124828
  simp only [CollatzResearch.WordTrace]
  refine ⟨2276425595888474885111569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3035234127851299846815425 2276425595888474885111569)
  ·
    refine ⟨1707319196916356163833677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2276425595888474885111569 1707319196916356163833677)
    ·
      refine ⟨640244698843633561437629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1707319196916356163833677 640244698843633561437629)
      ·
        refine ⟨240091762066362585539111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 640244698843633561437629 240091762066362585539111)
        ·
          refine ⟨360137643099543878308667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240091762066362585539111 360137643099543878308667)
          ·
            refine ⟨540206464649315817463001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360137643099543878308667 540206464649315817463001)
            ·
              refine ⟨405154848486986863097251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 540206464649315817463001 405154848486986863097251)
              ·
                refine ⟨607732272730480294645877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 405154848486986863097251 607732272730480294645877)
                ·
                  refine ⟨56974900568482527623051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 607732272730480294645877 56974900568482527623051)
                  ·
                    rfl

theorem cell20_124828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_124828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124828 prefixEnd_124828 := by exact prefixLift 124828
  have htrace : WordTrace (prefixWord ++ tailWord_124828) baseStart_124828 baseEnd_124828 := by
    simpa [prefixWord, tailWord_124828, baseEnd_124828] using wordTrace_append hprefix tailTrace_124828
  have hstable : (prefixWord ++ tailWord_124828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124828).length < 2 ^ (prefixWord ++ tailWord_124828).sum := by decide
  have hdescent : baseEnd_124828 < baseStart_124828 := by decide
  rcases family_descends (prefixWord ++ tailWord_124828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124831 : List Nat := [1, 1, 2, 5, 4, 1, 1, 1, 4]
def baseStart_124831 : Nat := 118140960795 + 124831 * 2 ^ 59
def prefixEnd_124831 : Nat := 4983230072969 + 3 ^ 40 * 124831 * 2
def baseEnd_124831 : Nat := 56976269850227850523039

theorem tailTrace_124831 : CollatzResearch.WordTrace tailWord_124831 prefixEnd_124831 56976269850227850523039 := by
  unfold tailWord_124831
  simp only [CollatzResearch.WordTrace]
  refine ⟨4552960610766081282582347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3035307073844054188388231 4552960610766081282582347)
  ·
    refine ⟨6829440916149121923873521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4552960610766081282582347 6829440916149121923873521)
    ·
      refine ⟨5122080687111841442905141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6829440916149121923873521 5122080687111841442905141)
      ·
        refine ⟨480195064416735135272357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5122080687111841442905141 480195064416735135272357)
        ·
          refine ⟨90036574578137837863567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 480195064416735135272357 90036574578137837863567)
          ·
            refine ⟨135054861867206756795351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90036574578137837863567 135054861867206756795351)
            ·
              refine ⟨202582292800810135193027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135054861867206756795351 202582292800810135193027)
              ·
                refine ⟨303873439201215202789541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202582292800810135193027 303873439201215202789541)
                ·
                  refine ⟨56976269850227850523039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 303873439201215202789541 56976269850227850523039)
                  ·
                    rfl

theorem cell20_124831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 4].length) (baseStart_124831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124831 prefixEnd_124831 := by exact prefixLift 124831
  have htrace : WordTrace (prefixWord ++ tailWord_124831) baseStart_124831 baseEnd_124831 := by
    simpa [prefixWord, tailWord_124831, baseEnd_124831] using wordTrace_append hprefix tailTrace_124831
  have hstable : (prefixWord ++ tailWord_124831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124831).length < 2 ^ (prefixWord ++ tailWord_124831).sum := by decide
  have hdescent : baseEnd_124831 < baseStart_124831 := by decide
  rcases family_descends (prefixWord ++ tailWord_124831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124856 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 6]
def baseStart_124856 : Nat := 118140960795 + 124856 * 2 ^ 59
def prefixEnd_124856 : Nat := 4983230072969 + 3 ^ 40 * 124856 * 2
def baseEnd_124856 : Nat := 56987680531438874689603

theorem tailTrace_124856 : CollatzResearch.WordTrace tailWord_124856 prefixEnd_124856 56987680531438874689603 := by
  unfold tailWord_124856
  simp only [CollatzResearch.WordTrace]
  refine ⟨2276936217837755276121211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3035914957117007034828281 2276936217837755276121211)
  ·
    refine ⟨3415404326756632914181817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2276936217837755276121211 3415404326756632914181817)
    ·
      refine ⟨2561553245067474685636363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3415404326756632914181817 2561553245067474685636363)
      ·
        refine ⟨3842329867601212028454545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2561553245067474685636363 3842329867601212028454545)
        ·
          refine ⟨2881747400700909021340909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3842329867601212028454545 2881747400700909021340909)
          ·
            refine ⟨1080655275262840883002841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2881747400700909021340909 1080655275262840883002841)
            ·
              refine ⟨810491456447130662252131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1080655275262840883002841 810491456447130662252131)
              ·
                refine ⟨1215737184670695993378197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 810491456447130662252131 1215737184670695993378197)
                ·
                  refine ⟨56987680531438874689603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1215737184670695993378197 56987680531438874689603)
                  ·
                    rfl

theorem cell20_124856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_124856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124856 prefixEnd_124856 := by exact prefixLift 124856
  have htrace : WordTrace (prefixWord ++ tailWord_124856) baseStart_124856 baseEnd_124856 := by
    simpa [prefixWord, tailWord_124856, baseEnd_124856] using wordTrace_append hprefix tailTrace_124856
  have hstable : (prefixWord ++ tailWord_124856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124856).length < 2 ^ (prefixWord ++ tailWord_124856).sum := by decide
  have hdescent : baseEnd_124856 < baseStart_124856 := by decide
  rcases family_descends (prefixWord ++ tailWord_124856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124863 : List Nat := [1, 1, 2, 2, 2, 1, 3, 8]
def baseStart_124863 : Nat := 118140960795 + 124863 * 2 ^ 59
def prefixEnd_124863 : Nat := 4983230072969 + 3 ^ 40 * 124863 * 2
def baseEnd_124863 : Nat := 18996958507392653818747

theorem tailTrace_124863 : CollatzResearch.WordTrace tailWord_124863 prefixEnd_124863 18996958507392653818747 := by
  unfold tailWord_124863
  simp only [CollatzResearch.WordTrace]
  refine ⟨4554127746650150747747243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3036085164433433831831495 4554127746650150747747243)
  ·
    refine ⟨6831191619975226121620865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4554127746650150747747243 6831191619975226121620865)
    ·
      refine ⟨5123393714981419591215649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6831191619975226121620865 5123393714981419591215649)
      ·
        refine ⟨3842545286236064693411737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5123393714981419591215649 3842545286236064693411737)
        ·
          refine ⟨2881908964677048520058803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3842545286236064693411737 2881908964677048520058803)
          ·
            refine ⟨4322863447015572780088205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2881908964677048520058803 4322863447015572780088205)
            ·
              refine ⟨1621073792630839792533077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4322863447015572780088205 1621073792630839792533077)
              ·
                refine ⟨18996958507392653818747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1621073792630839792533077 18996958507392653818747)
                ·
                  rfl

theorem cell20_124863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 8].length) (baseStart_124863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124863 prefixEnd_124863 := by exact prefixLift 124863
  have htrace : WordTrace (prefixWord ++ tailWord_124863) baseStart_124863 baseEnd_124863 := by
    simpa [prefixWord, tailWord_124863, baseEnd_124863] using wordTrace_append hprefix tailTrace_124863
  have hstable : (prefixWord ++ tailWord_124863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124863).length < 2 ^ (prefixWord ++ tailWord_124863).sum := by decide
  have hdescent : baseEnd_124863 < baseStart_124863 := by decide
  rcases family_descends (prefixWord ++ tailWord_124863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124886 : List Nat := [5, 2, 1, 1, 3, 1, 1, 4, 2]
def baseStart_124886 : Nat := 118140960795 + 124886 * 2 ^ 59
def prefixEnd_124886 : Nat := 4983230072969 + 3 ^ 40 * 124886 * 2
def baseEnd_124886 : Nat := 57001373348892103689481

theorem tailTrace_124886 : CollatzResearch.WordTrace tailWord_124886 prefixEnd_124886 57001373348892103689481 := by
  unfold tailWord_124886
  simp only [CollatzResearch.WordTrace]
  refine ⟨284685414097926604739657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3036644417044550450556341 284685414097926604739657)
  ·
    refine ⟨213514060573444953554743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284685414097926604739657 213514060573444953554743)
    ·
      refine ⟨320271090860167430332115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213514060573444953554743 320271090860167430332115)
      ·
        refine ⟨480406636290251145498173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320271090860167430332115 480406636290251145498173)
        ·
          refine ⟨180152488608844179561815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 480406636290251145498173 180152488608844179561815)
          ·
            refine ⟨270228732913266269342723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180152488608844179561815 270228732913266269342723)
            ·
              refine ⟨405343099369899404014085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270228732913266269342723 405343099369899404014085)
              ·
                refine ⟨76001831131856138252641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 405343099369899404014085 76001831131856138252641)
                ·
                  refine ⟨57001373348892103689481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76001831131856138252641 57001373348892103689481)
                  ·
                    rfl

theorem cell20_124886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_124886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124886 prefixEnd_124886 := by exact prefixLift 124886
  have htrace : WordTrace (prefixWord ++ tailWord_124886) baseStart_124886 baseEnd_124886 := by
    simpa [prefixWord, tailWord_124886, baseEnd_124886] using wordTrace_append hprefix tailTrace_124886
  have hstable : (prefixWord ++ tailWord_124886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124886).length < 2 ^ (prefixWord ++ tailWord_124886).sum := by decide
  have hdescent : baseEnd_124886 < baseStart_124886 := by decide
  rcases family_descends (prefixWord ++ tailWord_124886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124938 : List Nat := [3, 1, 2, 2, 5, 1, 1, 2, 3]
def baseStart_124938 : Nat := 118140960795 + 124938 * 2 ^ 59
def prefixEnd_124938 : Nat := 4983230072969 + 3 ^ 40 * 124938 * 2
def baseEnd_124938 : Nat := 57025107565811033955935

theorem tailTrace_124938 : CollatzResearch.WordTrace tailWord_124938 prefixEnd_124938 57025107565811033955935 := by
  unfold tailWord_124938
  simp only [CollatzResearch.WordTrace]
  refine ⟨1139215805344609639181867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3037908814252292371151645 1139215805344609639181867)
  ·
    refine ⟨1708823708016914458772801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1139215805344609639181867 1708823708016914458772801)
    ·
      refine ⟨1281617781012685844079601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1708823708016914458772801 1281617781012685844079601)
      ·
        refine ⟨961213335759514383059701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1281617781012685844079601 961213335759514383059701)
        ·
          refine ⟨90113750227454473411847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 961213335759514383059701 90113750227454473411847)
          ·
            refine ⟨135170625341181710117771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90113750227454473411847 135170625341181710117771)
            ·
              refine ⟨202755938011772565176657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135170625341181710117771 202755938011772565176657)
              ·
                refine ⟨152066953508829423882493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202755938011772565176657 152066953508829423882493)
                ·
                  refine ⟨57025107565811033955935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152066953508829423882493 57025107565811033955935)
                  ·
                    rfl

theorem cell20_124938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 3].length) (baseStart_124938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124938 prefixEnd_124938 := by exact prefixLift 124938
  have htrace : WordTrace (prefixWord ++ tailWord_124938) baseStart_124938 baseEnd_124938 := by
    simpa [prefixWord, tailWord_124938, baseEnd_124938] using wordTrace_append hprefix tailTrace_124938
  have hstable : (prefixWord ++ tailWord_124938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124938).length < 2 ^ (prefixWord ++ tailWord_124938).sum := by decide
  have hdescent : baseEnd_124938 < baseStart_124938 := by decide
  rcases family_descends (prefixWord ++ tailWord_124938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124939 : List Nat := [1, 1, 1, 1, 6, 1, 9]
def baseStart_124939 : Nat := 118140960795 + 124939 * 2 ^ 59
def prefixEnd_124939 : Nat := 4983230072969 + 3 ^ 40 * 124939 * 2
def baseEnd_124939 : Nat := 6336173777006608324733

theorem tailTrace_124939 : CollatzResearch.WordTrace tailWord_124939 prefixEnd_124939 6336173777006608324733 := by
  unfold tailWord_124939
  simp only [CollatzResearch.WordTrace]
  refine ⟨4556899694374815727513871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3037933129583210485009247 4556899694374815727513871)
  ·
    refine ⟨6835349541562223591270807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4556899694374815727513871 6835349541562223591270807)
    ·
      refine ⟨10253024312343335386906211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6835349541562223591270807 10253024312343335386906211)
      ·
        refine ⟨15379536468515003080359317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10253024312343335386906211 15379536468515003080359317)
        ·
          refine ⟨720915771961640769391843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15379536468515003080359317 720915771961640769391843)
          ·
            refine ⟨1081373657942461154087765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720915771961640769391843 1081373657942461154087765)
            ·
              refine ⟨6336173777006608324733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1081373657942461154087765 6336173777006608324733)
              ·
                rfl

theorem cell20_124939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 9].length) (baseStart_124939 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124939 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124939 prefixEnd_124939 := by exact prefixLift 124939
  have htrace : WordTrace (prefixWord ++ tailWord_124939) baseStart_124939 baseEnd_124939 := by
    simpa [prefixWord, tailWord_124939, baseEnd_124939] using wordTrace_append hprefix tailTrace_124939
  have hstable : (prefixWord ++ tailWord_124939).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124939).length < 2 ^ (prefixWord ++ tailWord_124939).sum := by decide
  have hdescent : baseEnd_124939 < baseStart_124939 := by decide
  rcases family_descends (prefixWord ++ tailWord_124939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124990 : List Nat := [4, 2, 1, 3, 3, 1, 6]
def baseStart_124990 : Nat := 118140960795 + 124990 * 2 ^ 59
def prefixEnd_124990 : Nat := 4983230072969 + 3 ^ 40 * 124990 * 2
def baseEnd_124990 : Nat := 6338760198081107135821

theorem tailTrace_124990 : CollatzResearch.WordTrace tailWord_124990 prefixEnd_124990 6338760198081107135821 := by
  unfold tailWord_124990
  simp only [CollatzResearch.WordTrace]
  refine ⟨569844977148756429702553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3039173211460034291746949 569844977148756429702553)
  ·
    refine ⟨427383732861567322276915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 569844977148756429702553 427383732861567322276915)
    ·
      refine ⟨641075599292350983415373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427383732861567322276915 641075599292350983415373)
      ·
        refine ⟨240403349734631618780765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 641075599292350983415373 240403349734631618780765)
        ·
          refine ⟨90151256150486857042787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240403349734631618780765 90151256150486857042787)
          ·
            refine ⟨135226884225730285564181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90151256150486857042787 135226884225730285564181)
            ·
              refine ⟨6338760198081107135821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 135226884225730285564181 6338760198081107135821)
              ·
                rfl

theorem cell20_124990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 6].length) (baseStart_124990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_124990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_124990 prefixEnd_124990 := by exact prefixLift 124990
  have htrace : WordTrace (prefixWord ++ tailWord_124990) baseStart_124990 baseEnd_124990 := by
    simpa [prefixWord, tailWord_124990, baseEnd_124990] using wordTrace_append hprefix tailTrace_124990
  have hstable : (prefixWord ++ tailWord_124990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124990).length < 2 ^ (prefixWord ++ tailWord_124990).sum := by decide
  have hdescent : baseEnd_124990 < baseStart_124990 := by decide
  rcases family_descends (prefixWord ++ tailWord_124990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125001 : List Nat := [1, 2, 1, 1, 2, 2, 4, 4, 3]
def baseStart_125001 : Nat := 118140960795 + 125001 * 2 ^ 59
def prefixEnd_125001 : Nat := 4983230072969 + 3 ^ 40 * 125001 * 2
def baseEnd_125001 : Nat := 57053862482462814855677

theorem tailTrace_125001 : CollatzResearch.WordTrace tailWord_125001 prefixEnd_125001 57053862482462814855677 := by
  unfold tailWord_125001
  simp only [CollatzResearch.WordTrace]
  refine ⟨4559161020150200316270857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3039440680100133544180571 4559161020150200316270857)
  ·
    refine ⟨3419370765112650237203143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4559161020150200316270857 3419370765112650237203143)
    ·
      refine ⟨5129056147668975355804715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3419370765112650237203143 5129056147668975355804715)
      ·
        refine ⟨7693584221503463033707073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5129056147668975355804715 7693584221503463033707073)
        ·
          refine ⟨5770188166127597275280305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7693584221503463033707073 5770188166127597275280305)
          ·
            refine ⟨4327641124595697956460229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5770188166127597275280305 4327641124595697956460229)
            ·
              refine ⟨811432710861693366836293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4327641124595697956460229 811432710861693366836293)
              ·
                refine ⟨152143633286567506281805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 811432710861693366836293 152143633286567506281805)
                ·
                  refine ⟨57053862482462814855677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152143633286567506281805 57053862482462814855677)
                  ·
                    rfl

theorem cell20_125001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 3].length) (baseStart_125001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125001 prefixEnd_125001 := by exact prefixLift 125001
  have htrace : WordTrace (prefixWord ++ tailWord_125001) baseStart_125001 baseEnd_125001 := by
    simpa [prefixWord, tailWord_125001, baseEnd_125001] using wordTrace_append hprefix tailTrace_125001
  have hstable : (prefixWord ++ tailWord_125001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125001).length < 2 ^ (prefixWord ++ tailWord_125001).sum := by decide
  have hdescent : baseEnd_125001 < baseStart_125001 := by decide
  rcases family_descends (prefixWord ++ tailWord_125001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125014 : List Nat := [5, 2, 2, 1, 1, 2, 1, 3, 3]
def baseStart_125014 : Nat := 118140960795 + 125014 * 2 ^ 59
def prefixEnd_125014 : Nat := 4983230072969 + 3 ^ 40 * 125014 * 2
def baseEnd_125014 : Nat := 57059796036692547422291

theorem tailTrace_125014 : CollatzResearch.WordTrace tailWord_125014 prefixEnd_125014 57059796036692547422291 := by
  unfold tailWord_125014
  simp only [CollatzResearch.WordTrace]
  refine ⟨284977198068943971030881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3039756779402069024329397 284977198068943971030881)
  ·
    refine ⟨213732898551707978273161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284977198068943971030881 213732898551707978273161)
    ·
      refine ⟨160299673913780983704871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213732898551707978273161 160299673913780983704871)
      ·
        refine ⟨240449510870671475557307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160299673913780983704871 240449510870671475557307)
        ·
          refine ⟨360674266306007213335961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240449510870671475557307 360674266306007213335961)
          ·
            refine ⟨270505699729505410001971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360674266306007213335961 270505699729505410001971)
            ·
              refine ⟨405758549594258115002957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270505699729505410001971 405758549594258115002957)
              ·
                refine ⟨152159456097846793126109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 405758549594258115002957 152159456097846793126109)
                ·
                  refine ⟨57059796036692547422291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152159456097846793126109 57059796036692547422291)
                  ·
                    rfl

theorem cell20_125014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_125014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125014 prefixEnd_125014 := by exact prefixLift 125014
  have htrace : WordTrace (prefixWord ++ tailWord_125014) baseStart_125014 baseEnd_125014 := by
    simpa [prefixWord, tailWord_125014, baseEnd_125014] using wordTrace_append hprefix tailTrace_125014
  have hstable : (prefixWord ++ tailWord_125014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125014).length < 2 ^ (prefixWord ++ tailWord_125014).sum := by decide
  have hdescent : baseEnd_125014 < baseStart_125014 := by decide
  rcases family_descends (prefixWord ++ tailWord_125014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125015 : List Nat := [1, 1, 3, 2, 2, 1, 3, 7]
def baseStart_125015 : Nat := 118140960795 + 125015 * 2 ^ 59
def prefixEnd_125015 : Nat := 4983230072969 + 3 ^ 40 * 125015 * 2
def baseEnd_125015 : Nat := 19020084154646996129651

theorem tailTrace_125015 : CollatzResearch.WordTrace tailWord_125015 prefixEnd_125015 19020084154646996129651 := by
  unfold tailWord_125015
  simp only [CollatzResearch.WordTrace]
  refine ⟨4559671642099480707280499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3039781094732987138186999 4559671642099480707280499)
  ·
    refine ⟨6839507463149221060920749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4559671642099480707280499 6839507463149221060920749)
    ·
      refine ⟨2564815298680957897845281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6839507463149221060920749 2564815298680957897845281)
      ·
        refine ⟨1923611474010718423383961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2564815298680957897845281 1923611474010718423383961)
        ·
          refine ⟨1442708605508038817537971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1923611474010718423383961 1442708605508038817537971)
          ·
            refine ⟨2164062908262058226306957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1442708605508038817537971 2164062908262058226306957)
            ·
              refine ⟨811523590598271834865109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2164062908262058226306957 811523590598271834865109)
              ·
                refine ⟨19020084154646996129651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 811523590598271834865109 19020084154646996129651)
                ·
                  rfl

theorem cell20_125015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 7].length) (baseStart_125015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125015 prefixEnd_125015 := by exact prefixLift 125015
  have htrace : WordTrace (prefixWord ++ tailWord_125015) baseStart_125015 baseEnd_125015 := by
    simpa [prefixWord, tailWord_125015, baseEnd_125015] using wordTrace_append hprefix tailTrace_125015
  have hstable : (prefixWord ++ tailWord_125015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125015).length < 2 ^ (prefixWord ++ tailWord_125015).sum := by decide
  have hdescent : baseEnd_125015 < baseStart_125015 := by decide
  rcases family_descends (prefixWord ++ tailWord_125015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125053 : List Nat := [1, 4, 1, 1, 3, 10]
def baseStart_125053 : Nat := 118140960795 + 125053 * 2 ^ 59
def prefixEnd_125053 : Nat := 4983230072969 + 3 ^ 40 * 125053 * 2
def baseEnd_125053 : Nat := 2113985062940064634153

theorem tailTrace_125053 : CollatzResearch.WordTrace tailWord_125053 prefixEnd_125053 2113985062940064634153 := by
  unfold tailWord_125053
  simp only [CollatzResearch.WordTrace]
  refine ⟨4561057615961813197163813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3040705077307875464775875 4561057615961813197163813)
  ·
    refine ⟨855198302992839974468215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4561057615961813197163813 855198302992839974468215)
    ·
      refine ⟨1282797454489259961702323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 855198302992839974468215 1282797454489259961702323)
      ·
        refine ⟨1924196181733889942553485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1282797454489259961702323 1924196181733889942553485)
        ·
          refine ⟨721573568150208728457557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1924196181733889942553485 721573568150208728457557)
          ·
            refine ⟨2113985062940064634153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 721573568150208728457557 2113985062940064634153)
            ·
              rfl

theorem cell20_125053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 10].length) (baseStart_125053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125053 prefixEnd_125053 := by exact prefixLift 125053
  have htrace : WordTrace (prefixWord ++ tailWord_125053) baseStart_125053 baseEnd_125053 := by
    simpa [prefixWord, tailWord_125053, baseEnd_125053] using wordTrace_append hprefix tailTrace_125053
  have hstable : (prefixWord ++ tailWord_125053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125053).length < 2 ^ (prefixWord ++ tailWord_125053).sum := by decide
  have hdescent : baseEnd_125053 < baseStart_125053 := by decide
  rcases family_descends (prefixWord ++ tailWord_125053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125059 : List Nat := [1, 1, 1, 3, 3, 5, 2, 2, 2]
def baseStart_125059 : Nat := 118140960795 + 125059 * 2 ^ 59
def prefixEnd_125059 : Nat := 4983230072969 + 3 ^ 40 * 125059 * 2
def baseEnd_125059 : Nat := 57080335262872390922107

theorem tailTrace_125059 : CollatzResearch.WordTrace tailWord_125059 prefixEnd_125059 57080335262872390922107 := by
  unfold tailWord_125059
  simp only [CollatzResearch.WordTrace]
  refine ⟨4561276453940076221882231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3040850969293384147921487 4561276453940076221882231)
  ·
    refine ⟨6841914680910114332823347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4561276453940076221882231 6841914680910114332823347)
    ·
      refine ⟨10262872021365171499235021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6841914680910114332823347 10262872021365171499235021)
      ·
        refine ⟨3848577008011939312213133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10262872021365171499235021 3848577008011939312213133)
        ·
          refine ⟨1443216378004477242079925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3848577008011939312213133 1443216378004477242079925)
          ·
            refine ⟨135301535437919741444993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1443216378004477242079925 135301535437919741444993)
            ·
              refine ⟨101476151578439806083745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135301535437919741444993 101476151578439806083745)
              ·
                refine ⟨76107113683829854562809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101476151578439806083745 76107113683829854562809)
                ·
                  refine ⟨57080335262872390922107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76107113683829854562809 57080335262872390922107)
                  ·
                    rfl

theorem cell20_125059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 2, 2].length) (baseStart_125059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125059 prefixEnd_125059 := by exact prefixLift 125059
  have htrace : WordTrace (prefixWord ++ tailWord_125059) baseStart_125059 baseEnd_125059 := by
    simpa [prefixWord, tailWord_125059, baseEnd_125059] using wordTrace_append hprefix tailTrace_125059
  have hstable : (prefixWord ++ tailWord_125059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125059).length < 2 ^ (prefixWord ++ tailWord_125059).sum := by decide
  have hdescent : baseEnd_125059 < baseStart_125059 := by decide
  rcases family_descends (prefixWord ++ tailWord_125059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125077 : List Nat := [1, 3, 2, 1, 1, 1, 3, 5, 3]
def baseStart_125077 : Nat := 118140960795 + 125077 * 2 ^ 59
def prefixEnd_125077 : Nat := 4983230072969 + 3 ^ 40 * 125077 * 2
def baseEnd_125077 : Nat := 57088550953344328322033

theorem tailTrace_125077 : CollatzResearch.WordTrace tailWord_125077 prefixEnd_125077 57088550953344328322033 := by
  unfold tailWord_125077
  simp only [CollatzResearch.WordTrace]
  refine ⟨4561932967874865296037485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3041288645249910197358323 4561932967874865296037485)
  ·
    refine ⟨1710724862953074486014057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4561932967874865296037485 1710724862953074486014057)
    ·
      refine ⟨1283043647214805864510543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1710724862953074486014057 1283043647214805864510543)
      ·
        refine ⟨1924565470822208796765815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1283043647214805864510543 1924565470822208796765815)
        ·
          refine ⟨2886848206233313195148723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1924565470822208796765815 2886848206233313195148723)
          ·
            refine ⟨4330272309349969792723085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2886848206233313195148723 4330272309349969792723085)
            ·
              refine ⟨1623852116006238672271157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4330272309349969792723085 1623852116006238672271157)
              ·
                refine ⟨152236135875584875525421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1623852116006238672271157 152236135875584875525421)
                ·
                  refine ⟨57088550953344328322033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152236135875584875525421 57088550953344328322033)
                  ·
                    rfl

theorem cell20_125077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_125077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125077 prefixEnd_125077 := by exact prefixLift 125077
  have htrace : WordTrace (prefixWord ++ tailWord_125077) baseStart_125077 baseEnd_125077 := by
    simpa [prefixWord, tailWord_125077, baseEnd_125077] using wordTrace_append hprefix tailTrace_125077
  have hstable : (prefixWord ++ tailWord_125077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125077).length < 2 ^ (prefixWord ++ tailWord_125077).sum := by decide
  have hdescent : baseEnd_125077 < baseStart_125077 := by decide
  rcases family_descends (prefixWord ++ tailWord_125077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125087 : List Nat := [1, 1, 2, 6, 1, 2, 3, 4]
def baseStart_125087 : Nat := 118140960795 + 125087 * 2 ^ 59
def prefixEnd_125087 : Nat := 4983230072969 + 3 ^ 40 * 125087 * 2
def baseEnd_125087 : Nat := 19031038408609579329553

theorem tailTrace_125087 : CollatzResearch.WordTrace tailWord_125087 prefixEnd_125087 19031038408609579329553 := by
  unfold tailWord_125087
  simp only [CollatzResearch.WordTrace]
  refine ⟨4562297697838637003901515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3041531798559091335934343 4562297697838637003901515)
  ·
    refine ⟨6843446546757955505852273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4562297697838637003901515 6843446546757955505852273)
    ·
      refine ⟨5132584910068466629389205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6843446546757955505852273 5132584910068466629389205)
      ·
        refine ⟨240589917659459373252619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5132584910068466629389205 240589917659459373252619)
        ·
          refine ⟨360884876489189059878929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240589917659459373252619 360884876489189059878929)
          ·
            refine ⟨270663657366891794909197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360884876489189059878929 270663657366891794909197)
            ·
              refine ⟨101498871512584423090949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270663657366891794909197 101498871512584423090949)
              ·
                refine ⟨19031038408609579329553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101498871512584423090949 19031038408609579329553)
                ·
                  rfl

theorem cell20_125087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 4].length) (baseStart_125087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125087 prefixEnd_125087 := by exact prefixLift 125087
  have htrace : WordTrace (prefixWord ++ tailWord_125087) baseStart_125087 baseEnd_125087 := by
    simpa [prefixWord, tailWord_125087, baseEnd_125087] using wordTrace_append hprefix tailTrace_125087
  have hstable : (prefixWord ++ tailWord_125087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125087).length < 2 ^ (prefixWord ++ tailWord_125087).sum := by decide
  have hdescent : baseEnd_125087 < baseStart_125087 := by decide
  rcases family_descends (prefixWord ++ tailWord_125087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125118 : List Nat := [4, 2, 1, 1, 4, 1, 2, 1, 4]
def baseStart_125118 : Nat := 118140960795 + 125118 * 2 ^ 59
def prefixEnd_125118 : Nat := 4983230072969 + 3 ^ 40 * 125118 * 2
def baseEnd_125118 : Nat := 57107264470530407955199

theorem tailTrace_125118 : CollatzResearch.WordTrace tailWord_125118 prefixEnd_125118 57107264470530407955199 := by
  unfold tailWord_125118
  simp only [CollatzResearch.WordTrace]
  refine ⟨570428545090791162285001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3042285573817552865520005 570428545090791162285001)
  ·
    refine ⟨427821408818093371713751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 570428545090791162285001 427821408818093371713751)
    ·
      refine ⟨641732113227140057570627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427821408818093371713751 641732113227140057570627)
      ·
        refine ⟨962598169840710086355941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641732113227140057570627 962598169840710086355941)
        ·
          refine ⟨180487156845133141191739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 962598169840710086355941 180487156845133141191739)
          ·
            refine ⟨270730735267699711787609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180487156845133141191739 270730735267699711787609)
            ·
              refine ⟨203048051450774783840707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270730735267699711787609 203048051450774783840707)
              ·
                refine ⟨304572077176162175761061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203048051450774783840707 304572077176162175761061)
                ·
                  refine ⟨57107264470530407955199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 304572077176162175761061 57107264470530407955199)
                  ·
                    rfl

theorem cell20_125118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_125118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125118 prefixEnd_125118 := by exact prefixLift 125118
  have htrace : WordTrace (prefixWord ++ tailWord_125118) baseStart_125118 baseEnd_125118 := by
    simpa [prefixWord, tailWord_125118, baseEnd_125118] using wordTrace_append hprefix tailTrace_125118
  have hstable : (prefixWord ++ tailWord_125118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125118).length < 2 ^ (prefixWord ++ tailWord_125118).sum := by decide
  have hdescent : baseEnd_125118 < baseStart_125118 := by decide
  rcases family_descends (prefixWord ++ tailWord_125118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125142 : List Nat := [5, 2, 1, 2, 1, 1, 4, 4]
def baseStart_125142 : Nat := 118140960795 + 125142 * 2 ^ 59
def prefixEnd_125142 : Nat := 4983230072969 + 3 ^ 40 * 125142 * 2
def baseEnd_125142 : Nat := 19039406241497663718367

theorem tailTrace_125142 : CollatzResearch.WordTrace tailWord_125142 prefixEnd_125142 19039406241497663718367 := by
  unfold tailWord_125142
  simp only [CollatzResearch.WordTrace]
  refine ⟨285268982039961337322105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3042869141759587598102453 285268982039961337322105)
  ·
    refine ⟨213951736529971002991579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285268982039961337322105 213951736529971002991579)
    ·
      refine ⟨320927604794956504487369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213951736529971002991579 320927604794956504487369)
      ·
        refine ⟨240695703596217378365527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320927604794956504487369 240695703596217378365527)
        ·
          refine ⟨361043555394326067548291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240695703596217378365527 361043555394326067548291)
          ·
            refine ⟨541565333091489101322437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361043555394326067548291 541565333091489101322437)
            ·
              refine ⟨101543499954654206497957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 541565333091489101322437 101543499954654206497957)
              ·
                refine ⟨19039406241497663718367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101543499954654206497957 19039406241497663718367)
                ·
                  rfl

theorem cell20_125142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_125142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125142 prefixEnd_125142 := by exact prefixLift 125142
  have htrace : WordTrace (prefixWord ++ tailWord_125142) baseStart_125142 baseEnd_125142 := by
    simpa [prefixWord, tailWord_125142, baseEnd_125142] using wordTrace_append hprefix tailTrace_125142
  have hstable : (prefixWord ++ tailWord_125142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125142).length < 2 ^ (prefixWord ++ tailWord_125142).sum := by decide
  have hdescent : baseEnd_125142 < baseStart_125142 := by decide
  rcases family_descends (prefixWord ++ tailWord_125142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125146 : List Nat := [3, 1, 1, 2, 2, 1, 6, 4]
def baseStart_125146 : Nat := 118140960795 + 125146 * 2 ^ 59
def prefixEnd_125146 : Nat := 4983230072969 + 3 ^ 40 * 125146 * 2
def baseEnd_125146 : Nat := 19040014811162251673917

theorem tailTrace_125146 : CollatzResearch.WordTrace tailWord_125146 prefixEnd_125146 19040014811162251673917 := by
  unfold tailWord_125146
  simp only [CollatzResearch.WordTrace]
  refine ⟨1141112401156222520074823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3042966403083260053532861 1141112401156222520074823)
  ·
    refine ⟨1711668601734333780112235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1141112401156222520074823 1711668601734333780112235)
    ·
      refine ⟨2567502902601500670168353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1711668601734333780112235 2567502902601500670168353)
      ·
        refine ⟨1925627176951125502626265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2567502902601500670168353 1925627176951125502626265)
        ·
          refine ⟨1444220382713344126969699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1925627176951125502626265 1444220382713344126969699)
          ·
            refine ⟨2166330574070016190454549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1444220382713344126969699 2166330574070016190454549)
            ·
              refine ⟨101546745659532008927557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2166330574070016190454549 101546745659532008927557)
              ·
                refine ⟨19040014811162251673917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101546745659532008927557 19040014811162251673917)
                ·
                  rfl

theorem cell20_125146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_125146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125146 prefixEnd_125146 := by exact prefixLift 125146
  have htrace : WordTrace (prefixWord ++ tailWord_125146) baseStart_125146 baseEnd_125146 := by
    simpa [prefixWord, tailWord_125146, baseEnd_125146] using wordTrace_append hprefix tailTrace_125146
  have hstable : (prefixWord ++ tailWord_125146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125146).length < 2 ^ (prefixWord ++ tailWord_125146).sum := by decide
  have hdescent : baseEnd_125146 < baseStart_125146 := by decide
  rcases family_descends (prefixWord ++ tailWord_125146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125167 : List Nat := [1, 1, 2, 1, 6, 1, 8]
def baseStart_125167 : Nat := 118140960795 + 125167 * 2 ^ 59
def prefixEnd_125167 : Nat := 4983230072969 + 3 ^ 40 * 125167 * 2
def baseEnd_125167 : Nat := 6347736600633779480185

theorem tailTrace_125167 : CollatzResearch.WordTrace tailWord_125167 prefixEnd_125167 6347736600633779480185 := by
  unfold tailWord_125167
  simp only [CollatzResearch.WordTrace]
  refine ⟨4565215537548810666813755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3043477025032540444542503 4565215537548810666813755)
  ·
    refine ⟨6847823306323216000220633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4565215537548810666813755 6847823306323216000220633)
    ·
      refine ⟨5135867479742412000165475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6847823306323216000220633 5135867479742412000165475)
      ·
        refine ⟨7703801219613618000248213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5135867479742412000165475 7703801219613618000248213)
        ·
          refine ⟨361115682169388343761635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7703801219613618000248213 361115682169388343761635)
          ·
            refine ⟨541673523254082515642453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361115682169388343761635 541673523254082515642453)
            ·
              refine ⟨6347736600633779480185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 541673523254082515642453 6347736600633779480185)
              ·
                rfl

theorem cell20_125167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 8].length) (baseStart_125167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125167 prefixEnd_125167 := by exact prefixLift 125167
  have htrace : WordTrace (prefixWord ++ tailWord_125167) baseStart_125167 baseEnd_125167 := by
    simpa [prefixWord, tailWord_125167, baseEnd_125167] using wordTrace_append hprefix tailTrace_125167
  have hstable : (prefixWord ++ tailWord_125167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125167).length < 2 ^ (prefixWord ++ tailWord_125167).sum := by decide
  have hdescent : baseEnd_125167 < baseStart_125167 := by decide
  rcases family_descends (prefixWord ++ tailWord_125167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125198 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 6]
def baseStart_125198 : Nat := 118140960795 + 125198 * 2 ^ 59
def prefixEnd_125198 : Nat := 4983230072969 + 3 ^ 40 * 125198 * 2
def baseEnd_125198 : Nat := 57143778650405685288205

theorem tailTrace_125198 : CollatzResearch.WordTrace tailWord_125198 prefixEnd_125198 57143778650405685288205 := by
  unfold tailWord_125198
  simp only [CollatzResearch.WordTrace]
  refine ⟨570793275054562870149031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3044230800291001974128165 570793275054562870149031)
  ·
    refine ⟨856189912581844305223547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 570793275054562870149031 856189912581844305223547)
    ·
      refine ⟨1284284868872766457835321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 856189912581844305223547 1284284868872766457835321)
      ·
        refine ⟨963213651654574843376491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1284284868872766457835321 963213651654574843376491)
        ·
          refine ⟨1444820477481862265064737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 963213651654574843376491 1444820477481862265064737)
          ·
            refine ⟨1083615358111396698798553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1444820477481862265064737 1083615358111396698798553)
            ·
              refine ⟨812711518583547524098915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1083615358111396698798553 812711518583547524098915)
              ·
                refine ⟨1219067277875321286148373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 812711518583547524098915 1219067277875321286148373)
                ·
                  refine ⟨57143778650405685288205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1219067277875321286148373 57143778650405685288205)
                  ·
                    rfl

theorem cell20_125198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_125198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125198 prefixEnd_125198 := by exact prefixLift 125198
  have htrace : WordTrace (prefixWord ++ tailWord_125198) baseStart_125198 baseEnd_125198 := by
    simpa [prefixWord, tailWord_125198, baseEnd_125198] using wordTrace_append hprefix tailTrace_125198
  have hstable : (prefixWord ++ tailWord_125198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125198).length < 2 ^ (prefixWord ++ tailWord_125198).sum := by decide
  have hdescent : baseEnd_125198 < baseStart_125198 := by decide
  rcases family_descends (prefixWord ++ tailWord_125198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125205 : List Nat := [1, 3, 2, 1, 2, 1, 4, 6]
def baseStart_125205 : Nat := 118140960795 + 125205 * 2 ^ 59
def prefixEnd_125205 : Nat := 4983230072969 + 3 ^ 40 * 125205 * 2
def baseEnd_125205 : Nat := 19048991213714924018281

theorem tailTrace_125205 : CollatzResearch.WordTrace tailWord_125205 prefixEnd_125205 19048991213714924018281 := by
  unfold tailWord_125205
  simp only [CollatzResearch.WordTrace]
  refine ⟨4566601511411143156697069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3044401007607428771131379 4566601511411143156697069)
  ·
    refine ⟨1712475566779178683761401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4566601511411143156697069 1712475566779178683761401)
    ·
      refine ⟨1284356675084384012821051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1712475566779178683761401 1284356675084384012821051)
      ·
        refine ⟨1926535012626576019231577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1284356675084384012821051 1926535012626576019231577)
        ·
          refine ⟨1444901259469932014423683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1926535012626576019231577 1444901259469932014423683)
          ·
            refine ⟨2167351889204898021635525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1444901259469932014423683 2167351889204898021635525)
            ·
              refine ⟨406378479225918379056661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2167351889204898021635525 406378479225918379056661)
              ·
                refine ⟨19048991213714924018281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 406378479225918379056661 19048991213714924018281)
                ·
                  rfl

theorem cell20_125205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 6].length) (baseStart_125205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125205 prefixEnd_125205 := by exact prefixLift 125205
  have htrace : WordTrace (prefixWord ++ tailWord_125205) baseStart_125205 baseEnd_125205 := by
    simpa [prefixWord, tailWord_125205, baseEnd_125205] using wordTrace_append hprefix tailTrace_125205
  have hstable : (prefixWord ++ tailWord_125205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125205).length < 2 ^ (prefixWord ++ tailWord_125205).sum := by decide
  have hdescent : baseEnd_125205 < baseStart_125205 := by decide
  rcases family_descends (prefixWord ++ tailWord_125205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125246 : List Nat := [4, 2, 1, 2, 1, 2, 2, 3, 3]
def baseStart_125246 : Nat := 118140960795 + 125246 * 2 ^ 59
def prefixEnd_125246 : Nat := 4983230072969 + 3 ^ 40 * 125246 * 2
def baseEnd_125246 : Nat := 57165687158330851688009

theorem tailTrace_125246 : CollatzResearch.WordTrace tailWord_125246 prefixEnd_125246 57165687158330851688009 := by
  unfold tailWord_125246
  simp only [CollatzResearch.WordTrace]
  refine ⟨571012113032825894867449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3045397936175071439293061 571012113032825894867449)
  ·
    refine ⟨428259084774619421150587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 571012113032825894867449 428259084774619421150587)
    ·
      refine ⟨642388627161929131725881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428259084774619421150587 642388627161929131725881)
      ·
        refine ⟨481791470371446848794411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 642388627161929131725881 481791470371446848794411)
        ·
          refine ⟨722687205557170273191617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481791470371446848794411 722687205557170273191617)
          ·
            refine ⟨542015404167877704893713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 722687205557170273191617 542015404167877704893713)
            ·
              refine ⟨406511553125908278670285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 542015404167877704893713 406511553125908278670285)
              ·
                refine ⟨152441832422215604501357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 406511553125908278670285 152441832422215604501357)
                ·
                  refine ⟨57165687158330851688009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152441832422215604501357 57165687158330851688009)
                  ·
                    rfl

theorem cell20_125246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_125246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125246 prefixEnd_125246 := by exact prefixLift 125246
  have htrace : WordTrace (prefixWord ++ tailWord_125246) baseStart_125246 baseEnd_125246 := by
    simpa [prefixWord, tailWord_125246, baseEnd_125246] using wordTrace_append hprefix tailTrace_125246
  have hstable : (prefixWord ++ tailWord_125246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125246).length < 2 ^ (prefixWord ++ tailWord_125246).sum := by decide
  have hdescent : baseEnd_125246 < baseStart_125246 := by decide
  rcases family_descends (prefixWord ++ tailWord_125246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125260 : List Nat := [2, 2, 1, 3, 2, 1, 5, 4]
def baseStart_125260 : Nat := 118140960795 + 125260 * 2 ^ 59
def prefixEnd_125260 : Nat := 4983230072969 + 3 ^ 40 * 125260 * 2
def baseEnd_125260 : Nat := 19057359046603008407095

theorem tailTrace_125260 : CollatzResearch.WordTrace tailWord_125260 prefixEnd_125260 19057359046603008407095 := by
  unfold tailWord_125260
  simp only [CollatzResearch.WordTrace]
  refine ⟨2284303763105943774974617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3045738350807925033299489 2284303763105943774974617)
  ·
    refine ⟨1713227822329457831230963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2284303763105943774974617 1713227822329457831230963)
    ·
      refine ⟨2569841733494186746846445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1713227822329457831230963 2569841733494186746846445)
      ·
        refine ⟨963690650060320030067417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2569841733494186746846445 963690650060320030067417)
        ·
          refine ⟨722767987545240022550563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 963690650060320030067417 722767987545240022550563)
          ·
            refine ⟨1084151981317860033825845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722767987545240022550563 1084151981317860033825845)
            ·
              refine ⟨101639248248549378171173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1084151981317860033825845 101639248248549378171173)
              ·
                refine ⟨19057359046603008407095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101639248248549378171173 19057359046603008407095)
                ·
                  rfl

theorem cell20_125260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 4].length) (baseStart_125260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125260 prefixEnd_125260 := by exact prefixLift 125260
  have htrace : WordTrace (prefixWord ++ tailWord_125260) baseStart_125260 baseEnd_125260 := by
    simpa [prefixWord, tailWord_125260, baseEnd_125260] using wordTrace_append hprefix tailTrace_125260
  have hstable : (prefixWord ++ tailWord_125260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125260).length < 2 ^ (prefixWord ++ tailWord_125260).sum := by decide
  have hdescent : baseEnd_125260 < baseStart_125260 := by decide
  rcases family_descends (prefixWord ++ tailWord_125260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125301 : List Nat := [1, 3, 4, 1, 2, 2, 3, 1, 3]
def baseStart_125301 : Nat := 118140960795 + 125301 * 2 ^ 59
def prefixEnd_125301 : Nat := 4983230072969 + 3 ^ 40 * 125301 * 2
def baseEnd_125301 : Nat := 57190790656995104854451

theorem tailTrace_125301 : CollatzResearch.WordTrace tailWord_125301 prefixEnd_125301 57190790656995104854451 := by
  unfold tailWord_125301
  simp only [CollatzResearch.WordTrace]
  refine ⟨4570102919063351552191757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3046735279375567701461171 4570102919063351552191757)
  ·
    refine ⟨1713788594648756832071909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4570102919063351552191757 1713788594648756832071909)
    ·
      refine ⟨321335361496641906013483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1713788594648756832071909 321335361496641906013483)
      ·
        refine ⟨482003042244962859020225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321335361496641906013483 482003042244962859020225)
        ·
          refine ⟨361502281683722144265169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482003042244962859020225 361502281683722144265169)
          ·
            refine ⟨271126711262791608198877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361502281683722144265169 271126711262791608198877)
            ·
              refine ⟨101672516723546853074579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271126711262791608198877 101672516723546853074579)
              ·
                refine ⟨152508775085320279611869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101672516723546853074579 152508775085320279611869)
                ·
                  refine ⟨57190790656995104854451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152508775085320279611869 57190790656995104854451)
                  ·
                    rfl

theorem cell20_125301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_125301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125301 prefixEnd_125301 := by exact prefixLift 125301
  have htrace : WordTrace (prefixWord ++ tailWord_125301) baseStart_125301 baseEnd_125301 := by
    simpa [prefixWord, tailWord_125301, baseEnd_125301] using wordTrace_append hprefix tailTrace_125301
  have hstable : (prefixWord ++ tailWord_125301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125301).length < 2 ^ (prefixWord ++ tailWord_125301).sum := by decide
  have hdescent : baseEnd_125301 < baseStart_125301 := by decide
  rcases family_descends (prefixWord ++ tailWord_125301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125315 : List Nat := [1, 1, 1, 3, 6, 2, 2, 4]
def baseStart_125315 : Nat := 118140960795 + 125315 * 2 ^ 59
def prefixEnd_125315 : Nat := 4983230072969 + 3 ^ 40 * 125315 * 2
def baseEnd_125315 : Nat := 19065726879491092795909

theorem tailTrace_125315 : CollatzResearch.WordTrace tailWord_125315 prefixEnd_125315 19065726879491092795909 := by
  unfold tailWord_125315
  simp only [CollatzResearch.WordTrace]
  refine ⟨4570613541012631943201399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3047075694008421295467599 4570613541012631943201399)
  ·
    refine ⟨6855920311518947914802099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4570613541012631943201399 6855920311518947914802099)
    ·
      refine ⟨10283880467278421872203149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6855920311518947914802099 10283880467278421872203149)
      ·
        refine ⟨3856455175229408202076181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10283880467278421872203149 3856455175229408202076181)
        ·
          refine ⟨180771336338878509472321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3856455175229408202076181 180771336338878509472321)
          ·
            refine ⟨135578502254158882104241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180771336338878509472321 135578502254158882104241)
            ·
              refine ⟨101683876690619161578181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135578502254158882104241 101683876690619161578181)
              ·
                refine ⟨19065726879491092795909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101683876690619161578181 19065726879491092795909)
                ·
                  rfl

theorem cell20_125315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 4].length) (baseStart_125315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125315 prefixEnd_125315 := by exact prefixLift 125315
  have htrace : WordTrace (prefixWord ++ tailWord_125315) baseStart_125315 baseEnd_125315 := by
    simpa [prefixWord, tailWord_125315, baseEnd_125315] using wordTrace_append hprefix tailTrace_125315
  have hstable : (prefixWord ++ tailWord_125315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125315).length < 2 ^ (prefixWord ++ tailWord_125315).sum := by decide
  have hdescent : baseEnd_125315 < baseStart_125315 := by decide
  rcases family_descends (prefixWord ++ tailWord_125315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125319 : List Nat := [1, 1, 4, 2, 2, 1, 3, 6]
def baseStart_125319 : Nat := 118140960795 + 125319 * 2 ^ 59
def prefixEnd_125319 : Nat := 4983230072969 + 3 ^ 40 * 125319 * 2
def baseEnd_125319 : Nat := 19066335449155680751459

theorem tailTrace_125319 : CollatzResearch.WordTrace tailWord_125319 prefixEnd_125319 19066335449155680751459 := by
  unfold tailWord_125319
  simp only [CollatzResearch.WordTrace]
  refine ⟨4570759432998140626347011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3047172955332093750898007 4570759432998140626347011)
  ·
    refine ⟨6856139149497210939520517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4570759432998140626347011 6856139149497210939520517)
    ·
      refine ⟨1285526090530727051160097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6856139149497210939520517 1285526090530727051160097)
      ·
        refine ⟨964144567898045288370073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1285526090530727051160097 964144567898045288370073)
        ·
          refine ⟨723108425923533966277555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 964144567898045288370073 723108425923533966277555)
          ·
            refine ⟨1084662638885300949416333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723108425923533966277555 1084662638885300949416333)
            ·
              refine ⟨406748489581987856031125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1084662638885300949416333 406748489581987856031125)
              ·
                refine ⟨19066335449155680751459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 406748489581987856031125 19066335449155680751459)
                ·
                  rfl

theorem cell20_125319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 6].length) (baseStart_125319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125319 prefixEnd_125319 := by exact prefixLift 125319
  have htrace : WordTrace (prefixWord ++ tailWord_125319) baseStart_125319 baseEnd_125319 := by
    simpa [prefixWord, tailWord_125319, baseEnd_125319] using wordTrace_append hprefix tailTrace_125319
  have hstable : (prefixWord ++ tailWord_125319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125319).length < 2 ^ (prefixWord ++ tailWord_125319).sum := by decide
  have hdescent : baseEnd_125319 < baseStart_125319 := by decide
  rcases family_descends (prefixWord ++ tailWord_125319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125336 : List Nat := [2, 1, 2, 5, 1, 3, 6]
def baseStart_125336 : Nat := 118140960795 + 125336 * 2 ^ 59
def prefixEnd_125336 : Nat := 4983230072969 + 3 ^ 40 * 125336 * 2
def baseEnd_125336 : Nat := 6356307290076726520849

theorem tailTrace_125336 : CollatzResearch.WordTrace tailWord_125336 prefixEnd_125336 6356307290076726520849 := by
  unfold tailWord_125336
  simp only [CollatzResearch.WordTrace]
  refine ⟨2285689736968276264857931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3047586315957701686477241 2285689736968276264857931)
  ·
    refine ⟨3428534605452414397286897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2285689736968276264857931 3428534605452414397286897)
    ·
      refine ⟨2571400954089310797965173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3428534605452414397286897 2571400954089310797965173)
      ·
        refine ⟨241068839445872887309235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2571400954089310797965173 241068839445872887309235)
        ·
          refine ⟨361603259168809330963853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241068839445872887309235 361603259168809330963853)
          ·
            refine ⟨135601222188303499111445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 361603259168809330963853 135601222188303499111445)
            ·
              refine ⟨6356307290076726520849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 135601222188303499111445 6356307290076726520849)
              ·
                rfl

theorem cell20_125336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 6].length) (baseStart_125336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125336 prefixEnd_125336 := by exact prefixLift 125336
  have htrace : WordTrace (prefixWord ++ tailWord_125336) baseStart_125336 baseEnd_125336 := by
    simpa [prefixWord, tailWord_125336, baseEnd_125336] using wordTrace_append hprefix tailTrace_125336
  have hstable : (prefixWord ++ tailWord_125336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125336).length < 2 ^ (prefixWord ++ tailWord_125336).sum := by decide
  have hdescent : baseEnd_125336 < baseStart_125336 := by decide
  rcases family_descends (prefixWord ++ tailWord_125336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125342 : List Nat := [4, 3, 1, 2, 1, 2, 3, 2, 2]
def baseStart_125342 : Nat := 118140960795 + 125342 * 2 ^ 59
def prefixEnd_125342 : Nat := 4983230072969 + 3 ^ 40 * 125342 * 2
def baseEnd_125342 : Nat := 57209504174181184487617

theorem tailTrace_125342 : CollatzResearch.WordTrace tailWord_125342 prefixEnd_125342 57209504174181184487617 := by
  unfold tailWord_125342
  simp only [CollatzResearch.WordTrace]
  refine ⟨571449788989351944304285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3047732207943210369622853 571449788989351944304285)
  ·
    refine ⟨214293670871006979114107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 571449788989351944304285 214293670871006979114107)
    ·
      refine ⟨321440506306510468671161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214293670871006979114107 321440506306510468671161)
      ·
        refine ⟨241080379729882851503371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321440506306510468671161 241080379729882851503371)
        ·
          refine ⟨361620569594824277255057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241080379729882851503371 361620569594824277255057)
          ·
            refine ⟨271215427196118207941293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361620569594824277255057 271215427196118207941293)
            ·
              refine ⟨101705785198544327977985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271215427196118207941293 101705785198544327977985)
              ·
                refine ⟨76279338898908245983489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101705785198544327977985 76279338898908245983489)
                ·
                  refine ⟨57209504174181184487617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76279338898908245983489 57209504174181184487617)
                  ·
                    rfl

theorem cell20_125342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_125342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125342 prefixEnd_125342 := by exact prefixLift 125342
  have htrace : WordTrace (prefixWord ++ tailWord_125342) baseStart_125342 baseEnd_125342 := by
    simpa [prefixWord, tailWord_125342, baseEnd_125342] using wordTrace_append hprefix tailTrace_125342
  have hstable : (prefixWord ++ tailWord_125342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125342).length < 2 ^ (prefixWord ++ tailWord_125342).sum := by decide
  have hdescent : baseEnd_125342 < baseStart_125342 := by decide
  rcases family_descends (prefixWord ++ tailWord_125342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125343 : List Nat := [1, 1, 2, 5, 1, 1, 2, 4, 3]
def baseStart_125343 : Nat := 118140960795 + 125343 * 2 ^ 59
def prefixEnd_125343 : Nat := 4983230072969 + 3 ^ 40 * 125343 * 2
def baseEnd_125343 : Nat := 57209960601429625454279

theorem tailTrace_125343 : CollatzResearch.WordTrace tailWord_125343 prefixEnd_125343 57209960601429625454279 := by
  unfold tailWord_125343
  simp only [CollatzResearch.WordTrace]
  refine ⟨4571634784911192725220683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3047756523274128483480455 4571634784911192725220683)
  ·
    refine ⟨6857452177366789087831025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4571634784911192725220683 6857452177366789087831025)
    ·
      refine ⟨5143089133025091815873269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6857452177366789087831025 5143089133025091815873269)
      ·
        refine ⟨482164606221102357738119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5143089133025091815873269 482164606221102357738119)
        ·
          refine ⟨723246909331653536607179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482164606221102357738119 723246909331653536607179)
          ·
            refine ⟨1084870363997480304910769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723246909331653536607179 1084870363997480304910769)
            ·
              refine ⟨813652772998110228683077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1084870363997480304910769 813652772998110228683077)
              ·
                refine ⟨152559894937145667878077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 813652772998110228683077 152559894937145667878077)
                ·
                  refine ⟨57209960601429625454279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152559894937145667878077 57209960601429625454279)
                  ·
                    rfl

theorem cell20_125343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 3].length) (baseStart_125343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125343 prefixEnd_125343 := by exact prefixLift 125343
  have htrace : WordTrace (prefixWord ++ tailWord_125343) baseStart_125343 baseEnd_125343 := by
    simpa [prefixWord, tailWord_125343, baseEnd_125343] using wordTrace_append hprefix tailTrace_125343
  have hstable : (prefixWord ++ tailWord_125343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125343).length < 2 ^ (prefixWord ++ tailWord_125343).sum := by decide
  have hdescent : baseEnd_125343 < baseStart_125343 := by decide
  rcases family_descends (prefixWord ++ tailWord_125343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125443 : List Nat := [1, 1, 1, 3, 2, 1, 6, 3, 2]
def baseStart_125443 : Nat := 118140960795 + 125443 * 2 ^ 59
def prefixEnd_125443 : Nat := 4983230072969 + 3 ^ 40 * 125443 * 2
def baseEnd_125443 : Nat := 57255603326273722120537

theorem tailTrace_125443 : CollatzResearch.WordTrace tailWord_125443 prefixEnd_125443 57255603326273722120537 := by
  unfold tailWord_125443
  simp only [CollatzResearch.WordTrace]
  refine ⟨4575282084548909803860983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3050188056365939869240655 4575282084548909803860983)
  ·
    refine ⟨6862923126823364705791475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4575282084548909803860983 6862923126823364705791475)
    ·
      refine ⟨10294384690235047058687213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6862923126823364705791475 10294384690235047058687213)
      ·
        refine ⟨3860394258838142647007705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10294384690235047058687213 3860394258838142647007705)
        ·
          refine ⟨2895295694128606985255779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3860394258838142647007705 2895295694128606985255779)
          ·
            refine ⟨4342943541192910477883669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2895295694128606985255779 4342943541192910477883669)
            ·
              refine ⟨203575478493417678650797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4342943541192910477883669 203575478493417678650797)
              ·
                refine ⟨76340804435031629494049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203575478493417678650797 76340804435031629494049)
                ·
                  refine ⟨57255603326273722120537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76340804435031629494049 57255603326273722120537)
                  ·
                    rfl

theorem cell20_125443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 3, 2].length) (baseStart_125443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125443 prefixEnd_125443 := by exact prefixLift 125443
  have htrace : WordTrace (prefixWord ++ tailWord_125443) baseStart_125443 baseEnd_125443 := by
    simpa [prefixWord, tailWord_125443, baseEnd_125443] using wordTrace_append hprefix tailTrace_125443
  have hstable : (prefixWord ++ tailWord_125443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125443).length < 2 ^ (prefixWord ++ tailWord_125443).sum := by decide
  have hdescent : baseEnd_125443 < baseStart_125443 := by decide
  rcases family_descends (prefixWord ++ tailWord_125443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125446 : List Nat := [6, 2, 1, 1, 1, 2, 7]
def baseStart_125446 : Nat := 118140960795 + 125446 * 2 ^ 59
def prefixEnd_125446 : Nat := 4983230072969 + 3 ^ 40 * 125446 * 2
def baseEnd_125446 : Nat := 6361885845335449446725

theorem tailTrace_125446 : CollatzResearch.WordTrace tailWord_125446 prefixEnd_125446 6361885845335449446725 := by
  unfold tailWord_125446
  simp only [CollatzResearch.WordTrace]
  refine ⟨142980984485563791131881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3050261002358694210813461 142980984485563791131881)
  ·
    refine ⟨107235738364172843348911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142980984485563791131881 107235738364172843348911)
    ·
      refine ⟨160853607546259265023367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107235738364172843348911 160853607546259265023367)
      ·
        refine ⟨241280411319388897535051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160853607546259265023367 241280411319388897535051)
        ·
          refine ⟨361920616979083346302577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241280411319388897535051 361920616979083346302577)
          ·
            refine ⟨271440462734312509726933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361920616979083346302577 271440462734312509726933)
            ·
              refine ⟨6361885845335449446725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 271440462734312509726933 6361885845335449446725)
              ·
                rfl

theorem cell20_125446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 7].length) (baseStart_125446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125446 prefixEnd_125446 := by exact prefixLift 125446
  have htrace : WordTrace (prefixWord ++ tailWord_125446) baseStart_125446 baseEnd_125446 := by
    simpa [prefixWord, tailWord_125446, baseEnd_125446] using wordTrace_append hprefix tailTrace_125446
  have hstable : (prefixWord ++ tailWord_125446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125446).length < 2 ^ (prefixWord ++ tailWord_125446).sum := by decide
  have hdescent : baseEnd_125446 < baseStart_125446 := by decide
  rcases family_descends (prefixWord ++ tailWord_125446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125453 : List Nat := [1, 7, 1, 1, 1, 2, 1, 1, 5]
def baseStart_125453 : Nat := 118140960795 + 125453 * 2 ^ 59
def prefixEnd_125453 : Nat := 4983230072969 + 3 ^ 40 * 125453 * 2
def baseEnd_125453 : Nat := 57260167598758131787163

theorem tailTrace_125453 : CollatzResearch.WordTrace tailWord_125453 prefixEnd_125453 57260167598758131787163 := by
  unfold tailWord_125453
  simp only [CollatzResearch.WordTrace]
  refine ⟨4575646814512681511725013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3050431209675121007816675 4575646814512681511725013)
  ·
    refine ⟨107241722215140972931055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 4575646814512681511725013 107241722215140972931055)
    ·
      refine ⟨160862583322711459396583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107241722215140972931055 160862583322711459396583)
      ·
        refine ⟨241293874984067189094875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160862583322711459396583 241293874984067189094875)
        ·
          refine ⟨361940812476100783642313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241293874984067189094875 361940812476100783642313)
          ·
            refine ⟨271455609357075587731735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361940812476100783642313 271455609357075587731735)
            ·
              refine ⟨407183414035613381597603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271455609357075587731735 407183414035613381597603)
              ·
                refine ⟨610775121053420072396405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407183414035613381597603 610775121053420072396405)
                ·
                  refine ⟨57260167598758131787163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 610775121053420072396405 57260167598758131787163)
                  ·
                    rfl

theorem cell20_125453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_125453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125453 prefixEnd_125453 := by exact prefixLift 125453
  have htrace : WordTrace (prefixWord ++ tailWord_125453) baseStart_125453 baseEnd_125453 := by
    simpa [prefixWord, tailWord_125453, baseEnd_125453] using wordTrace_append hprefix tailTrace_125453
  have hstable : (prefixWord ++ tailWord_125453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125453).length < 2 ^ (prefixWord ++ tailWord_125453).sum := by decide
  have hdescent : baseEnd_125453 < baseStart_125453 := by decide
  rcases family_descends (prefixWord ++ tailWord_125453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125460 : List Nat := [2, 4, 3, 1, 1, 2, 2, 1, 4]
def baseStart_125460 : Nat := 118140960795 + 125460 * 2 ^ 59
def prefixEnd_125460 : Nat := 4983230072969 + 3 ^ 40 * 125460 * 2
def baseEnd_125460 : Nat := 57263362589497218553801

theorem tailTrace_125460 : CollatzResearch.WordTrace tailWord_125460 prefixEnd_125460 57263362589497218553801 := by
  unfold tailWord_125460
  simp only [CollatzResearch.WordTrace]
  refine ⟨2287951062743660853614917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3050601416991547804819889 2287951062743660853614917)
  ·
    refine ⟨428990824264436410052797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2287951062743660853614917 428990824264436410052797)
    ·
      refine ⟨160871559099163653769799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428990824264436410052797 160871559099163653769799)
      ·
        refine ⟨241307338648745480654699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160871559099163653769799 241307338648745480654699)
        ·
          refine ⟨361961007973118220982049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241307338648745480654699 361961007973118220982049)
          ·
            refine ⟨271470755979838665736537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361961007973118220982049 271470755979838665736537)
            ·
              refine ⟨203603066984878999302403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271470755979838665736537 203603066984878999302403)
              ·
                refine ⟨305404600477318498953605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203603066984878999302403 305404600477318498953605)
                ·
                  refine ⟨57263362589497218553801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 305404600477318498953605 57263362589497218553801)
                  ·
                    rfl

theorem cell20_125460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_125460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125460 prefixEnd_125460 := by exact prefixLift 125460
  have htrace : WordTrace (prefixWord ++ tailWord_125460) baseStart_125460 baseEnd_125460 := by
    simpa [prefixWord, tailWord_125460, baseEnd_125460] using wordTrace_append hprefix tailTrace_125460
  have hstable : (prefixWord ++ tailWord_125460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125460).length < 2 ^ (prefixWord ++ tailWord_125460).sum := by decide
  have hdescent : baseEnd_125460 < baseStart_125460 := by decide
  rcases family_descends (prefixWord ++ tailWord_125460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125464 : List Nat := [2, 1, 2, 3, 3, 1, 1, 3, 4]
def baseStart_125464 : Nat := 118140960795 + 125464 * 2 ^ 59
def prefixEnd_125464 : Nat := 4983230072969 + 3 ^ 40 * 125464 * 2
def baseEnd_125464 : Nat := 57265188298490982420451

theorem tailTrace_125464 : CollatzResearch.WordTrace tailWord_125464 prefixEnd_125464 57265188298490982420451 := by
  unfold tailWord_125464
  simp only [CollatzResearch.WordTrace]
  refine ⟨2288024008736415195187723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3050698678315220260250297 2288024008736415195187723)
  ·
    refine ⟨3432036013104622792781585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2288024008736415195187723 3432036013104622792781585)
    ·
      refine ⟨2574027009828467094586189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3432036013104622792781585 2574027009828467094586189)
      ·
        refine ⟨965260128685675160469821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2574027009828467094586189 965260128685675160469821)
        ·
          refine ⟨361972548257128185176183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 965260128685675160469821 361972548257128185176183)
          ·
            refine ⟨542958822385692277764275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361972548257128185176183 542958822385692277764275)
            ·
              refine ⟨814438233578538416646413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542958822385692277764275 814438233578538416646413)
              ·
                refine ⟨305414337591951906242405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 814438233578538416646413 305414337591951906242405)
                ·
                  refine ⟨57265188298490982420451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 305414337591951906242405 57265188298490982420451)
                  ·
                    rfl

theorem cell20_125464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_125464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125464 prefixEnd_125464 := by exact prefixLift 125464
  have htrace : WordTrace (prefixWord ++ tailWord_125464) baseStart_125464 baseEnd_125464 := by
    simpa [prefixWord, tailWord_125464, baseEnd_125464] using wordTrace_append hprefix tailTrace_125464
  have hstable : (prefixWord ++ tailWord_125464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125464).length < 2 ^ (prefixWord ++ tailWord_125464).sum := by decide
  have hdescent : baseEnd_125464 < baseStart_125464 := by decide
  rcases family_descends (prefixWord ++ tailWord_125464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125498 : List Nat := [3, 1, 1, 1, 3, 5, 1, 3, 2]
def baseStart_125498 : Nat := 118140960795 + 125498 * 2 ^ 59
def prefixEnd_125498 : Nat := 4983230072969 + 3 ^ 40 * 125498 * 2
def baseEnd_125498 : Nat := 57280706824937975286979

theorem tailTrace_125498 : CollatzResearch.WordTrace tailWord_125498 prefixEnd_125498 57280706824937975286979 := by
  unfold tailWord_125498
  simp only [CollatzResearch.WordTrace]
  refine ⟨1144322024837413549278287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3051525399566436131408765 1144322024837413549278287)
  ·
    refine ⟨1716483037256120323917431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1144322024837413549278287 1716483037256120323917431)
    ·
      refine ⟨2574724555884180485876147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1716483037256120323917431 2574724555884180485876147)
      ·
        refine ⟨3862086833826270728814221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2574724555884180485876147 3862086833826270728814221)
        ·
          refine ⟨1448282562684851523305333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3862086833826270728814221 1448282562684851523305333)
          ·
            refine ⟨135776490251704830309875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1448282562684851523305333 135776490251704830309875)
            ·
              refine ⟨203664735377557245464813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135776490251704830309875 203664735377557245464813)
              ·
                refine ⟨76374275766583967049305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203664735377557245464813 76374275766583967049305)
                ·
                  refine ⟨57280706824937975286979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76374275766583967049305 57280706824937975286979)
                  ·
                    rfl

theorem cell20_125498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 3, 2].length) (baseStart_125498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125498 prefixEnd_125498 := by exact prefixLift 125498
  have htrace : WordTrace (prefixWord ++ tailWord_125498) baseStart_125498 baseEnd_125498 := by
    simpa [prefixWord, tailWord_125498, baseEnd_125498] using wordTrace_append hprefix tailTrace_125498
  have hstable : (prefixWord ++ tailWord_125498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125498).length < 2 ^ (prefixWord ++ tailWord_125498).sum := by decide
  have hdescent : baseEnd_125498 < baseStart_125498 := by decide
  rcases family_descends (prefixWord ++ tailWord_125498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125509 : List Nat := [1, 3, 1, 1, 1, 7, 6]
def baseStart_125509 : Nat := 118140960795 + 125509 * 2 ^ 59
def prefixEnd_125509 : Nat := 4983230072969 + 3 ^ 40 * 125509 * 2
def baseEnd_125509 : Nat := 6365080836074536213363

theorem tailTrace_125509 : CollatzResearch.WordTrace tailWord_125509 prefixEnd_125509 6365080836074536213363 := by
  unfold tailWord_125509
  simp only [CollatzResearch.WordTrace]
  refine ⟨4577689302309803075763581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3051792868206535383842387 4577689302309803075763581)
  ·
    refine ⟨1716633488366176153411343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4577689302309803075763581 1716633488366176153411343)
    ·
      refine ⟨2574950232549264230117015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1716633488366176153411343 2574950232549264230117015)
      ·
        refine ⟨3862425348823896345175523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2574950232549264230117015 3862425348823896345175523)
        ·
          refine ⟨5793638023235844517763285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3862425348823896345175523 5793638023235844517763285)
          ·
            refine ⟨135788391169590105885077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 5793638023235844517763285 135788391169590105885077)
            ·
              refine ⟨6365080836074536213363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 135788391169590105885077 6365080836074536213363)
              ·
                rfl

theorem cell20_125509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 6].length) (baseStart_125509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125509 prefixEnd_125509 := by exact prefixLift 125509
  have htrace : WordTrace (prefixWord ++ tailWord_125509) baseStart_125509 baseEnd_125509 := by
    simpa [prefixWord, tailWord_125509, baseEnd_125509] using wordTrace_append hprefix tailTrace_125509
  have hstable : (prefixWord ++ tailWord_125509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125509).length < 2 ^ (prefixWord ++ tailWord_125509).sum := by decide
  have hdescent : baseEnd_125509 < baseStart_125509 := by decide
  rcases family_descends (prefixWord ++ tailWord_125509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125516 : List Nat := [2, 2, 1, 3, 1, 2, 1, 3, 5]
def baseStart_125516 : Nat := 118140960795 + 125516 * 2 ^ 59
def prefixEnd_125516 : Nat := 4983230072969 + 3 ^ 40 * 125516 * 2
def baseEnd_125516 : Nat := 57288922515409912686905

theorem tailTrace_125516 : CollatzResearch.WordTrace tailWord_125516 prefixEnd_125516 57288922515409912686905 := by
  unfold tailWord_125516
  simp only [CollatzResearch.WordTrace]
  refine ⟨2288972306642221635634201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3051963075522962180845601 2288972306642221635634201)
  ·
    refine ⟨1716729229981666226725651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2288972306642221635634201 1716729229981666226725651)
    ·
      refine ⟨2575093844972499340088477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1716729229981666226725651 2575093844972499340088477)
      ·
        refine ⟨965660191864687252533179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2575093844972499340088477 965660191864687252533179)
        ·
          refine ⟨1448490287797030878799769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 965660191864687252533179 1448490287797030878799769)
          ·
            refine ⟨1086367715847773159099827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1448490287797030878799769 1086367715847773159099827)
            ·
              refine ⟨1629551573771659738649741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086367715847773159099827 1629551573771659738649741)
              ·
                refine ⟨611081840164372401993653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1629551573771659738649741 611081840164372401993653)
                ·
                  refine ⟨57288922515409912686905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 611081840164372401993653 57288922515409912686905)
                  ·
                    rfl

theorem cell20_125516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_125516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125516 prefixEnd_125516 := by exact prefixLift 125516
  have htrace : WordTrace (prefixWord ++ tailWord_125516) baseStart_125516 baseEnd_125516 := by
    simpa [prefixWord, tailWord_125516, baseEnd_125516] using wordTrace_append hprefix tailTrace_125516
  have hstable : (prefixWord ++ tailWord_125516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125516).length < 2 ^ (prefixWord ++ tailWord_125516).sum := by decide
  have hdescent : baseEnd_125516 < baseStart_125516 := by decide
  rcases family_descends (prefixWord ++ tailWord_125516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125568 : List Nat := [2, 1, 1, 2, 1, 13]
def baseStart_125568 : Nat := 118140960795 + 125568 * 2 ^ 59
def prefixEnd_125568 : Nat := 4983230072969 + 3 ^ 40 * 125568 * 2
def baseEnd_125568 : Nat := 2122690990086253442717

theorem tailTrace_125568 : CollatzResearch.WordTrace tailWord_125568 prefixEnd_125568 2122690990086253442717 := by
  unfold tailWord_125568
  simp only [CollatzResearch.WordTrace]
  refine ⟨2289920604548028076080679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3053227472730704101440905 2289920604548028076080679)
  ·
    refine ⟨3434880906822042114121019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2289920604548028076080679 3434880906822042114121019)
    ·
      refine ⟨5152321360233063171181529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3434880906822042114121019 5152321360233063171181529)
      ·
        refine ⟨3864241020174797378386147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5152321360233063171181529 3864241020174797378386147)
        ·
          refine ⟨5796361530262196067579221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3864241020174797378386147 5796361530262196067579221)
          ·
            refine ⟨2122690990086253442717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 5796361530262196067579221 2122690990086253442717)
            ·
              rfl

theorem cell20_125568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 13].length) (baseStart_125568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125568 prefixEnd_125568 := by exact prefixLift 125568
  have htrace : WordTrace (prefixWord ++ tailWord_125568) baseStart_125568 baseEnd_125568 := by
    simpa [prefixWord, tailWord_125568, baseEnd_125568] using wordTrace_append hprefix tailTrace_125568
  have hstable : (prefixWord ++ tailWord_125568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125568).length < 2 ^ (prefixWord ++ tailWord_125568).sum := by decide
  have hdescent : baseEnd_125568 < baseStart_125568 := by decide
  rcases family_descends (prefixWord ++ tailWord_125568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125588 : List Nat := [2, 4, 2, 2, 1, 1, 2, 3, 3]
def baseStart_125588 : Nat := 118140960795 + 125588 * 2 ^ 59
def prefixEnd_125588 : Nat := 4983230072969 + 3 ^ 40 * 125588 * 2
def baseEnd_125588 : Nat := 57321785277297662286611

theorem tailTrace_125588 : CollatzResearch.WordTrace tailWord_125588 prefixEnd_125588 57321785277297662286611 := by
  unfold tailWord_125588
  simp only [CollatzResearch.WordTrace]
  refine ⟨2290285334511799783944709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3053713779349066378592945 2290285334511799783944709)
  ·
    refine ⟨429428500220962459489633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2290285334511799783944709 429428500220962459489633)
    ·
      refine ⟨322071375165721844617225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429428500220962459489633 322071375165721844617225)
      ·
        refine ⟨241553531374291383462919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322071375165721844617225 241553531374291383462919)
        ·
          refine ⟨362330297061437075194379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241553531374291383462919 362330297061437075194379)
          ·
            refine ⟨543495445592155612791569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362330297061437075194379 543495445592155612791569)
            ·
              refine ⟨407621584194116709593677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 543495445592155612791569 407621584194116709593677)
              ·
                refine ⟨152858094072793766097629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 407621584194116709593677 152858094072793766097629)
                ·
                  refine ⟨57321785277297662286611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152858094072793766097629 57321785277297662286611)
                  ·
                    rfl

theorem cell20_125588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_125588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125588 prefixEnd_125588 := by exact prefixLift 125588
  have htrace : WordTrace (prefixWord ++ tailWord_125588) baseStart_125588 baseEnd_125588 := by
    simpa [prefixWord, tailWord_125588, baseEnd_125588] using wordTrace_append hprefix tailTrace_125588
  have hstable : (prefixWord ++ tailWord_125588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125588).length < 2 ^ (prefixWord ++ tailWord_125588).sum := by decide
  have hdescent : baseEnd_125588 < baseStart_125588 := by decide
  rcases family_descends (prefixWord ++ tailWord_125588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125622 : List Nat := [5, 1, 3, 1, 2, 2, 1, 2, 3]
def baseStart_125622 : Nat := 118140960795 + 125622 * 2 ^ 59
def prefixEnd_125622 : Nat := 4983230072969 + 3 ^ 40 * 125622 * 2
def baseEnd_125622 : Nat := 57337303803744655153139

theorem tailTrace_125622 : CollatzResearch.WordTrace tailWord_125622 prefixEnd_125622 57337303803744655153139 := by
  unfold tailWord_125622
  simp only [CollatzResearch.WordTrace]
  refine ⟨286363171931276460914195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3054540500600282249751413 286363171931276460914195)
  ·
    refine ⟨429544757896914691371293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286363171931276460914195 429544757896914691371293)
    ·
      refine ⟨161079284211343009264235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 429544757896914691371293 161079284211343009264235)
      ·
        refine ⟨241618926317014513896353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161079284211343009264235 241618926317014513896353)
        ·
          refine ⟨181214194737760885422265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241618926317014513896353 181214194737760885422265)
          ·
            refine ⟨135910646053320664066699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181214194737760885422265 135910646053320664066699)
            ·
              refine ⟨203865969079980996100049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135910646053320664066699 203865969079980996100049)
              ·
                refine ⟨152899476809985747075037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203865969079980996100049 152899476809985747075037)
                ·
                  refine ⟨57337303803744655153139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152899476809985747075037 57337303803744655153139)
                  ·
                    rfl

theorem cell20_125622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_125622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125622 prefixEnd_125622 := by exact prefixLift 125622
  have htrace : WordTrace (prefixWord ++ tailWord_125622) baseStart_125622 baseEnd_125622 := by
    simpa [prefixWord, tailWord_125622, baseEnd_125622] using wordTrace_append hprefix tailTrace_125622
  have hstable : (prefixWord ++ tailWord_125622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125622).length < 2 ^ (prefixWord ++ tailWord_125622).sum := by decide
  have hdescent : baseEnd_125622 < baseStart_125622 := by decide
  rcases family_descends (prefixWord ++ tailWord_125622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125623 : List Nat := [1, 1, 3, 1, 6, 1, 7]
def baseStart_125623 : Nat := 118140960795 + 125623 * 2 ^ 59
def prefixEnd_125623 : Nat := 4983230072969 + 3 ^ 40 * 125623 * 2
def baseEnd_125623 : Nat := 6370862247888121791089

theorem tailTrace_125623 : CollatzResearch.WordTrace tailWord_125623 prefixEnd_125623 6370862247888121791089 := by
  unfold tailWord_125623
  simp only [CollatzResearch.WordTrace]
  refine ⟨4581847223896800545413523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3054564815931200363609015 4581847223896800545413523)
  ·
    refine ⟨6872770835845200818120285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4581847223896800545413523 6872770835845200818120285)
    ·
      refine ⟨2577289063441950306795107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6872770835845200818120285 2577289063441950306795107)
      ·
        refine ⟨3865933595162925460192661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2577289063441950306795107 3865933595162925460192661)
        ·
          refine ⟨181215637273262130946531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3865933595162925460192661 181215637273262130946531)
          ·
            refine ⟨271823455909893196419797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181215637273262130946531 271823455909893196419797)
            ·
              refine ⟨6370862247888121791089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 271823455909893196419797 6370862247888121791089)
              ·
                rfl

theorem cell20_125623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 7].length) (baseStart_125623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125623 prefixEnd_125623 := by exact prefixLift 125623
  have htrace : WordTrace (prefixWord ++ tailWord_125623) baseStart_125623 baseEnd_125623 := by
    simpa [prefixWord, tailWord_125623, baseEnd_125623] using wordTrace_append hprefix tailTrace_125623
  have hstable : (prefixWord ++ tailWord_125623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125623).length < 2 ^ (prefixWord ++ tailWord_125623).sum := by decide
  have hdescent : baseEnd_125623 < baseStart_125623 := by decide
  rcases family_descends (prefixWord ++ tailWord_125623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125668 : List Nat := [2, 3, 1, 1, 1, 4, 1, 2, 5]
def baseStart_125668 : Nat := 118140960795 + 125668 * 2 ^ 59
def prefixEnd_125668 : Nat := 4983230072969 + 3 ^ 40 * 125668 * 2
def baseEnd_125668 : Nat := 57358299457172939619617

theorem tailTrace_125668 : CollatzResearch.WordTrace tailWord_125668 prefixEnd_125668 57358299457172939619617 := by
  unfold tailWord_125668
  simp only [CollatzResearch.WordTrace]
  refine ⟨2291744254366886615400829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3055659005822515487201105 2291744254366886615400829)
  ·
    refine ⟨859404095387582480775311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2291744254366886615400829 859404095387582480775311)
    ·
      refine ⟨1289106143081373721162967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 859404095387582480775311 1289106143081373721162967)
      ·
        refine ⟨1933659214622060581744451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1289106143081373721162967 1933659214622060581744451)
        ·
          refine ⟨2900488821933090872616677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1933659214622060581744451 2900488821933090872616677)
          ·
            refine ⟨543841654112454538615627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2900488821933090872616677 543841654112454538615627)
            ·
              refine ⟨815762481168681807923441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543841654112454538615627 815762481168681807923441)
              ·
                refine ⟨611821860876511355942581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 815762481168681807923441 611821860876511355942581)
                ·
                  refine ⟨57358299457172939619617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 611821860876511355942581 57358299457172939619617)
                  ·
                    rfl

theorem cell20_125668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_125668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125668 prefixEnd_125668 := by exact prefixLift 125668
  have htrace : WordTrace (prefixWord ++ tailWord_125668) baseStart_125668 baseEnd_125668 := by
    simpa [prefixWord, tailWord_125668, baseEnd_125668] using wordTrace_append hprefix tailTrace_125668
  have hstable : (prefixWord ++ tailWord_125668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125668).length < 2 ^ (prefixWord ++ tailWord_125668).sum := by decide
  have hdescent : baseEnd_125668 < baseStart_125668 := by decide
  rcases family_descends (prefixWord ++ tailWord_125668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125684 : List Nat := [2, 6, 1, 1, 3, 1, 1, 1, 4]
def baseStart_125684 : Nat := 118140960795 + 125684 * 2 ^ 59
def prefixEnd_125684 : Nat := 4983230072969 + 3 ^ 40 * 125684 * 2
def baseEnd_125684 : Nat := 57365602293147995086219

theorem tailTrace_125684 : CollatzResearch.WordTrace tailWord_125684 prefixEnd_125684 57365602293147995086219 := by
  unfold tailWord_125684
  simp only [CollatzResearch.WordTrace]
  refine ⟨2292036038337903981692053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3056048051117205308922737 2292036038337903981692053)
  ·
    refine ⟨107439189297089249141815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2292036038337903981692053 107439189297089249141815)
    ·
      refine ⟨161158783945633873712723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107439189297089249141815 161158783945633873712723)
      ·
        refine ⟨241738175918450810569085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161158783945633873712723 241738175918450810569085)
        ·
          refine ⟨90651815969419053963407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241738175918450810569085 90651815969419053963407)
          ·
            refine ⟨135977723954128580945111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90651815969419053963407 135977723954128580945111)
            ·
              refine ⟨203966585931192871417667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135977723954128580945111 203966585931192871417667)
              ·
                refine ⟨305949878896789307126501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203966585931192871417667 305949878896789307126501)
                ·
                  refine ⟨57365602293147995086219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 305949878896789307126501 57365602293147995086219)
                  ·
                    rfl

theorem cell20_125684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_125684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125684 prefixEnd_125684 := by exact prefixLift 125684
  have htrace : WordTrace (prefixWord ++ tailWord_125684) baseStart_125684 baseEnd_125684 := by
    simpa [prefixWord, tailWord_125684, baseEnd_125684] using wordTrace_append hprefix tailTrace_125684
  have hstable : (prefixWord ++ tailWord_125684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125684).length < 2 ^ (prefixWord ++ tailWord_125684).sum := by decide
  have hdescent : baseEnd_125684 < baseStart_125684 := by decide
  rcases family_descends (prefixWord ++ tailWord_125684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125692 : List Nat := [2, 2, 2, 1, 3, 2, 3, 1, 4]
def baseStart_125692 : Nat := 118140960795 + 125692 * 2 ^ 59
def prefixEnd_125692 : Nat := 4983230072969 + 3 ^ 40 * 125692 * 2
def baseEnd_125692 : Nat := 57369253711135522819519

theorem tailTrace_125692 : CollatzResearch.WordTrace tailWord_125692 prefixEnd_125692 57369253711135522819519 := by
  unfold tailWord_125692
  simp only [CollatzResearch.WordTrace]
  refine ⟨2292181930323412664837665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3056242573764550219783553 2292181930323412664837665)
  ·
    refine ⟨1719136447742559498628249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2292181930323412664837665 1719136447742559498628249)
    ·
      refine ⟨1289352335806919623971187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1719136447742559498628249 1289352335806919623971187)
      ·
        refine ⟨1934028503710379435956781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1289352335806919623971187 1934028503710379435956781)
        ·
          refine ⟨725260688891392288483793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1934028503710379435956781 725260688891392288483793)
          ·
            refine ⟨543945516668544216362845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 725260688891392288483793 543945516668544216362845)
            ·
              refine ⟨203979568750704081136067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 543945516668544216362845 203979568750704081136067)
              ·
                refine ⟨305969353126056121704101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203979568750704081136067 305969353126056121704101)
                ·
                  refine ⟨57369253711135522819519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 305969353126056121704101 57369253711135522819519)
                  ·
                    rfl

theorem cell20_125692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_125692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125692 prefixEnd_125692 := by exact prefixLift 125692
  have htrace : WordTrace (prefixWord ++ tailWord_125692) baseStart_125692 baseEnd_125692 := by
    simpa [prefixWord, tailWord_125692, baseEnd_125692] using wordTrace_append hprefix tailTrace_125692
  have hstable : (prefixWord ++ tailWord_125692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125692).length < 2 ^ (prefixWord ++ tailWord_125692).sum := by decide
  have hdescent : baseEnd_125692 < baseStart_125692 := by decide
  rcases family_descends (prefixWord ++ tailWord_125692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125713 : List Nat := [1, 2, 2, 1, 1, 3, 2, 4, 4]
def baseStart_125713 : Nat := 118140960795 + 125713 * 2 ^ 59
def prefixEnd_125713 : Nat := 4983230072969 + 3 ^ 40 * 125713 * 2
def baseEnd_125713 : Nat := 57378838683352783119433

theorem tailTrace_125713 : CollatzResearch.WordTrace tailWord_125713 prefixEnd_125713 57378838683352783119433 := by
  unfold tailWord_125713
  simp only [CollatzResearch.WordTrace]
  refine ⟨4585129793570745916189793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3056753195713830610793195 4585129793570745916189793)
  ·
    refine ⟨3438847345178059437142345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4585129793570745916189793 3438847345178059437142345)
    ·
      refine ⟨2579135508883544577856759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3438847345178059437142345 2579135508883544577856759)
      ·
        refine ⟨3868703263325316866785139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2579135508883544577856759 3868703263325316866785139)
        ·
          refine ⟨5803054894987975300177709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3868703263325316866785139 5803054894987975300177709)
          ·
            refine ⟨2176145585620490737566641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5803054894987975300177709 2176145585620490737566641)
            ·
              refine ⟨1632109189215368053174981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2176145585620490737566641 1632109189215368053174981)
              ·
                refine ⟨306020472977881509970309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1632109189215368053174981 306020472977881509970309)
                ·
                  refine ⟨57378838683352783119433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 306020472977881509970309 57378838683352783119433)
                  ·
                    rfl

theorem cell20_125713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_125713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125713 prefixEnd_125713 := by exact prefixLift 125713
  have htrace : WordTrace (prefixWord ++ tailWord_125713) baseStart_125713 baseEnd_125713 := by
    simpa [prefixWord, tailWord_125713, baseEnd_125713] using wordTrace_append hprefix tailTrace_125713
  have hstable : (prefixWord ++ tailWord_125713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125713).length < 2 ^ (prefixWord ++ tailWord_125713).sum := by decide
  have hdescent : baseEnd_125713 < baseStart_125713 := by decide
  rcases family_descends (prefixWord ++ tailWord_125713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125747 : List Nat := [1, 1, 1, 2, 6, 2, 1, 4, 2]
def baseStart_125747 : Nat := 118140960795 + 125747 * 2 ^ 59
def prefixEnd_125747 : Nat := 4983230072969 + 3 ^ 40 * 125747 * 2
def baseEnd_125747 : Nat := 57394357209799775985961

theorem tailTrace_125747 : CollatzResearch.WordTrace tailWord_125747 prefixEnd_125747 57394357209799775985961 := by
  unfold tailWord_125747
  simp only [CollatzResearch.WordTrace]
  refine ⟨4586369875447569722927495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3057579916965046481951663 4586369875447569722927495)
  ·
    refine ⟨6879554813171354584391243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4586369875447569722927495 6879554813171354584391243)
    ·
      refine ⟨10319332219757031876586865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6879554813171354584391243 10319332219757031876586865)
      ·
        refine ⟨7739499164817773907440149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10319332219757031876586865 7739499164817773907440149)
        ·
          refine ⟨362789023350833151911257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7739499164817773907440149 362789023350833151911257)
          ·
            refine ⟨272091767513124863933443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362789023350833151911257 272091767513124863933443)
            ·
              refine ⟨408137651269687295900165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272091767513124863933443 408137651269687295900165)
              ·
                refine ⟨76525809613066367981281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 408137651269687295900165 76525809613066367981281)
                ·
                  refine ⟨57394357209799775985961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76525809613066367981281 57394357209799775985961)
                  ·
                    rfl

theorem cell20_125747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 4, 2].length) (baseStart_125747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125747 prefixEnd_125747 := by exact prefixLift 125747
  have htrace : WordTrace (prefixWord ++ tailWord_125747) baseStart_125747 baseEnd_125747 := by
    simpa [prefixWord, tailWord_125747, baseEnd_125747] using wordTrace_append hprefix tailTrace_125747
  have hstable : (prefixWord ++ tailWord_125747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125747).length < 2 ^ (prefixWord ++ tailWord_125747).sum := by decide
  have hdescent : baseEnd_125747 < baseStart_125747 := by decide
  rcases family_descends (prefixWord ++ tailWord_125747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125750 : List Nat := [5, 1, 2, 2, 3, 1, 1, 5]
def baseStart_125750 : Nat := 118140960795 + 125750 * 2 ^ 59
def prefixEnd_125750 : Nat := 4983230072969 + 3 ^ 40 * 125750 * 2
def baseEnd_125750 : Nat := 19131908830515032961983

theorem tailTrace_125750 : CollatzResearch.WordTrace tailWord_125750 prefixEnd_125750 19131908830515032961983 := by
  unfold tailWord_125750
  simp only [CollatzResearch.WordTrace]
  refine ⟨286654955902293827205419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3057652862957800823524469 286654955902293827205419)
  ·
    refine ⟨429982433853440740808129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286654955902293827205419 429982433853440740808129)
    ·
      refine ⟨322486825390080555606097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429982433853440740808129 322486825390080555606097)
      ·
        refine ⟨241865119042560416704573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322486825390080555606097 241865119042560416704573)
        ·
          refine ⟨90699419640960156264215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241865119042560416704573 90699419640960156264215)
          ·
            refine ⟨136049129461440234396323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90699419640960156264215 136049129461440234396323)
            ·
              refine ⟨204073694192160351594485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136049129461440234396323 204073694192160351594485)
              ·
                refine ⟨19131908830515032961983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 204073694192160351594485 19131908830515032961983)
                ·
                  rfl

theorem cell20_125750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_125750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125750 prefixEnd_125750 := by exact prefixLift 125750
  have htrace : WordTrace (prefixWord ++ tailWord_125750) baseStart_125750 baseEnd_125750 := by
    simpa [prefixWord, tailWord_125750, baseEnd_125750] using wordTrace_append hprefix tailTrace_125750
  have hstable : (prefixWord ++ tailWord_125750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125750).length < 2 ^ (prefixWord ++ tailWord_125750).sum := by decide
  have hdescent : baseEnd_125750 < baseStart_125750 := by decide
  rcases family_descends (prefixWord ++ tailWord_125750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125751 : List Nat := [1, 1, 3, 1, 2, 1, 4, 3, 4]
def baseStart_125751 : Nat := 118140960795 + 125751 * 2 ^ 59
def prefixEnd_125751 : Nat := 4983230072969 + 3 ^ 40 * 125751 * 2
def baseEnd_125751 : Nat := 57396182918793539852611

theorem tailTrace_125751 : CollatzResearch.WordTrace tailWord_125751 prefixEnd_125751 57396182918793539852611 := by
  unfold tailWord_125751
  simp only [CollatzResearch.WordTrace]
  refine ⟨4586515767433078406073107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3057677178288718937382071 4586515767433078406073107)
  ·
    refine ⟨6879773651149617609109661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4586515767433078406073107 6879773651149617609109661)
    ·
      refine ⟨2579915119181106603416123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6879773651149617609109661 2579915119181106603416123)
      ·
        refine ⟨3869872678771659905124185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2579915119181106603416123 3869872678771659905124185)
        ·
          refine ⟨2902404509078744928843139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3869872678771659905124185 2902404509078744928843139)
          ·
            refine ⟨4353606763618117393264709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2902404509078744928843139 4353606763618117393264709)
            ·
              refine ⟨816301268178397011237133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4353606763618117393264709 816301268178397011237133)
              ·
                refine ⟨306112975566898879213925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 816301268178397011237133 306112975566898879213925)
                ·
                  refine ⟨57396182918793539852611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 306112975566898879213925 57396182918793539852611)
                  ·
                    rfl

theorem cell20_125751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 4].length) (baseStart_125751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125751 prefixEnd_125751 := by exact prefixLift 125751
  have htrace : WordTrace (prefixWord ++ tailWord_125751) baseStart_125751 baseEnd_125751 := by
    simpa [prefixWord, tailWord_125751, baseEnd_125751] using wordTrace_append hprefix tailTrace_125751
  have hstable : (prefixWord ++ tailWord_125751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125751).length < 2 ^ (prefixWord ++ tailWord_125751).sum := by decide
  have hdescent : baseEnd_125751 < baseStart_125751 := by decide
  rcases family_descends (prefixWord ++ tailWord_125751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125754 : List Nat := [3, 1, 1, 1, 6, 2, 1, 5]
def baseStart_125754 : Nat := 118140960795 + 125754 * 2 ^ 59
def prefixEnd_125754 : Nat := 4983230072969 + 3 ^ 40 * 125754 * 2
def baseEnd_125754 : Nat := 19132517400179620917533

theorem tailTrace_125754 : CollatzResearch.WordTrace tailWord_125754 prefixEnd_125754 19132517400179620917533 := by
  unfold tailWord_125754
  simp only [CollatzResearch.WordTrace]
  refine ⟨1146656296605552479608079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3057750124281473278954877 1146656296605552479608079)
  ·
    refine ⟨1719984444908328719412119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1146656296605552479608079 1719984444908328719412119)
    ·
      refine ⟨2579976667362493079118179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1719984444908328719412119 2579976667362493079118179)
      ·
        refine ⟨3869965001043739618677269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2579976667362493079118179 3869965001043739618677269)
        ·
          refine ⟨181404609423925294625497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3869965001043739618677269 181404609423925294625497)
          ·
            refine ⟨136053457067943970969123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181404609423925294625497 136053457067943970969123)
            ·
              refine ⟨204080185601915956453685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136053457067943970969123 204080185601915956453685)
              ·
                refine ⟨19132517400179620917533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 204080185601915956453685 19132517400179620917533)
                ·
                  rfl

theorem cell20_125754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_125754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125754 prefixEnd_125754 := by exact prefixLift 125754
  have htrace : WordTrace (prefixWord ++ tailWord_125754) baseStart_125754 baseEnd_125754 := by
    simpa [prefixWord, tailWord_125754, baseEnd_125754] using wordTrace_append hprefix tailTrace_125754
  have hstable : (prefixWord ++ tailWord_125754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125754).length < 2 ^ (prefixWord ++ tailWord_125754).sum := by decide
  have hdescent : baseEnd_125754 < baseStart_125754 := by decide
  rcases family_descends (prefixWord ++ tailWord_125754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125764 : List Nat := [2, 3, 4, 2, 1, 1, 1, 2, 4]
def baseStart_125764 : Nat := 118140960795 + 125764 * 2 ^ 59
def prefixEnd_125764 : Nat := 4983230072969 + 3 ^ 40 * 125764 * 2
def baseEnd_125764 : Nat := 57402116473023272419225

theorem tailTrace_125764 : CollatzResearch.WordTrace tailWord_125764 prefixEnd_125764 57402116473023272419225 := by
  unfold tailWord_125764
  simp only [CollatzResearch.WordTrace]
  refine ⟨2293494958192990813148173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3057993277590654417530897 2293494958192990813148173)
  ·
    refine ⟨860060609322371554930565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2293494958192990813148173 860060609322371554930565)
    ·
      refine ⟨161261364247944666549481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 860060609322371554930565 161261364247944666549481)
      ·
        refine ⟨120946023185958499912111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161261364247944666549481 120946023185958499912111)
        ·
          refine ⟨181419034778937749868167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120946023185958499912111 181419034778937749868167)
          ·
            refine ⟨272128552168406624802251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181419034778937749868167 272128552168406624802251)
            ·
              refine ⟨408192828252609937203377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272128552168406624802251 408192828252609937203377)
              ·
                refine ⟨306144621189457452902533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 408192828252609937203377 306144621189457452902533)
                ·
                  refine ⟨57402116473023272419225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 306144621189457452902533 57402116473023272419225)
                  ·
                    rfl

theorem cell20_125764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_125764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125764 prefixEnd_125764 := by exact prefixLift 125764
  have htrace : WordTrace (prefixWord ++ tailWord_125764) baseStart_125764 baseEnd_125764 := by
    simpa [prefixWord, tailWord_125764, baseEnd_125764] using wordTrace_append hprefix tailTrace_125764
  have hstable : (prefixWord ++ tailWord_125764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125764).length < 2 ^ (prefixWord ++ tailWord_125764).sum := by decide
  have hdescent : baseEnd_125764 < baseStart_125764 := by decide
  rcases family_descends (prefixWord ++ tailWord_125764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125785 : List Nat := [1, 2, 1, 2, 2, 5, 2, 3, 2]
def baseStart_125785 : Nat := 118140960795 + 125785 * 2 ^ 59
def prefixEnd_125785 : Nat := 4983230072969 + 3 ^ 40 * 125785 * 2
def baseEnd_125785 : Nat := 57411701445240532719139

theorem tailTrace_125785 : CollatzResearch.WordTrace tailWord_125785 prefixEnd_125785 57411701445240532719139 := by
  unfold tailWord_125785
  simp only [CollatzResearch.WordTrace]
  refine ⟨4587755849309902212810809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3058503899539934808540539 4587755849309902212810809)
  ·
    refine ⟨3440816886982426659608107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4587755849309902212810809 3440816886982426659608107)
    ·
      refine ⟨5161225330473639989412161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3440816886982426659608107 5161225330473639989412161)
      ·
        refine ⟨3870918997855229992059121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5161225330473639989412161 3870918997855229992059121)
        ·
          refine ⟨2903189248391422494044341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3870918997855229992059121 2903189248391422494044341)
          ·
            refine ⟨272173992036695858816657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2903189248391422494044341 272173992036695858816657)
            ·
              refine ⟨204130494027521894112493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272173992036695858816657 204130494027521894112493)
              ·
                refine ⟨76548935260320710292185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204130494027521894112493 76548935260320710292185)
                ·
                  refine ⟨57411701445240532719139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76548935260320710292185 57411701445240532719139)
                  ·
                    rfl

theorem cell20_125785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 3, 2].length) (baseStart_125785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125785 prefixEnd_125785 := by exact prefixLift 125785
  have htrace : WordTrace (prefixWord ++ tailWord_125785) baseStart_125785 baseEnd_125785 := by
    simpa [prefixWord, tailWord_125785, baseEnd_125785] using wordTrace_append hprefix tailTrace_125785
  have hstable : (prefixWord ++ tailWord_125785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125785).length < 2 ^ (prefixWord ++ tailWord_125785).sum := by decide
  have hdescent : baseEnd_125785 < baseStart_125785 := by decide
  rcases family_descends (prefixWord ++ tailWord_125785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125799 : List Nat := [1, 1, 5, 1, 2, 2, 3, 2, 3]
def baseStart_125799 : Nat := 118140960795 + 125799 * 2 ^ 59
def prefixEnd_125799 : Nat := 4983230072969 + 3 ^ 40 * 125799 * 2
def baseEnd_125799 : Nat := 57418091426718706252415

theorem tailTrace_125799 : CollatzResearch.WordTrace tailWord_125799 prefixEnd_125799 57418091426718706252415 := by
  unfold tailWord_125799
  simp only [CollatzResearch.WordTrace]
  refine ⟨4588266471259182603820451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3058844314172788402546967 4588266471259182603820451)
  ·
    refine ⟨6882399706888773905730677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4588266471259182603820451 6882399706888773905730677)
    ·
      refine ⟨645224972520822553662251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6882399706888773905730677 645224972520822553662251)
      ·
        refine ⟨967837458781233830493377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645224972520822553662251 967837458781233830493377)
        ·
          refine ⟨725878094085925372870033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 967837458781233830493377 725878094085925372870033)
          ·
            refine ⟨544408570564444029652525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 725878094085925372870033 544408570564444029652525)
            ·
              refine ⟨204153213961666511119697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 544408570564444029652525 204153213961666511119697)
              ·
                refine ⟨153114910471249883339773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204153213961666511119697 153114910471249883339773)
                ·
                  refine ⟨57418091426718706252415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153114910471249883339773 57418091426718706252415)
                  ·
                    rfl

theorem cell20_125799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 3].length) (baseStart_125799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125799 prefixEnd_125799 := by exact prefixLift 125799
  have htrace : WordTrace (prefixWord ++ tailWord_125799) baseStart_125799 baseEnd_125799 := by
    simpa [prefixWord, tailWord_125799, baseEnd_125799] using wordTrace_append hprefix tailTrace_125799
  have hstable : (prefixWord ++ tailWord_125799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125799).length < 2 ^ (prefixWord ++ tailWord_125799).sum := by decide
  have hdescent : baseEnd_125799 < baseStart_125799 := by decide
  rcases family_descends (prefixWord ++ tailWord_125799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125820 : List Nat := [2, 2, 2, 1, 1, 1, 1, 7, 3]
def baseStart_125820 : Nat := 118140960795 + 125820 * 2 ^ 59
def prefixEnd_125820 : Nat := 4983230072969 + 3 ^ 40 * 125820 * 2
def baseEnd_125820 : Nat := 57427676398935966552329

theorem tailTrace_125820 : CollatzResearch.WordTrace tailWord_125820 prefixEnd_125820 57427676398935966552329 := by
  unfold tailWord_125820
  simp only [CollatzResearch.WordTrace]
  refine ⟨2294516202091551595167457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3059354936122068793556609 2294516202091551595167457)
  ·
    refine ⟨1720887151568663696375593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2294516202091551595167457 1720887151568663696375593)
    ·
      refine ⟨1290665363676497772281695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1720887151568663696375593 1290665363676497772281695)
      ·
        refine ⟨1935998045514746658422543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1290665363676497772281695 1935998045514746658422543)
        ·
          refine ⟨2903997068272119987633815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1935998045514746658422543 2903997068272119987633815)
          ·
            refine ⟨4355995602408179981450723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2903997068272119987633815 4355995602408179981450723)
            ·
              refine ⟨6533993403612269972176085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4355995602408179981450723 6533993403612269972176085)
              ·
                refine ⟨153140470397162577472877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6533993403612269972176085 153140470397162577472877)
                ·
                  refine ⟨57427676398935966552329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153140470397162577472877 57427676398935966552329)
                  ·
                    rfl

theorem cell20_125820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_125820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125820 prefixEnd_125820 := by exact prefixLift 125820
  have htrace : WordTrace (prefixWord ++ tailWord_125820) baseStart_125820 baseEnd_125820 := by
    simpa [prefixWord, tailWord_125820, baseEnd_125820] using wordTrace_append hprefix tailTrace_125820
  have hstable : (prefixWord ++ tailWord_125820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125820).length < 2 ^ (prefixWord ++ tailWord_125820).sum := by decide
  have hdescent : baseEnd_125820 < baseStart_125820 := by decide
  rcases family_descends (prefixWord ++ tailWord_125820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125827 : List Nat := [1, 1, 1, 3, 4, 1, 1, 4, 4]
def baseStart_125827 : Nat := 118140960795 + 125827 * 2 ^ 59
def prefixEnd_125827 : Nat := 4983230072969 + 3 ^ 40 * 125827 * 2
def baseEnd_125827 : Nat := 57430871389675053318967

theorem tailTrace_125827 : CollatzResearch.WordTrace tailWord_125827 prefixEnd_125827 57430871389675053318967 := by
  unfold tailWord_125827
  simp only [CollatzResearch.WordTrace]
  refine ⟨4589287715157743385839735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3059525143438495590559823 4589287715157743385839735)
  ·
    refine ⟨6883931572736615078759603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4589287715157743385839735 6883931572736615078759603)
    ·
      refine ⟨10325897359104922618139405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6883931572736615078759603 10325897359104922618139405)
      ·
        refine ⟨3872211509664345981802277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10325897359104922618139405 3872211509664345981802277)
        ·
          refine ⟨726039658062064871587927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3872211509664345981802277 726039658062064871587927)
          ·
            refine ⟨1089059487093097307381891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726039658062064871587927 1089059487093097307381891)
            ·
              refine ⟨1633589230639645961072837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1089059487093097307381891 1633589230639645961072837)
              ·
                refine ⟨306297980744933617701157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1633589230639645961072837 306297980744933617701157)
                ·
                  refine ⟨57430871389675053318967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 306297980744933617701157 57430871389675053318967)
                  ·
                    rfl

theorem cell20_125827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 4].length) (baseStart_125827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125827 prefixEnd_125827 := by exact prefixLift 125827
  have htrace : WordTrace (prefixWord ++ tailWord_125827) baseStart_125827 baseEnd_125827 := by
    simpa [prefixWord, tailWord_125827, baseEnd_125827] using wordTrace_append hprefix tailTrace_125827
  have hstable : (prefixWord ++ tailWord_125827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125827).length < 2 ^ (prefixWord ++ tailWord_125827).sum := by decide
  have hdescent : baseEnd_125827 < baseStart_125827 := by decide
  rcases family_descends (prefixWord ++ tailWord_125827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125913 : List Nat := [1, 2, 1, 2, 5, 2, 2, 2, 3]
def baseStart_125913 : Nat := 118140960795 + 125913 * 2 ^ 59
def prefixEnd_125913 : Nat := 4983230072969 + 3 ^ 40 * 125913 * 2
def baseEnd_125913 : Nat := 57470124133040976451949

theorem tailTrace_125913 : CollatzResearch.WordTrace tailWord_125913 prefixEnd_125913 57470124133040976451949 := by
  unfold tailWord_125913
  simp only [CollatzResearch.WordTrace]
  refine ⟨4592424392846180073470393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3061616261897453382313595 4592424392846180073470393)
  ·
    refine ⟨3444318294634635055102795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4592424392846180073470393 3444318294634635055102795)
    ·
      refine ⟨5166477441951952582654193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3444318294634635055102795 5166477441951952582654193)
      ·
        refine ⟨3874858081463964436990645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5166477441951952582654193 3874858081463964436990645)
        ·
          refine ⟨363267945137246665967873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3874858081463964436990645 363267945137246665967873)
          ·
            refine ⟨272450958852934999475905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363267945137246665967873 272450958852934999475905)
            ·
              refine ⟨204338219139701249606929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272450958852934999475905 204338219139701249606929)
              ·
                refine ⟨153253664354775937205197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204338219139701249606929 153253664354775937205197)
                ·
                  refine ⟨57470124133040976451949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153253664354775937205197 57470124133040976451949)
                  ·
                    rfl

theorem cell20_125913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 3].length) (baseStart_125913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125913 prefixEnd_125913 := by exact prefixLift 125913
  have htrace : WordTrace (prefixWord ++ tailWord_125913) baseStart_125913 baseEnd_125913 := by
    simpa [prefixWord, tailWord_125913, baseEnd_125913] using wordTrace_append hprefix tailTrace_125913
  have hstable : (prefixWord ++ tailWord_125913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125913).length < 2 ^ (prefixWord ++ tailWord_125913).sum := by decide
  have hdescent : baseEnd_125913 < baseStart_125913 := by decide
  rcases family_descends (prefixWord ++ tailWord_125913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125927 : List Nat := [1, 1, 5, 2, 2, 1, 3, 5]
def baseStart_125927 : Nat := 118140960795 + 125927 * 2 ^ 59
def prefixEnd_125927 : Nat := 4983230072969 + 3 ^ 40 * 125927 * 2
def baseEnd_125927 : Nat := 19158838038173049995075

theorem tailTrace_125927 : CollatzResearch.WordTrace tailWord_125927 prefixEnd_125927 19158838038173049995075 := by
  unfold tailWord_125927
  simp only [CollatzResearch.WordTrace]
  refine ⟨4592935014795460464480035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3061956676530306976320023 4592935014795460464480035)
  ·
    refine ⟨6889402522193190696720053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4592935014795460464480035 6889402522193190696720053)
    ·
      refine ⟨645881486455611627817505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6889402522193190696720053 645881486455611627817505)
      ·
        refine ⟨484411114841708720863129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 645881486455611627817505 484411114841708720863129)
        ·
          refine ⟨363308336131281540647347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484411114841708720863129 363308336131281540647347)
          ·
            refine ⟨544962504196922310971021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363308336131281540647347 544962504196922310971021)
            ·
              refine ⟨204360939073845866614133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 544962504196922310971021 204360939073845866614133)
              ·
                refine ⟨19158838038173049995075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 204360939073845866614133 19158838038173049995075)
                ·
                  rfl

theorem cell20_125927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 5].length) (baseStart_125927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125927 prefixEnd_125927 := by exact prefixLift 125927
  have htrace : WordTrace (prefixWord ++ tailWord_125927) baseStart_125927 baseEnd_125927 := by
    simpa [prefixWord, tailWord_125927, baseEnd_125927] using wordTrace_append hprefix tailTrace_125927
  have hstable : (prefixWord ++ tailWord_125927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125927).length < 2 ^ (prefixWord ++ tailWord_125927).sum := by decide
  have hdescent : baseEnd_125927 < baseStart_125927 := by decide
  rcases family_descends (prefixWord ++ tailWord_125927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125975 : List Nat := [1, 1, 3, 5, 1, 1, 2, 4, 2]
def baseStart_125975 : Nat := 118140960795 + 125975 * 2 ^ 59
def prefixEnd_125975 : Nat := 4983230072969 + 3 ^ 40 * 125975 * 2
def baseEnd_125975 : Nat := 57498422622444316385029

theorem tailTrace_125975 : CollatzResearch.WordTrace tailWord_125975 prefixEnd_125975 57498422622444316385029 := by
  unfold tailWord_125975
  simp only [CollatzResearch.WordTrace]
  refine ⟨4594685718621564662227379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3063123812414376441484919 4594685718621564662227379)
  ·
    refine ⟨6892028577932346993341069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4594685718621564662227379 6892028577932346993341069)
    ·
      refine ⟨2584510716724630122502901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6892028577932346993341069 2584510716724630122502901)
      ·
        refine ⟨242297879692934073984647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2584510716724630122502901 242297879692934073984647)
        ·
          refine ⟨363446819539401110976971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242297879692934073984647 363446819539401110976971)
          ·
            refine ⟨545170229309101666465457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363446819539401110976971 545170229309101666465457)
            ·
              refine ⟨408877671981826249849093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 545170229309101666465457 408877671981826249849093)
              ·
                refine ⟨76664563496592421846705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 408877671981826249849093 76664563496592421846705)
                ·
                  refine ⟨57498422622444316385029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76664563496592421846705 57498422622444316385029)
                  ·
                    rfl

theorem cell20_125975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 4, 2].length) (baseStart_125975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125975 prefixEnd_125975 := by exact prefixLift 125975
  have htrace : WordTrace (prefixWord ++ tailWord_125975) baseStart_125975 baseEnd_125975 := by
    simpa [prefixWord, tailWord_125975, baseEnd_125975] using wordTrace_append hprefix tailTrace_125975
  have hstable : (prefixWord ++ tailWord_125975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125975).length < 2 ^ (prefixWord ++ tailWord_125975).sum := by decide
  have hdescent : baseEnd_125975 < baseStart_125975 := by decide
  rcases family_descends (prefixWord ++ tailWord_125975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125989 : List Nat := [1, 3, 1, 2, 2, 2, 5, 1, 3]
def baseStart_125989 : Nat := 118140960795 + 125989 * 2 ^ 59
def prefixEnd_125989 : Nat := 4983230072969 + 3 ^ 40 * 125989 * 2
def baseEnd_125989 : Nat := 57504812603922489918305

theorem tailTrace_125989 : CollatzResearch.WordTrace tailWord_125989 prefixEnd_125989 57504812603922489918305 := by
  unfold tailWord_125989
  simp only [CollatzResearch.WordTrace]
  refine ⟨4595196340570845053237021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3063464227047230035491347 4595196340570845053237021)
  ·
    refine ⟨1723198627714066894963883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4595196340570845053237021 1723198627714066894963883)
    ·
      refine ⟨2584797941571100342445825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1723198627714066894963883 2584797941571100342445825)
      ·
        refine ⟨1938598456178325256834369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2584797941571100342445825 1938598456178325256834369)
        ·
          refine ⟨1453948842133743942625777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1938598456178325256834369 1453948842133743942625777)
          ·
            refine ⟨1090461631600307956969333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1453948842133743942625777 1090461631600307956969333)
            ·
              refine ⟨102230777962528870965875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1090461631600307956969333 102230777962528870965875)
              ·
                refine ⟨153346166943793306448813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102230777962528870965875 153346166943793306448813)
                ·
                  refine ⟨57504812603922489918305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153346166943793306448813 57504812603922489918305)
                  ·
                    rfl

theorem cell20_125989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_125989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_125989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_125989 prefixEnd_125989 := by exact prefixLift 125989
  have htrace : WordTrace (prefixWord ++ tailWord_125989) baseStart_125989 baseEnd_125989 := by
    simpa [prefixWord, tailWord_125989, baseEnd_125989] using wordTrace_append hprefix tailTrace_125989
  have hstable : (prefixWord ++ tailWord_125989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125989).length < 2 ^ (prefixWord ++ tailWord_125989).sum := by decide
  have hdescent : baseEnd_125989 < baseStart_125989 := by decide
  rcases family_descends (prefixWord ++ tailWord_125989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126013 : List Nat := [1, 4, 1, 3, 1, 2, 3, 3, 2]
def baseStart_126013 : Nat := 118140960795 + 126013 * 2 ^ 59
def prefixEnd_126013 : Nat := 4983230072969 + 3 ^ 40 * 126013 * 2
def baseEnd_126013 : Nat := 57515766857885073118207

theorem tailTrace_126013 : CollatzResearch.WordTrace tailWord_126013 prefixEnd_126013 57515766857885073118207 := by
  unfold tailWord_126013
  simp only [CollatzResearch.WordTrace]
  refine ⟨4596071692483897152110693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3064047794989264768073795 4596071692483897152110693)
  ·
    refine ⟨861763442340730716020755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4596071692483897152110693 861763442340730716020755)
    ·
      refine ⟨1292645163511096074031133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 861763442340730716020755 1292645163511096074031133)
      ·
        refine ⟨484741936316661027761675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1292645163511096074031133 484741936316661027761675)
        ·
          refine ⟨727112904474991541642513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484741936316661027761675 727112904474991541642513)
          ·
            refine ⟨545334678356243656231885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 727112904474991541642513 545334678356243656231885)
            ·
              refine ⟨204500504383591371086957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 545334678356243656231885 204500504383591371086957)
              ·
                refine ⟨76687689143846764157609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204500504383591371086957 76687689143846764157609)
                ·
                  refine ⟨57515766857885073118207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76687689143846764157609 57515766857885073118207)
                  ·
                    rfl

theorem cell20_126013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_126013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126013 prefixEnd_126013 := by exact prefixLift 126013
  have htrace : WordTrace (prefixWord ++ tailWord_126013) baseStart_126013 baseEnd_126013 := by
    simpa [prefixWord, tailWord_126013, baseEnd_126013] using wordTrace_append hprefix tailTrace_126013
  have hstable : (prefixWord ++ tailWord_126013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126013).length < 2 ^ (prefixWord ++ tailWord_126013).sum := by decide
  have hdescent : baseEnd_126013 < baseStart_126013 := by decide
  rcases family_descends (prefixWord ++ tailWord_126013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126034 : List Nat := [3, 2, 2, 1, 3, 1, 3, 1, 4]
def baseStart_126034 : Nat := 118140960795 + 126034 * 2 ^ 59
def prefixEnd_126034 : Nat := 4983230072969 + 3 ^ 40 * 126034 * 2
def baseEnd_126034 : Nat := 57525351830102333418121

theorem tailTrace_126034 : CollatzResearch.WordTrace tailWord_126034 prefixEnd_126034 57525351830102333418121 := by
  unfold tailWord_126034
  simp only [CollatzResearch.WordTrace]
  refine ⟨1149209406351954434656289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3064558416938545159083437 1149209406351954434656289)
  ·
    refine ⟨861907054763965825992217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1149209406351954434656289 861907054763965825992217)
    ·
      refine ⟨646430291072974369494163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 861907054763965825992217 646430291072974369494163)
      ·
        refine ⟨969645436609461554241245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646430291072974369494163 969645436609461554241245)
        ·
          refine ⟨363617038728548082840467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 969645436609461554241245 363617038728548082840467)
          ·
            refine ⟨545425558092822124260701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363617038728548082840467 545425558092822124260701)
            ·
              refine ⟨204534584284808296597763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 545425558092822124260701 204534584284808296597763)
              ·
                refine ⟨306801876427212444896645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204534584284808296597763 306801876427212444896645)
                ·
                  refine ⟨57525351830102333418121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 306801876427212444896645 57525351830102333418121)
                  ·
                    rfl

theorem cell20_126034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_126034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126034 prefixEnd_126034 := by exact prefixLift 126034
  have htrace : WordTrace (prefixWord ++ tailWord_126034) baseStart_126034 baseEnd_126034 := by
    simpa [prefixWord, tailWord_126034, baseEnd_126034] using wordTrace_append hprefix tailTrace_126034
  have hstable : (prefixWord ++ tailWord_126034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126034).length < 2 ^ (prefixWord ++ tailWord_126034).sum := by decide
  have hdescent : baseEnd_126034 < baseStart_126034 := by decide
  rcases family_descends (prefixWord ++ tailWord_126034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126048 : List Nat := [2, 1, 1, 3, 2, 2, 3, 3, 3]
def baseStart_126048 : Nat := 118140960795 + 126048 * 2 ^ 59
def prefixEnd_126048 : Nat := 4983230072969 + 3 ^ 40 * 126048 * 2
def baseEnd_126048 : Nat := 57531741811580506951397

theorem tailTrace_126048 : CollatzResearch.WordTrace tailWord_126048 prefixEnd_126048 57531741811580506951397 := by
  unfold tailWord_126048
  simp only [CollatzResearch.WordTrace]
  refine ⟨2298674123678549064817399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3064898831571398753089865 2298674123678549064817399)
  ·
    refine ⟨3448011185517823597226099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2298674123678549064817399 3448011185517823597226099)
    ·
      refine ⟨5172016778276735395839149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3448011185517823597226099 5172016778276735395839149)
      ·
        refine ⟨1939506291853775773439681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5172016778276735395839149 1939506291853775773439681)
        ·
          refine ⟨1454629718890331830079761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1939506291853775773439681 1454629718890331830079761)
          ·
            refine ⟨1090972289167748872559821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1454629718890331830079761 1090972289167748872559821)
            ·
              refine ⟨409114608437905827209933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1090972289167748872559821 409114608437905827209933)
              ·
                refine ⟨153417978164214685203725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 409114608437905827209933 153417978164214685203725)
                ·
                  refine ⟨57531741811580506951397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153417978164214685203725 57531741811580506951397)
                  ·
                    rfl

theorem cell20_126048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 3].length) (baseStart_126048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126048 prefixEnd_126048 := by exact prefixLift 126048
  have htrace : WordTrace (prefixWord ++ tailWord_126048) baseStart_126048 baseEnd_126048 := by
    simpa [prefixWord, tailWord_126048, baseEnd_126048] using wordTrace_append hprefix tailTrace_126048
  have hstable : (prefixWord ++ tailWord_126048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126048).length < 2 ^ (prefixWord ++ tailWord_126048).sum := by decide
  have hdescent : baseEnd_126048 < baseStart_126048 := by decide
  rcases family_descends (prefixWord ++ tailWord_126048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126078 : List Nat := [4, 2, 4, 1, 1, 1, 2, 2, 3]
def baseStart_126078 : Nat := 118140960795 + 126078 * 2 ^ 59
def prefixEnd_126078 : Nat := 4983230072969 + 3 ^ 40 * 126078 * 2
def baseEnd_126078 : Nat := 57545434629033735951275

theorem tailTrace_126078 : CollatzResearch.WordTrace tailWord_126078 prefixEnd_126078 57545434629033735951275 := by
  unfold tailWord_126078
  simp only [CollatzResearch.WordTrace]
  refine ⟨574805304656051656653361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3065628291498942168817925 574805304656051656653361)
  ·
    refine ⟨431103978492038742490021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 574805304656051656653361 431103978492038742490021)
    ·
      refine ⟨80831995967257264216879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 431103978492038742490021 80831995967257264216879)
      ·
        refine ⟨121247993950885896325319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80831995967257264216879 121247993950885896325319)
        ·
          refine ⟨181871990926328844487979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121247993950885896325319 181871990926328844487979)
          ·
            refine ⟨272807986389493266731969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181871990926328844487979 272807986389493266731969)
            ·
              refine ⟨204605989792119950048977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272807986389493266731969 204605989792119950048977)
              ·
                refine ⟨153454492344089962536733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204605989792119950048977 153454492344089962536733)
                ·
                  refine ⟨57545434629033735951275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153454492344089962536733 57545434629033735951275)
                  ·
                    rfl

theorem cell20_126078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_126078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126078 prefixEnd_126078 := by exact prefixLift 126078
  have htrace : WordTrace (prefixWord ++ tailWord_126078) baseStart_126078 baseEnd_126078 := by
    simpa [prefixWord, tailWord_126078, baseEnd_126078] using wordTrace_append hprefix tailTrace_126078
  have hstable : (prefixWord ++ tailWord_126078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126078).length < 2 ^ (prefixWord ++ tailWord_126078).sum := by decide
  have hdescent : baseEnd_126078 < baseStart_126078 := by decide
  rcases family_descends (prefixWord ++ tailWord_126078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126085 : List Nat := [1, 3, 1, 1, 7, 1, 2, 2, 2]
def baseStart_126085 : Nat := 118140960795 + 126085 * 2 ^ 59
def prefixEnd_126085 : Nat := 4983230072969 + 3 ^ 40 * 126085 * 2
def baseEnd_126085 : Nat := 57548629619772822717913

theorem tailTrace_126085 : CollatzResearch.WordTrace tailWord_126085 prefixEnd_126085 57548629619772822717913 := by
  unfold tailWord_126085
  simp only [CollatzResearch.WordTrace]
  refine ⟨4598697748223053448731709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3065798498815368965821139 4598697748223053448731709)
  ·
    refine ⟨1724511655583645043274391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4598697748223053448731709 1724511655583645043274391)
    ·
      refine ⟨2586767483375467564911587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1724511655583645043274391 2586767483375467564911587)
      ·
        refine ⟨3880151225063201347367381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2586767483375467564911587 3880151225063201347367381)
        ·
          refine ⟨90941044337418781578923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 3880151225063201347367381 90941044337418781578923)
          ·
            refine ⟨136411566506128172368385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90941044337418781578923 136411566506128172368385)
            ·
              refine ⟨102308674879596129276289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136411566506128172368385 102308674879596129276289)
              ·
                refine ⟨76731506159697096957217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102308674879596129276289 76731506159697096957217)
                ·
                  refine ⟨57548629619772822717913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76731506159697096957217 57548629619772822717913)
                  ·
                    rfl

theorem cell20_126085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 2, 2].length) (baseStart_126085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126085 prefixEnd_126085 := by exact prefixLift 126085
  have htrace : WordTrace (prefixWord ++ tailWord_126085) baseStart_126085 baseEnd_126085 := by
    simpa [prefixWord, tailWord_126085, baseEnd_126085] using wordTrace_append hprefix tailTrace_126085
  have hstable : (prefixWord ++ tailWord_126085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126085).length < 2 ^ (prefixWord ++ tailWord_126085).sum := by decide
  have hdescent : baseEnd_126085 < baseStart_126085 := by decide
  rcases family_descends (prefixWord ++ tailWord_126085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126089 : List Nat := [1, 2, 1, 1, 4, 3, 4, 2, 2]
def baseStart_126089 : Nat := 118140960795 + 126089 * 2 ^ 59
def prefixEnd_126089 : Nat := 4983230072969 + 3 ^ 40 * 126089 * 2
def baseEnd_126089 : Nat := 57550455328766586584563

theorem tailTrace_126089 : CollatzResearch.WordTrace tailWord_126089 prefixEnd_126089 57550455328766586584563 := by
  unfold tailWord_126089
  simp only [CollatzResearch.WordTrace]
  refine ⟨4598843640208562131877321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3065895760139041421251547 4598843640208562131877321)
  ·
    refine ⟨3449132730156421598907991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4598843640208562131877321 3449132730156421598907991)
    ·
      refine ⟨5173699095234632398361987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3449132730156421598907991 5173699095234632398361987)
      ·
        refine ⟨7760548642851948597542981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5173699095234632398361987 7760548642851948597542981)
        ·
          refine ⟨1455102870534740362039309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7760548642851948597542981 1455102870534740362039309)
          ·
            refine ⟨545663576450527635764741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1455102870534740362039309 545663576450527635764741)
            ·
              refine ⟨102311920584473931705889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 545663576450527635764741 102311920584473931705889)
              ·
                refine ⟨76733940438355448779417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102311920584473931705889 76733940438355448779417)
                ·
                  refine ⟨57550455328766586584563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76733940438355448779417 57550455328766586584563)
                  ·
                    rfl

theorem cell20_126089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 2, 2].length) (baseStart_126089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126089 prefixEnd_126089 := by exact prefixLift 126089
  have htrace : WordTrace (prefixWord ++ tailWord_126089) baseStart_126089 baseEnd_126089 := by
    simpa [prefixWord, tailWord_126089, baseEnd_126089] using wordTrace_append hprefix tailTrace_126089
  have hstable : (prefixWord ++ tailWord_126089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126089).length < 2 ^ (prefixWord ++ tailWord_126089).sum := by decide
  have hdescent : baseEnd_126089 < baseStart_126089 := by decide
  rcases family_descends (prefixWord ++ tailWord_126089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126110 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 6]
def baseStart_126110 : Nat := 118140960795 + 126110 * 2 ^ 59
def prefixEnd_126110 : Nat := 4983230072969 + 3 ^ 40 * 126110 * 2
def baseEnd_126110 : Nat := 57560040300983846884477

theorem tailTrace_126110 : CollatzResearch.WordTrace tailWord_126110 prefixEnd_126110 57560040300983846884477 := by
  unfold tailWord_126110
  simp only [CollatzResearch.WordTrace]
  refine ⟨574951196641560339798973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3066406382088321812261189 574951196641560339798973)
  ·
    refine ⟨215606698740585127424615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 574951196641560339798973 215606698740585127424615)
    ·
      refine ⟨323410048110877691136923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215606698740585127424615 323410048110877691136923)
      ·
        refine ⟨485115072166316536705385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323410048110877691136923 485115072166316536705385)
        ·
          refine ⟨363836304124737402529039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485115072166316536705385 363836304124737402529039)
          ·
            refine ⟨545754456187106103793559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363836304124737402529039 545754456187106103793559)
            ·
              refine ⟨818631684280659155690339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545754456187106103793559 818631684280659155690339)
              ·
                refine ⟨1227947526420988733535509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 818631684280659155690339 1227947526420988733535509)
                ·
                  refine ⟨57560040300983846884477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1227947526420988733535509 57560040300983846884477)
                  ·
                    rfl

theorem cell20_126110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_126110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126110 prefixEnd_126110 := by exact prefixLift 126110
  have htrace : WordTrace (prefixWord ++ tailWord_126110) baseStart_126110 baseEnd_126110 := by
    simpa [prefixWord, tailWord_126110, baseEnd_126110] using wordTrace_append hprefix tailTrace_126110
  have hstable : (prefixWord ++ tailWord_126110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126110).length < 2 ^ (prefixWord ++ tailWord_126110).sum := by decide
  have hdescent : baseEnd_126110 < baseStart_126110 := by decide
  rcases family_descends (prefixWord ++ tailWord_126110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126117 : List Nat := [1, 3, 1, 2, 1, 5, 3, 4]
def baseStart_126117 : Nat := 118140960795 + 126117 * 2 ^ 59
def prefixEnd_126117 : Nat := 4983230072969 + 3 ^ 40 * 126117 * 2
def baseEnd_126117 : Nat := 19187745097240977883705

theorem tailTrace_126117 : CollatzResearch.WordTrace tailWord_126117 prefixEnd_126117 19187745097240977883705 := by
  unfold tailWord_126117
  simp only [CollatzResearch.WordTrace]
  refine ⟨4599864884107122913896605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3066576589404748609264403 4599864884107122913896605)
  ·
    refine ⟨1724949331540171092711227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4599864884107122913896605 1724949331540171092711227)
    ·
      refine ⟨2587423997310256639066841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1724949331540171092711227 2587423997310256639066841)
      ·
        refine ⟨1940567997982692479300131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2587423997310256639066841 1940567997982692479300131)
        ·
          refine ⟨2910851996974038718950197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1940567997982692479300131 2910851996974038718950197)
          ·
            refine ⟨272892374716316129901581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2910851996974038718950197 272892374716316129901581)
            ·
              refine ⟨102334640518618548713093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272892374716316129901581 102334640518618548713093)
              ·
                refine ⟨19187745097240977883705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102334640518618548713093 19187745097240977883705)
                ·
                  rfl

theorem cell20_126117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 4].length) (baseStart_126117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126117 prefixEnd_126117 := by exact prefixLift 126117
  have htrace : WordTrace (prefixWord ++ tailWord_126117) baseStart_126117 baseEnd_126117 := by
    simpa [prefixWord, tailWord_126117, baseEnd_126117] using wordTrace_append hprefix tailTrace_126117
  have hstable : (prefixWord ++ tailWord_126117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126117).length < 2 ^ (prefixWord ++ tailWord_126117).sum := by decide
  have hdescent : baseEnd_126117 < baseStart_126117 := by decide
  rcases family_descends (prefixWord ++ tailWord_126117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126158 : List Nat := [4, 1, 1, 1, 5, 1, 3, 1, 3]
def baseStart_126158 : Nat := 118140960795 + 126158 * 2 ^ 59
def prefixEnd_126158 : Nat := 4983230072969 + 3 ^ 40 * 126158 * 2
def baseEnd_126158 : Nat := 57581948808909013284281

theorem tailTrace_126158 : CollatzResearch.WordTrace tailWord_126158 prefixEnd_126158 57581948808909013284281 := by
  unfold tailWord_126158
  simp only [CollatzResearch.WordTrace]
  refine ⟨575170034619823364517391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3067573517972391277426085 575170034619823364517391)
  ·
    refine ⟨862755051929735046776087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 575170034619823364517391 862755051929735046776087)
    ·
      refine ⟨1294132577894602570164131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 862755051929735046776087 1294132577894602570164131)
      ·
        refine ⟨1941198866841903855246197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1294132577894602570164131 1941198866841903855246197)
        ·
          refine ⟨181987393766428486429331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1941198866841903855246197 181987393766428486429331)
          ·
            refine ⟨272981090649642729643997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181987393766428486429331 272981090649642729643997)
            ·
              refine ⟨102367908993616023616499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272981090649642729643997 102367908993616023616499)
              ·
                refine ⟨153551863490424035424749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102367908993616023616499 153551863490424035424749)
                ·
                  refine ⟨57581948808909013284281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153551863490424035424749 57581948808909013284281)
                  ·
                    rfl

theorem cell20_126158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_126158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126158 prefixEnd_126158 := by exact prefixLift 126158
  have htrace : WordTrace (prefixWord ++ tailWord_126158) baseStart_126158 baseEnd_126158 := by
    simpa [prefixWord, tailWord_126158, baseEnd_126158] using wordTrace_append hprefix tailTrace_126158
  have hstable : (prefixWord ++ tailWord_126158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126158).length < 2 ^ (prefixWord ++ tailWord_126158).sum := by decide
  have hdescent : baseEnd_126158 < baseStart_126158 := by decide
  rcases family_descends (prefixWord ++ tailWord_126158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126176 : List Nat := [2, 1, 1, 3, 1, 5, 1, 6]
def baseStart_126176 : Nat := 118140960795 + 126176 * 2 ^ 59
def prefixEnd_126176 : Nat := 4983230072969 + 3 ^ 40 * 126176 * 2
def baseEnd_126176 : Nat := 19196721499793650228069

theorem tailTrace_126176 : CollatzResearch.WordTrace tailWord_126176 prefixEnd_126176 19196721499793650228069 := by
  unfold tailWord_126176
  simp only [CollatzResearch.WordTrace]
  refine ⟨2301008395446687995147191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3068011193928917326862921 2301008395446687995147191)
  ·
    refine ⟨3451512593170031992720787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2301008395446687995147191 3451512593170031992720787)
    ·
      refine ⟨5177268889755047989081181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3451512593170031992720787 5177268889755047989081181)
      ·
        refine ⟨1941475833658142995905443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5177268889755047989081181 1941475833658142995905443)
        ·
          refine ⟨2912213750487214493858165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1941475833658142995905443 2912213750487214493858165)
          ·
            refine ⟨273020039108176358799203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2912213750487214493858165 273020039108176358799203)
            ·
              refine ⟨409530058662264538198805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273020039108176358799203 409530058662264538198805)
              ·
                refine ⟨19196721499793650228069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 409530058662264538198805 19196721499793650228069)
                ·
                  rfl

theorem cell20_126176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 6].length) (baseStart_126176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126176 prefixEnd_126176 := by exact prefixLift 126176
  have htrace : WordTrace (prefixWord ++ tailWord_126176) baseStart_126176 baseEnd_126176 := by
    simpa [prefixWord, tailWord_126176, baseEnd_126176] using wordTrace_append hprefix tailTrace_126176
  have hstable : (prefixWord ++ tailWord_126176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126176).length < 2 ^ (prefixWord ++ tailWord_126176).sum := by decide
  have hdescent : baseEnd_126176 < baseStart_126176 := by decide
  rcases family_descends (prefixWord ++ tailWord_126176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126207 : List Nat := [1, 1, 2, 2, 1, 5, 3, 1, 4]
def baseStart_126207 : Nat := 118140960795 + 126207 * 2 ^ 59
def prefixEnd_126207 : Nat := 4983230072969 + 3 ^ 40 * 126207 * 2
def baseEnd_126207 : Nat := 57604313744082620650747

theorem tailTrace_126207 : CollatzResearch.WordTrace tailWord_126207 prefixEnd_126207 57604313744082620650747 := by
  unfold tailWord_126207
  simp only [CollatzResearch.WordTrace]
  refine ⟨4603147453781068284672875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3068764969187378856448583 4603147453781068284672875)
  ·
    refine ⟨6904721180671602427009313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4603147453781068284672875 6904721180671602427009313)
    ·
      refine ⟨5178540885503701820256985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6904721180671602427009313 5178540885503701820256985)
      ·
        refine ⟨3883905664127776365192739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5178540885503701820256985 3883905664127776365192739)
        ·
          refine ⟨5825858496191664547789109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3883905664127776365192739 5825858496191664547789109)
          ·
            refine ⟨546174234017968551355229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5825858496191664547789109 546174234017968551355229)
            ·
              refine ⟨204815337756738206758211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 546174234017968551355229 204815337756738206758211)
              ·
                refine ⟨307223006635107310137317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204815337756738206758211 307223006635107310137317)
                ·
                  refine ⟨57604313744082620650747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 307223006635107310137317 57604313744082620650747)
                  ·
                    rfl

theorem cell20_126207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 4].length) (baseStart_126207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126207 prefixEnd_126207 := by exact prefixLift 126207
  have htrace : WordTrace (prefixWord ++ tailWord_126207) baseStart_126207 baseEnd_126207 := by
    simpa [prefixWord, tailWord_126207, baseEnd_126207] using wordTrace_append hprefix tailTrace_126207
  have hstable : (prefixWord ++ tailWord_126207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126207).length < 2 ^ (prefixWord ++ tailWord_126207).sum := by decide
  have hdescent : baseEnd_126207 < baseStart_126207 := by decide
  rcases family_descends (prefixWord ++ tailWord_126207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126210 : List Nat := [3, 4, 1, 1, 3, 1, 2, 5]
def baseStart_126210 : Nat := 118140960795 + 126210 * 2 ^ 59
def prefixEnd_126210 : Nat := 4983230072969 + 3 ^ 40 * 126210 * 2
def baseEnd_126210 : Nat := 19201894341942647850245

theorem tailTrace_126210 : CollatzResearch.WordTrace tailWord_126210 prefixEnd_126210 19201894341942647850245 := by
  unfold tailWord_126210
  simp only [CollatzResearch.WordTrace]
  refine ⟨1150814218192549949258021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3068837915180133198021389 1150814218192549949258021)
  ·
    refine ⟨215777665911103115485879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1150814218192549949258021 215777665911103115485879)
    ·
      refine ⟨323666498866654673228819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215777665911103115485879 323666498866654673228819)
      ·
        refine ⟨485499748299982009843229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323666498866654673228819 485499748299982009843229)
        ·
          refine ⟨182062405612493253691211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 485499748299982009843229 182062405612493253691211)
          ·
            refine ⟨273093608418739880536817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182062405612493253691211 273093608418739880536817)
            ·
              refine ⟨204820206314054910402613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273093608418739880536817 204820206314054910402613)
              ·
                refine ⟨19201894341942647850245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 204820206314054910402613 19201894341942647850245)
                ·
                  rfl

theorem cell20_126210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_126210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126210 prefixEnd_126210 := by exact prefixLift 126210
  have htrace : WordTrace (prefixWord ++ tailWord_126210) baseStart_126210 baseEnd_126210 := by
    simpa [prefixWord, tailWord_126210, baseEnd_126210] using wordTrace_append hprefix tailTrace_126210
  have hstable : (prefixWord ++ tailWord_126210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126210).length < 2 ^ (prefixWord ++ tailWord_126210).sum := by decide
  have hdescent : baseEnd_126210 < baseStart_126210 := by decide
  rcases family_descends (prefixWord ++ tailWord_126210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126258 : List Nat := [3, 2, 1, 1, 4, 3, 2, 2, 2]
def baseStart_126258 : Nat := 118140960795 + 126258 * 2 ^ 59
def prefixEnd_126258 : Nat := 4983230072969 + 3 ^ 40 * 126258 * 2
def baseEnd_126258 : Nat := 57627591533753109950539

theorem tailTrace_126258 : CollatzResearch.WordTrace tailWord_126258 prefixEnd_126258 57627591533753109950539 := by
  unfold tailWord_126258
  simp only [CollatzResearch.WordTrace]
  refine ⟨1151251894149075998694857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3070005051064202663186285 1151251894149075998694857)
  ·
    refine ⟨863438920611806999021143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1151251894149075998694857 863438920611806999021143)
    ·
      refine ⟨1295158380917710498531715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 863438920611806999021143 1295158380917710498531715)
      ·
        refine ⟨1942737571376565747797573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1295158380917710498531715 1942737571376565747797573)
        ·
          refine ⟨364263294633106077712045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1942737571376565747797573 364263294633106077712045)
          ·
            refine ⟨136598735487414779142017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 364263294633106077712045 136598735487414779142017)
            ·
              refine ⟨102449051615561084356513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136598735487414779142017 102449051615561084356513)
              ·
                refine ⟨76836788711670813267385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102449051615561084356513 76836788711670813267385)
                ·
                  refine ⟨57627591533753109950539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76836788711670813267385 57627591533753109950539)
                  ·
                    rfl

theorem cell20_126258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_126258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126258 prefixEnd_126258 := by exact prefixLift 126258
  have htrace : WordTrace (prefixWord ++ tailWord_126258) baseStart_126258 baseEnd_126258 := by
    simpa [prefixWord, tailWord_126258, baseEnd_126258] using wordTrace_append hprefix tailTrace_126258
  have hstable : (prefixWord ++ tailWord_126258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126258).length < 2 ^ (prefixWord ++ tailWord_126258).sum := by decide
  have hdescent : baseEnd_126258 < baseStart_126258 := by decide
  rcases family_descends (prefixWord ++ tailWord_126258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126425 : List Nat := [1, 2, 1, 2, 4, 10]
def baseStart_126425 : Nat := 118140960795 + 126425 * 2 ^ 59
def prefixEnd_126425 : Nat := 4983230072969 + 3 ^ 40 * 126425 * 2
def baseEnd_126425 : Nat := 2137178329046027829007

theorem tailTrace_126425 : CollatzResearch.WordTrace tailWord_126425 prefixEnd_126425 2137178329046027829007 := by
  unfold tailWord_126425
  simp only [CollatzResearch.WordTrace]
  refine ⟨4611098566991291516108729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3074065711327527677405819 4611098566991291516108729)
  ·
    refine ⟨3458323925243468637081547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4611098566991291516108729 3458323925243468637081547)
    ·
      refine ⟨5187485887865202955622321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3458323925243468637081547 5187485887865202955622321)
      ·
        refine ⟨3890614415898902216716741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5187485887865202955622321 3890614415898902216716741)
        ·
          refine ⟨729490202981044165634389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3890614415898902216716741 729490202981044165634389)
          ·
            refine ⟨2137178329046027829007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 729490202981044165634389 2137178329046027829007)
            ·
              rfl

theorem cell20_126425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 10].length) (baseStart_126425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126425 prefixEnd_126425 := by exact prefixLift 126425
  have htrace : WordTrace (prefixWord ++ tailWord_126425) baseStart_126425 baseEnd_126425 := by
    simpa [prefixWord, tailWord_126425, baseEnd_126425] using wordTrace_append hprefix tailTrace_126425
  have hstable : (prefixWord ++ tailWord_126425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126425).length < 2 ^ (prefixWord ++ tailWord_126425).sum := by decide
  have hdescent : baseEnd_126425 < baseStart_126425 := by decide
  rcases family_descends (prefixWord ++ tailWord_126425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126456 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 6]
def baseStart_126456 : Nat := 118140960795 + 126456 * 2 ^ 59
def prefixEnd_126456 : Nat := 4983230072969 + 3 ^ 40 * 126456 * 2
def baseEnd_126456 : Nat := 57717964128944421349729

theorem tailTrace_126456 : CollatzResearch.WordTrace tailWord_126456 prefixEnd_126456 57717964128944421349729 := by
  unfold tailWord_126456
  simp only [CollatzResearch.WordTrace]
  refine ⟨2306114614939491905243611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3074819486585989206991481 2306114614939491905243611)
  ·
    refine ⟨3459171922409237857865417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2306114614939491905243611 3459171922409237857865417)
    ·
      refine ⟨2594378941806928393399063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3459171922409237857865417 2594378941806928393399063)
      ·
        refine ⟨3891568412710392590098595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2594378941806928393399063 3891568412710392590098595)
        ·
          refine ⟨5837352619065588885147893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3891568412710392590098595 5837352619065588885147893)
          ·
            refine ⟨547251808037398957982615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5837352619065588885147893 547251808037398957982615)
            ·
              refine ⟨820877712056098436973923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547251808037398957982615 820877712056098436973923)
              ·
                refine ⟨1231316568084147655460885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 820877712056098436973923 1231316568084147655460885)
                ·
                  refine ⟨57717964128944421349729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1231316568084147655460885 57717964128944421349729)
                  ·
                    rfl

theorem cell20_126456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_126456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126456 prefixEnd_126456 := by exact prefixLift 126456
  have htrace : WordTrace (prefixWord ++ tailWord_126456) baseStart_126456 baseEnd_126456 := by
    simpa [prefixWord, tailWord_126456, baseEnd_126456] using wordTrace_append hprefix tailTrace_126456
  have hstable : (prefixWord ++ tailWord_126456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126456).length < 2 ^ (prefixWord ++ tailWord_126456).sum := by decide
  have hdescent : baseEnd_126456 < baseStart_126456 := by decide
  rcases family_descends (prefixWord ++ tailWord_126456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126501 : List Nat := [1, 3, 1, 2, 2, 1, 1, 9]
def baseStart_126501 : Nat := 118140960795 + 126501 * 2 ^ 59
def prefixEnd_126501 : Nat := 4983230072969 + 3 ^ 40 * 126501 * 2
def baseEnd_126501 : Nat := 19246167785041421616515

theorem tailTrace_126501 : CollatzResearch.WordTrace tailWord_126501 prefixEnd_126501 19246167785041421616515 := by
  unfold tailWord_126501
  simp only [CollatzResearch.WordTrace]
  refine ⟨4613870514715956495875357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3075913676477304330583571 4613870514715956495875357)
  ·
    refine ⟨1730201443018483685953259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4613870514715956495875357 1730201443018483685953259)
    ·
      refine ⟨2595302164527725528929889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1730201443018483685953259 2595302164527725528929889)
      ·
        refine ⟨1946476623395794146697417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2595302164527725528929889 1946476623395794146697417)
        ·
          refine ⟨1459857467546845610023063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1946476623395794146697417 1459857467546845610023063)
          ·
            refine ⟨2189786201320268415034595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1459857467546845610023063 2189786201320268415034595)
            ·
              refine ⟨3284679301980402622551893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2189786201320268415034595 3284679301980402622551893)
              ·
                refine ⟨19246167785041421616515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3284679301980402622551893 19246167785041421616515)
                ·
                  rfl

theorem cell20_126501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 9].length) (baseStart_126501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126501 prefixEnd_126501 := by exact prefixLift 126501
  have htrace : WordTrace (prefixWord ++ tailWord_126501) baseStart_126501 baseEnd_126501 := by
    simpa [prefixWord, tailWord_126501, baseEnd_126501] using wordTrace_append hprefix tailTrace_126501
  have hstable : (prefixWord ++ tailWord_126501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126501).length < 2 ^ (prefixWord ++ tailWord_126501).sum := by decide
  have hdescent : baseEnd_126501 < baseStart_126501 := by decide
  rcases family_descends (prefixWord ++ tailWord_126501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126524 : List Nat := [2, 2, 2, 2, 5, 1, 1, 3, 2]
def baseStart_126524 : Nat := 118140960795 + 126524 * 2 ^ 59
def prefixEnd_126524 : Nat := 4983230072969 + 3 ^ 40 * 126524 * 2
def baseEnd_126524 : Nat := 57749001181838407082785

theorem tailTrace_126524 : CollatzResearch.WordTrace tailWord_126524 prefixEnd_126524 57749001181838407082785 := by
  unfold tailWord_126524
  simp only [CollatzResearch.WordTrace]
  refine ⟨2307354696816315711981313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3076472929088420949308417 2307354696816315711981313)
  ·
    refine ⟨1730516022612236783985985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2307354696816315711981313 1730516022612236783985985)
    ·
      refine ⟨1297887016959177587989489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1730516022612236783985985 1297887016959177587989489)
      ·
        refine ⟨973415262719383190992117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1297887016959177587989489 973415262719383190992117)
        ·
          refine ⟨91257680879942174155511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 973415262719383190992117 91257680879942174155511)
          ·
            refine ⟨136886521319913261233267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91257680879942174155511 136886521319913261233267)
            ·
              refine ⟨205329781979869891849901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136886521319913261233267 205329781979869891849901)
              ·
                refine ⟨76998668242451209443713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205329781979869891849901 76998668242451209443713)
                ·
                  refine ⟨57749001181838407082785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76998668242451209443713 57749001181838407082785)
                  ·
                    rfl

theorem cell20_126524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 3, 2].length) (baseStart_126524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126524 prefixEnd_126524 := by exact prefixLift 126524
  have htrace : WordTrace (prefixWord ++ tailWord_126524) baseStart_126524 baseEnd_126524 := by
    simpa [prefixWord, tailWord_126524, baseEnd_126524] using wordTrace_append hprefix tailTrace_126524
  have hstable : (prefixWord ++ tailWord_126524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126524).length < 2 ^ (prefixWord ++ tailWord_126524).sum := by decide
  have hdescent : baseEnd_126524 < baseStart_126524 := by decide
  rcases family_descends (prefixWord ++ tailWord_126524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126535 : List Nat := [1, 1, 4, 1, 6, 1, 6]
def baseStart_126535 : Nat := 118140960795 + 126535 * 2 ^ 59
def prefixEnd_126535 : Nat := 4983230072969 + 3 ^ 40 * 126535 * 2
def baseEnd_126535 : Nat := 6417113542396806412897

theorem tailTrace_126535 : CollatzResearch.WordTrace tailWord_126535 prefixEnd_126535 6417113542396806412897 := by
  unfold tailWord_126535
  simp only [CollatzResearch.WordTrace]
  refine ⟨4615110596592780302613059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3076740397728520201742039 4615110596592780302613059)
  ·
    refine ⟨6922665894889170453919589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4615110596592780302613059 6922665894889170453919589)
    ·
      refine ⟨1297999855291719460109923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6922665894889170453919589 1297999855291719460109923)
      ·
        refine ⟨1946999782937579190164885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1297999855291719460109923 1946999782937579190164885)
        ·
          refine ⟨91265614825199024538979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1946999782937579190164885 91265614825199024538979)
          ·
            refine ⟨136898422237798536808469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91265614825199024538979 136898422237798536808469)
            ·
              refine ⟨6417113542396806412897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 136898422237798536808469 6417113542396806412897)
              ·
                rfl

theorem cell20_126535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 6].length) (baseStart_126535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126535 prefixEnd_126535 := by exact prefixLift 126535
  have htrace : WordTrace (prefixWord ++ tailWord_126535) baseStart_126535 baseEnd_126535 := by
    simpa [prefixWord, tailWord_126535, baseEnd_126535] using wordTrace_append hprefix tailTrace_126535
  have hstable : (prefixWord ++ tailWord_126535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126535).length < 2 ^ (prefixWord ++ tailWord_126535).sum := by decide
  have hdescent : baseEnd_126535 < baseStart_126535 := by decide
  rcases family_descends (prefixWord ++ tailWord_126535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126556 : List Nat := [2, 2, 4, 1, 2, 1, 1, 7]
def baseStart_126556 : Nat := 118140960795 + 126556 * 2 ^ 59
def prefixEnd_126556 : Nat := 4983230072969 + 3 ^ 40 * 126556 * 2
def baseEnd_126556 : Nat := 19254535617929506005329

theorem tailTrace_126556 : CollatzResearch.WordTrace tailWord_126556 prefixEnd_126556 19254535617929506005329 := by
  unfold tailWord_126556
  simp only [CollatzResearch.WordTrace]
  refine ⟨2307938264758350444563761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3077251019677800592751681 2307938264758350444563761)
  ·
    refine ⟨1730953698568762833422821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2307938264758350444563761 1730953698568762833422821)
    ·
      refine ⟨324553818481643031266779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1730953698568762833422821 324553818481643031266779)
      ·
        refine ⟨486830727722464546900169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324553818481643031266779 486830727722464546900169)
        ·
          refine ⟨365123045791848410175127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486830727722464546900169 365123045791848410175127)
          ·
            refine ⟨547684568687772615262691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365123045791848410175127 547684568687772615262691)
            ·
              refine ⟨821526853031658922894037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547684568687772615262691 821526853031658922894037)
              ·
                refine ⟨19254535617929506005329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 821526853031658922894037 19254535617929506005329)
                ·
                  rfl

theorem cell20_126556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 7].length) (baseStart_126556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126556 prefixEnd_126556 := by exact prefixLift 126556
  have htrace : WordTrace (prefixWord ++ tailWord_126556) baseStart_126556 baseEnd_126556 := by
    simpa [prefixWord, tailWord_126556, baseEnd_126556] using wordTrace_append hprefix tailTrace_126556
  have hstable : (prefixWord ++ tailWord_126556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126556).length < 2 ^ (prefixWord ++ tailWord_126556).sum := by decide
  have hdescent : baseEnd_126556 < baseStart_126556 := by decide
  rcases family_descends (prefixWord ++ tailWord_126556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126587 : List Nat := [1, 1, 1, 1, 1, 4, 4, 5, 2]
def baseStart_126587 : Nat := 118140960795 + 126587 * 2 ^ 59
def prefixEnd_126587 : Nat := 4983230072969 + 3 ^ 40 * 126587 * 2
def baseEnd_126587 : Nat := 57777756098490187982527

theorem tailTrace_126587 : CollatzResearch.WordTrace tailWord_126587 prefixEnd_126587 57777756098490187982527 := by
  unfold tailWord_126587
  simp only [CollatzResearch.WordTrace]
  refine ⟨4617007192404393183506015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3078004794936262122337343 4617007192404393183506015)
  ·
    refine ⟨6925510788606589775259023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4617007192404393183506015 6925510788606589775259023)
    ·
      refine ⟨10388266182909884662888535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6925510788606589775259023 10388266182909884662888535)
      ·
        refine ⟨15582399274364826994332803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10388266182909884662888535 15582399274364826994332803)
        ·
          refine ⟨23373598911547240491499205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15582399274364826994332803 23373598911547240491499205)
          ·
            refine ⟨4382549795915107592156101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23373598911547240491499205 4382549795915107592156101)
            ·
              refine ⟨821728086734082673529269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4382549795915107592156101 821728086734082673529269)
              ·
                refine ⟨77037008131320250643369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 821728086734082673529269 77037008131320250643369)
                ·
                  refine ⟨57777756098490187982527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77037008131320250643369 57777756098490187982527)
                  ·
                    rfl

theorem cell20_126587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5, 2].length) (baseStart_126587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126587 prefixEnd_126587 := by exact prefixLift 126587
  have htrace : WordTrace (prefixWord ++ tailWord_126587) baseStart_126587 baseEnd_126587 := by
    simpa [prefixWord, tailWord_126587, baseEnd_126587] using wordTrace_append hprefix tailTrace_126587
  have hstable : (prefixWord ++ tailWord_126587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126587).length < 2 ^ (prefixWord ++ tailWord_126587).sum := by decide
  have hdescent : baseEnd_126587 < baseStart_126587 := by decide
  rcases family_descends (prefixWord ++ tailWord_126587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126601 : List Nat := [1, 2, 1, 1, 4, 1, 3, 4, 3]
def baseStart_126601 : Nat := 118140960795 + 126601 * 2 ^ 59
def prefixEnd_126601 : Nat := 4983230072969 + 3 ^ 40 * 126601 * 2
def baseEnd_126601 : Nat := 57784146079968361515803

theorem tailTrace_126601 : CollatzResearch.WordTrace tailWord_126601 prefixEnd_126601 57784146079968361515803 := by
  unfold tailWord_126601
  simp only [CollatzResearch.WordTrace]
  refine ⟨4617517814353673574515657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3078345209569115716343771 4617517814353673574515657)
  ·
    refine ⟨3463138360765255180886743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4617517814353673574515657 3463138360765255180886743)
    ·
      refine ⟨5194707541147882771330115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3463138360765255180886743 5194707541147882771330115)
      ·
        refine ⟨7792061311721824156995173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5194707541147882771330115 7792061311721824156995173)
        ·
          refine ⟨1461011495947842029436595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7792061311721824156995173 1461011495947842029436595)
          ·
            refine ⟨2191517243921763044154893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1461011495947842029436595 2191517243921763044154893)
            ·
              refine ⟨821818966470661141558085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2191517243921763044154893 821818966470661141558085)
              ·
                refine ⟨154091056213248964042141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 821818966470661141558085 154091056213248964042141)
                ·
                  refine ⟨57784146079968361515803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154091056213248964042141 57784146079968361515803)
                  ·
                    rfl

theorem cell20_126601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 3].length) (baseStart_126601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126601 prefixEnd_126601 := by exact prefixLift 126601
  have htrace : WordTrace (prefixWord ++ tailWord_126601) baseStart_126601 baseEnd_126601 := by
    simpa [prefixWord, tailWord_126601, baseEnd_126601] using wordTrace_append hprefix tailTrace_126601
  have hstable : (prefixWord ++ tailWord_126601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126601).length < 2 ^ (prefixWord ++ tailWord_126601).sum := by decide
  have hdescent : baseEnd_126601 < baseStart_126601 := by decide
  rcases family_descends (prefixWord ++ tailWord_126601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126625 : List Nat := [1, 2, 3, 3, 2, 2, 1, 2, 4]
def baseStart_126625 : Nat := 118140960795 + 126625 * 2 ^ 59
def prefixEnd_126625 : Nat := 4983230072969 + 3 ^ 40 * 126625 * 2
def baseEnd_126625 : Nat := 57795100333930944715705

theorem tailTrace_126625 : CollatzResearch.WordTrace tailWord_126625 prefixEnd_126625 57795100333930944715705 := by
  unfold tailWord_126625
  simp only [CollatzResearch.WordTrace]
  refine ⟨4618393166266725673389329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3078928777511150448926219 4618393166266725673389329)
  ·
    refine ⟨3463794874700044255041997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4618393166266725673389329 3463794874700044255041997)
    ·
      refine ⟨1298923078012516595640749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3463794874700044255041997 1298923078012516595640749)
      ·
        refine ⟨487096154254693723365281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1298923078012516595640749 487096154254693723365281)
        ·
          refine ⟨365322115691020292523961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487096154254693723365281 365322115691020292523961)
          ·
            refine ⟨273991586768265219392971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365322115691020292523961 273991586768265219392971)
            ·
              refine ⟨410987380152397829089457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273991586768265219392971 410987380152397829089457)
              ·
                refine ⟨308240535114298371817093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 410987380152397829089457 308240535114298371817093)
                ·
                  refine ⟨57795100333930944715705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 308240535114298371817093 57795100333930944715705)
                  ·
                    rfl

theorem cell20_126625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_126625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126625 prefixEnd_126625 := by exact prefixLift 126625
  have htrace : WordTrace (prefixWord ++ tailWord_126625) baseStart_126625 baseEnd_126625 := by
    simpa [prefixWord, tailWord_126625, baseEnd_126625] using wordTrace_append hprefix tailTrace_126625
  have hstable : (prefixWord ++ tailWord_126625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126625).length < 2 ^ (prefixWord ++ tailWord_126625).sum := by decide
  have hdescent : baseEnd_126625 < baseStart_126625 := by decide
  rcases family_descends (prefixWord ++ tailWord_126625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126638 : List Nat := [4, 1, 4, 1, 2, 1, 2, 3, 2]
def baseStart_126638 : Nat := 118140960795 + 126638 * 2 ^ 59
def prefixEnd_126638 : Nat := 4983230072969 + 3 ^ 40 * 126638 * 2
def baseEnd_126638 : Nat := 57801033888160677282319

theorem tailTrace_126638 : CollatzResearch.WordTrace tailWord_126638 prefixEnd_126638 57801033888160677282319 := by
  unfold tailWord_126638
  simp only [CollatzResearch.WordTrace]
  refine ⟨577358414402453611701571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3079244876813085929075045 577358414402453611701571)
  ·
    refine ⟨866037621603680417552357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 577358414402453611701571 866037621603680417552357)
    ·
      refine ⟨162382054050690078291067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 866037621603680417552357 162382054050690078291067)
      ·
        refine ⟨243573081076035117436601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162382054050690078291067 243573081076035117436601)
        ·
          refine ⟨182679810807026338077451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243573081076035117436601 182679810807026338077451)
          ·
            refine ⟨274019716210539507116177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182679810807026338077451 274019716210539507116177)
            ·
              refine ⟨205514787157904630337133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274019716210539507116177 205514787157904630337133)
              ·
                refine ⟨77068045184214236376425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205514787157904630337133 77068045184214236376425)
                ·
                  refine ⟨57801033888160677282319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77068045184214236376425 57801033888160677282319)
                  ·
                    rfl

theorem cell20_126638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_126638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126638 prefixEnd_126638 := by exact prefixLift 126638
  have htrace : WordTrace (prefixWord ++ tailWord_126638) baseStart_126638 baseEnd_126638 := by
    simpa [prefixWord, tailWord_126638, baseEnd_126638] using wordTrace_append hprefix tailTrace_126638
  have hstable : (prefixWord ++ tailWord_126638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126638).length < 2 ^ (prefixWord ++ tailWord_126638).sum := by decide
  have hdescent : baseEnd_126638 < baseStart_126638 := by decide
  rcases family_descends (prefixWord ++ tailWord_126638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126653 : List Nat := [1, 4, 1, 2, 1, 2, 9]
def baseStart_126653 : Nat := 118140960795 + 126653 * 2 ^ 59
def prefixEnd_126653 : Nat := 4983230072969 + 3 ^ 40 * 126653 * 2
def baseEnd_126653 : Nat := 6423097810765254642473

theorem tailTrace_126653 : CollatzResearch.WordTrace tailWord_126653 prefixEnd_126653 6423097810765254642473 := by
  unfold tailWord_126653
  simp only [CollatzResearch.WordTrace]
  refine ⟨4619414410165286455408613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3079609606776857636939075 4619414410165286455408613)
  ·
    refine ⟨866140201905991210389115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4619414410165286455408613 866140201905991210389115)
    ·
      refine ⟨1299210302858986815583673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 866140201905991210389115 1299210302858986815583673)
      ·
        refine ⟨974407727144240111687755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1299210302858986815583673 974407727144240111687755)
        ·
          refine ⟨1461611590716360167531633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 974407727144240111687755 1461611590716360167531633)
          ·
            refine ⟨1096208693037270125648725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1461611590716360167531633 1096208693037270125648725)
            ·
              refine ⟨6423097810765254642473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1096208693037270125648725 6423097810765254642473)
              ·
                rfl

theorem cell20_126653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 9].length) (baseStart_126653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126653 prefixEnd_126653 := by exact prefixLift 126653
  have htrace : WordTrace (prefixWord ++ tailWord_126653) baseStart_126653 baseEnd_126653 := by
    simpa [prefixWord, tailWord_126653, baseEnd_126653] using wordTrace_append hprefix tailTrace_126653
  have hstable : (prefixWord ++ tailWord_126653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126653).length < 2 ^ (prefixWord ++ tailWord_126653).sum := by decide
  have hdescent : baseEnd_126653 < baseStart_126653 := by decide
  rcases family_descends (prefixWord ++ tailWord_126653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126663 : List Nat := [1, 1, 4, 1, 1, 1, 3, 6, 2]
def baseStart_126663 : Nat := 118140960795 + 126663 * 2 ^ 59
def prefixEnd_126663 : Nat := 4983230072969 + 3 ^ 40 * 126663 * 2
def baseEnd_126663 : Nat := 57812444569371701448883

theorem tailTrace_126663 : CollatzResearch.WordTrace tailWord_126663 prefixEnd_126663 57812444569371701448883 := by
  unfold tailWord_126663
  simp only [CollatzResearch.WordTrace]
  refine ⟨4619779140129058163272643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3079852760086038775515095 4619779140129058163272643)
  ·
    refine ⟨6929668710193587244908965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4619779140129058163272643 6929668710193587244908965)
    ·
      refine ⟨1299312883161297608420431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6929668710193587244908965 1299312883161297608420431)
      ·
        refine ⟨1948969324741946412630647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1299312883161297608420431 1948969324741946412630647)
        ·
          refine ⟨2923453987112919618945971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1948969324741946412630647 2923453987112919618945971)
          ·
            refine ⟨4385180980669379428418957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2923453987112919618945971 4385180980669379428418957)
            ·
              refine ⟨1644442867751017285657109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4385180980669379428418957 1644442867751017285657109)
              ·
                refine ⟨77083259425828935265177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1644442867751017285657109 77083259425828935265177)
                ·
                  refine ⟨57812444569371701448883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77083259425828935265177 57812444569371701448883)
                  ·
                    rfl

theorem cell20_126663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 6, 2].length) (baseStart_126663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126663 prefixEnd_126663 := by exact prefixLift 126663
  have htrace : WordTrace (prefixWord ++ tailWord_126663) baseStart_126663 baseEnd_126663 := by
    simpa [prefixWord, tailWord_126663, baseEnd_126663] using wordTrace_append hprefix tailTrace_126663
  have hstable : (prefixWord ++ tailWord_126663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126663).length < 2 ^ (prefixWord ++ tailWord_126663).sum := by decide
  have hdescent : baseEnd_126663 < baseStart_126663 := by decide
  rcases family_descends (prefixWord ++ tailWord_126663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126732 : List Nat := [2, 2, 1, 2, 2, 1, 6, 1, 3]
def baseStart_126732 : Nat := 118140960795 + 126732 * 2 ^ 59
def prefixEnd_126732 : Nat := 4983230072969 + 3 ^ 40 * 126732 * 2
def baseEnd_126732 : Nat := 57843938049514128148601

theorem tailTrace_126732 : CollatzResearch.WordTrace tailWord_126732 prefixEnd_126732 57843938049514128148601 := by
  unfold tailWord_126732
  simp only [CollatzResearch.WordTrace]
  refine ⟨2311147888439541473767225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3081530517919388631689633 2311147888439541473767225)
  ·
    refine ⟨1733360916329656105325419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2311147888439541473767225 1733360916329656105325419)
    ·
      refine ⟨2600041374494484157988129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1733360916329656105325419 2600041374494484157988129)
      ·
        refine ⟨1950031030870863118491097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2600041374494484157988129 1950031030870863118491097)
        ·
          refine ⟨1462523273153147338868323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1950031030870863118491097 1462523273153147338868323)
          ·
            refine ⟨2193784909729721008302485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1462523273153147338868323 2193784909729721008302485)
            ·
              refine ⟨102833667643580672264179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2193784909729721008302485 102833667643580672264179)
              ·
                refine ⟨154250501465371008396269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102833667643580672264179 154250501465371008396269)
                ·
                  refine ⟨57843938049514128148601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154250501465371008396269 57843938049514128148601)
                  ·
                    rfl

theorem cell20_126732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_126732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126732 prefixEnd_126732 := by exact prefixLift 126732
  have htrace : WordTrace (prefixWord ++ tailWord_126732) baseStart_126732 baseEnd_126732 := by
    simpa [prefixWord, tailWord_126732, baseEnd_126732] using wordTrace_append hprefix tailTrace_126732
  have hstable : (prefixWord ++ tailWord_126732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126732).length < 2 ^ (prefixWord ++ tailWord_126732).sum := by decide
  have hdescent : baseEnd_126732 < baseStart_126732 := by decide
  rcases family_descends (prefixWord ++ tailWord_126732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126770 : List Nat := [3, 2, 1, 1, 3, 3, 2, 2, 3]
def baseStart_126770 : Nat := 118140960795 + 126770 * 2 ^ 59
def prefixEnd_126770 : Nat := 4983230072969 + 3 ^ 40 * 126770 * 2
def baseEnd_126770 : Nat := 57861282284954884881779

theorem tailTrace_126770 : CollatzResearch.WordTrace tailWord_126770 prefixEnd_126770 57861282284954884881779 := by
  unfold tailWord_126770
  simp only [CollatzResearch.WordTrace]
  refine ⟨1155920437685353859354441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3082454500494276958278509 1155920437685353859354441)
  ·
    refine ⟨866940328264015394515831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1155920437685353859354441 866940328264015394515831)
    ·
      refine ⟨1300410492396023091773747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 866940328264015394515831 1300410492396023091773747)
      ·
        refine ⟨1950615738594034637660621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1300410492396023091773747 1950615738594034637660621)
        ·
          refine ⟨731480901972762989122733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1950615738594034637660621 731480901972762989122733)
          ·
            refine ⟨274305338239786120921025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 731480901972762989122733 274305338239786120921025)
            ·
              refine ⟨205729003679839590690769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274305338239786120921025 205729003679839590690769)
              ·
                refine ⟨154296752759879693018077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205729003679839590690769 154296752759879693018077)
                ·
                  refine ⟨57861282284954884881779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154296752759879693018077 57861282284954884881779)
                  ·
                    rfl

theorem cell20_126770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_126770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126770 prefixEnd_126770 := by exact prefixLift 126770
  have htrace : WordTrace (prefixWord ++ tailWord_126770) baseStart_126770 baseEnd_126770 := by
    simpa [prefixWord, tailWord_126770, baseEnd_126770] using wordTrace_append hprefix tailTrace_126770
  have hstable : (prefixWord ++ tailWord_126770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126770).length < 2 ^ (prefixWord ++ tailWord_126770).sum := by decide
  have hdescent : baseEnd_126770 < baseStart_126770 := by decide
  rcases family_descends (prefixWord ++ tailWord_126770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126791 : List Nat := [1, 1, 4, 1, 2, 1, 4, 3, 3]
def baseStart_126791 : Nat := 118140960795 + 126791 * 2 ^ 59
def prefixEnd_126791 : Nat := 4983230072969 + 3 ^ 40 * 126791 * 2
def baseEnd_126791 : Nat := 57870867257172145181693

theorem tailTrace_126791 : CollatzResearch.WordTrace tailWord_126791 prefixEnd_126791 57870867257172145181693 := by
  unfold tailWord_126791
  simp only [CollatzResearch.WordTrace]
  refine ⟨4624447683665336023932227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3082965122443557349288151 4624447683665336023932227)
  ·
    refine ⟨6936671525498004035898341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4624447683665336023932227 6936671525498004035898341)
    ·
      refine ⟨1300625911030875756730939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6936671525498004035898341 1300625911030875756730939)
      ·
        refine ⟨1950938866546313635096409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1300625911030875756730939 1950938866546313635096409)
        ·
          refine ⟨1463204149909735226322307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1950938866546313635096409 1463204149909735226322307)
          ·
            refine ⟨2194806224864602839483461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1463204149909735226322307 2194806224864602839483461)
            ·
              refine ⟨411526167162113032403149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2194806224864602839483461 411526167162113032403149)
              ·
                refine ⟨154322312685792387151181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 411526167162113032403149 154322312685792387151181)
                ·
                  refine ⟨57870867257172145181693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154322312685792387151181 57870867257172145181693)
                  ·
                    rfl

theorem cell20_126791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 3].length) (baseStart_126791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126791 prefixEnd_126791 := by exact prefixLift 126791
  have htrace : WordTrace (prefixWord ++ tailWord_126791) baseStart_126791 baseEnd_126791 := by
    simpa [prefixWord, tailWord_126791, baseEnd_126791] using wordTrace_append hprefix tailTrace_126791
  have hstable : (prefixWord ++ tailWord_126791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126791).length < 2 ^ (prefixWord ++ tailWord_126791).sum := by decide
  have hdescent : baseEnd_126791 < baseStart_126791 := by decide
  rcases family_descends (prefixWord ++ tailWord_126791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126815 : List Nat := [1, 1, 2, 3, 1, 4, 1, 5, 2]
def baseStart_126815 : Nat := 118140960795 + 126815 * 2 ^ 59
def prefixEnd_126815 : Nat := 4983230072969 + 3 ^ 40 * 126815 * 2
def baseEnd_126815 : Nat := 57881821511134728381595

theorem tailTrace_126815 : CollatzResearch.WordTrace tailWord_126815 prefixEnd_126815 57881821511134728381595 := by
  unfold tailWord_126815
  simp only [CollatzResearch.WordTrace]
  refine ⟨4625323035578388122805899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3083548690385592081870599 4625323035578388122805899)
  ·
    refine ⟨6937984553367582184208849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4625323035578388122805899 6937984553367582184208849)
    ·
      refine ⟨5203488415025686638156637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6937984553367582184208849 5203488415025686638156637)
      ·
        refine ⟨1951308155634632489308739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5203488415025686638156637 1951308155634632489308739)
        ·
          refine ⟨2926962233451948733963109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1951308155634632489308739 2926962233451948733963109)
          ·
            refine ⟨548805418772240387618083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2926962233451948733963109 548805418772240387618083)
            ·
              refine ⟨823208128158360581427125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548805418772240387618083 823208128158360581427125)
              ·
                refine ⟨77175762014846304508793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 823208128158360581427125 77175762014846304508793)
                ·
                  refine ⟨57881821511134728381595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77175762014846304508793 57881821511134728381595)
                  ·
                    rfl

theorem cell20_126815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 5, 2].length) (baseStart_126815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126815 prefixEnd_126815 := by exact prefixLift 126815
  have htrace : WordTrace (prefixWord ++ tailWord_126815) baseStart_126815 baseEnd_126815 := by
    simpa [prefixWord, tailWord_126815, baseEnd_126815] using wordTrace_append hprefix tailTrace_126815
  have hstable : (prefixWord ++ tailWord_126815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126815).length < 2 ^ (prefixWord ++ tailWord_126815).sum := by decide
  have hdescent : baseEnd_126815 < baseStart_126815 := by decide
  rcases family_descends (prefixWord ++ tailWord_126815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126856 : List Nat := [2, 1, 3, 3, 4, 1, 2, 4]
def baseStart_126856 : Nat := 118140960795 + 126856 * 2 ^ 59
def prefixEnd_126856 : Nat := 4983230072969 + 3 ^ 40 * 126856 * 2
def baseEnd_126856 : Nat := 19300178342773602671587

theorem tailTrace_126856 : CollatzResearch.WordTrace tailWord_126856 prefixEnd_126856 19300178342773602671587 := by
  unfold tailWord_126856
  simp only [CollatzResearch.WordTrace]
  refine ⟨2313409214214926062524211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3084545618953234750032281 2313409214214926062524211)
  ·
    refine ⟨3470113821322389093786317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2313409214214926062524211 3470113821322389093786317)
    ·
      refine ⟨1301292682995895910169869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3470113821322389093786317 1301292682995895910169869)
      ·
        refine ⟨487984756123460966313701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1301292682995895910169869 487984756123460966313701)
        ·
          refine ⟨91497141773148931183819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 487984756123460966313701 91497141773148931183819)
          ·
            refine ⟨137245712659723396775729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91497141773148931183819 137245712659723396775729)
            ·
              refine ⟨102934284494792547581797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137245712659723396775729 102934284494792547581797)
              ·
                refine ⟨19300178342773602671587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102934284494792547581797 19300178342773602671587)
                ·
                  rfl

theorem cell20_126856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 4].length) (baseStart_126856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126856 prefixEnd_126856 := by exact prefixLift 126856
  have htrace : WordTrace (prefixWord ++ tailWord_126856) baseStart_126856 baseEnd_126856 := by
    simpa [prefixWord, tailWord_126856, baseEnd_126856] using wordTrace_append hprefix tailTrace_126856
  have hstable : (prefixWord ++ tailWord_126856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126856).length < 2 ^ (prefixWord ++ tailWord_126856).sum := by decide
  have hdescent : baseEnd_126856 < baseStart_126856 := by decide
  rcases family_descends (prefixWord ++ tailWord_126856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126887 : List Nat := [1, 1, 6, 1, 2, 2, 3, 2, 2]
def baseStart_126887 : Nat := 118140960795 + 126887 * 2 ^ 59
def prefixEnd_126887 : Nat := 4983230072969 + 3 ^ 40 * 126887 * 2
def baseEnd_126887 : Nat := 57914684273022477981301

theorem tailTrace_126887 : CollatzResearch.WordTrace tailWord_126887 prefixEnd_126887 57914684273022477981301 := by
  unfold tailWord_126887
  simp only [CollatzResearch.WordTrace]
  refine ⟨4627949091317544419426915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3085299394211696279617943 4627949091317544419426915)
  ·
    refine ⟨6941923636976316629140373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4627949091317544419426915 6941923636976316629140373)
    ·
      refine ⟨325402670483264841990955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6941923636976316629140373 325402670483264841990955)
      ·
        refine ⟨488104005724897262986433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325402670483264841990955 488104005724897262986433)
        ·
          refine ⟨366078004293672947239825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488104005724897262986433 366078004293672947239825)
          ·
            refine ⟨274558503220254710429869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366078004293672947239825 274558503220254710429869)
            ·
              refine ⟨102959438707595516411201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274558503220254710429869 102959438707595516411201)
              ·
                refine ⟨77219579030696637308401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102959438707595516411201 77219579030696637308401)
                ·
                  refine ⟨57914684273022477981301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77219579030696637308401 57914684273022477981301)
                  ·
                    rfl

theorem cell20_126887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 2, 2].length) (baseStart_126887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126887 prefixEnd_126887 := by exact prefixLift 126887
  have htrace : WordTrace (prefixWord ++ tailWord_126887) baseStart_126887 baseEnd_126887 := by
    simpa [prefixWord, tailWord_126887, baseEnd_126887] using wordTrace_append hprefix tailTrace_126887
  have hstable : (prefixWord ++ tailWord_126887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126887).length < 2 ^ (prefixWord ++ tailWord_126887).sum := by decide
  have hdescent : baseEnd_126887 < baseStart_126887 := by decide
  rcases family_descends (prefixWord ++ tailWord_126887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126901 : List Nat := [1, 3, 3, 2, 1, 4, 2, 1, 3]
def baseStart_126901 : Nat := 118140960795 + 126901 * 2 ^ 59
def prefixEnd_126901 : Nat := 4983230072969 + 3 ^ 40 * 126901 * 2
def baseEnd_126901 : Nat := 57921074254500651514577

theorem tailTrace_126901 : CollatzResearch.WordTrace tailWord_126901 prefixEnd_126901 57921074254500651514577 := by
  unfold tailWord_126901
  simp only [CollatzResearch.WordTrace]
  refine ⟨4628459713266824810436557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3085639808844549873624371 4628459713266824810436557)
  ·
    refine ⟨1735672392475059303913709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4628459713266824810436557 1735672392475059303913709)
    ·
      refine ⟨650877147178147238967641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1735672392475059303913709 650877147178147238967641)
      ·
        refine ⟨488157860383610429225731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 650877147178147238967641 488157860383610429225731)
        ·
          refine ⟨732236790575415643838597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488157860383610429225731 732236790575415643838597)
          ·
            refine ⟨137294398232890433219737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 732236790575415643838597 137294398232890433219737)
            ·
              refine ⟨102970798674667824914803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137294398232890433219737 102970798674667824914803)
              ·
                refine ⟨154456198012001737372205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102970798674667824914803 154456198012001737372205)
                ·
                  refine ⟨57921074254500651514577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154456198012001737372205 57921074254500651514577)
                  ·
                    rfl

theorem cell20_126901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_126901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126901 prefixEnd_126901 := by exact prefixLift 126901
  have htrace : WordTrace (prefixWord ++ tailWord_126901) baseStart_126901 baseEnd_126901 := by
    simpa [prefixWord, tailWord_126901, baseEnd_126901] using wordTrace_append hprefix tailTrace_126901
  have hstable : (prefixWord ++ tailWord_126901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126901).length < 2 ^ (prefixWord ++ tailWord_126901).sum := by decide
  have hdescent : baseEnd_126901 < baseStart_126901 := by decide
  rcases family_descends (prefixWord ++ tailWord_126901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126905 : List Nat := [1, 2, 1, 4, 2, 1, 3, 3, 3]
def baseStart_126905 : Nat := 118140960795 + 126905 * 2 ^ 59
def prefixEnd_126905 : Nat := 4983230072969 + 3 ^ 40 * 126905 * 2
def baseEnd_126905 : Nat := 57922899963494415381227

theorem tailTrace_126905 : CollatzResearch.WordTrace tailWord_126905 prefixEnd_126905 57922899963494415381227 := by
  unfold tailWord_126905
  simp only [CollatzResearch.WordTrace]
  refine ⟨4628605605252333493582169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3085737070168222329054779 4628605605252333493582169)
  ·
    refine ⟨3471454203939250120186627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4628605605252333493582169 3471454203939250120186627)
    ·
      refine ⟨5207181305908875180279941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3471454203939250120186627 5207181305908875180279941)
      ·
        refine ⟨976346494857914096302489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5207181305908875180279941 976346494857914096302489)
        ·
          refine ⟨732259871143435572226867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 976346494857914096302489 732259871143435572226867)
          ·
            refine ⟨1098389806715153358340301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732259871143435572226867 1098389806715153358340301)
            ·
              refine ⟨411896177518182509377613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1098389806715153358340301 411896177518182509377613)
              ·
                refine ⟨154461066569318441016605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 411896177518182509377613 154461066569318441016605)
                ·
                  refine ⟨57922899963494415381227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154461066569318441016605 57922899963494415381227)
                  ·
                    rfl

theorem cell20_126905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 3].length) (baseStart_126905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126905 prefixEnd_126905 := by exact prefixLift 126905
  have htrace : WordTrace (prefixWord ++ tailWord_126905) baseStart_126905 baseEnd_126905 := by
    simpa [prefixWord, tailWord_126905, baseEnd_126905] using wordTrace_append hprefix tailTrace_126905
  have hstable : (prefixWord ++ tailWord_126905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126905).length < 2 ^ (prefixWord ++ tailWord_126905).sum := by decide
  have hdescent : baseEnd_126905 < baseStart_126905 := by decide
  rcases family_descends (prefixWord ++ tailWord_126905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126943 : List Nat := [1, 1, 2, 3, 4, 1, 1, 4, 3]
def baseStart_126943 : Nat := 118140960795 + 126943 * 2 ^ 59
def prefixEnd_126943 : Nat := 4983230072969 + 3 ^ 40 * 126943 * 2
def baseEnd_126943 : Nat := 57940244198935172114405

theorem tailTrace_126943 : CollatzResearch.WordTrace tailWord_126943 prefixEnd_126943 57940244198935172114405 := by
  unfold tailWord_126943
  simp only [CollatzResearch.WordTrace]
  refine ⟨4629991579114665983465483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3086661052743110655643655 4629991579114665983465483)
  ·
    refine ⟨6944987368671998975198225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4629991579114665983465483 6944987368671998975198225)
    ·
      refine ⟨5208740526503999231398669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6944987368671998975198225 5208740526503999231398669)
      ·
        refine ⟨1953277697438999711774501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5208740526503999231398669 1953277697438999711774501)
        ·
          refine ⟨366239568269812445957719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1953277697438999711774501 366239568269812445957719)
          ·
            refine ⟨549359352404718668936579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366239568269812445957719 549359352404718668936579)
            ·
              refine ⟨824039028607078003404869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549359352404718668936579 824039028607078003404869)
              ·
                refine ⟨154507317863827125638413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 824039028607078003404869 154507317863827125638413)
                ·
                  refine ⟨57940244198935172114405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154507317863827125638413 57940244198935172114405)
                  ·
                    rfl

theorem cell20_126943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 3].length) (baseStart_126943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126943 prefixEnd_126943 := by exact prefixLift 126943
  have htrace : WordTrace (prefixWord ++ tailWord_126943) baseStart_126943 baseEnd_126943 := by
    simpa [prefixWord, tailWord_126943, baseEnd_126943] using wordTrace_append hprefix tailTrace_126943
  have hstable : (prefixWord ++ tailWord_126943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126943).length < 2 ^ (prefixWord ++ tailWord_126943).sum := by decide
  have hdescent : baseEnd_126943 < baseStart_126943 := by decide
  rcases family_descends (prefixWord ++ tailWord_126943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126971 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 6]
def baseStart_126971 : Nat := 118140960795 + 126971 * 2 ^ 59
def prefixEnd_126971 : Nat := 4983230072969 + 3 ^ 40 * 126971 * 2
def baseEnd_126971 : Nat := 57953024161891519180957

theorem tailTrace_126971 : CollatzResearch.WordTrace tailWord_126971 prefixEnd_126971 57953024161891519180957 := by
  unfold tailWord_126971
  simp only [CollatzResearch.WordTrace]
  refine ⟨4631012823013226765484767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3087341882008817843656511 4631012823013226765484767)
  ·
    refine ⟨6946519234519840148227151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4631012823013226765484767 6946519234519840148227151)
    ·
      refine ⟨10419778851779760222340727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6946519234519840148227151 10419778851779760222340727)
      ·
        refine ⟨15629668277669640333511091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10419778851779760222340727 15629668277669640333511091)
        ·
          refine ⟨23444502416504460500266637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15629668277669640333511091 23444502416504460500266637)
          ·
            refine ⟨8791688406189172687599989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23444502416504460500266637 8791688406189172687599989)
            ·
              refine ⟨824220788080234939462499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8791688406189172687599989 824220788080234939462499)
              ·
                refine ⟨1236331182120352409193749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 824220788080234939462499 1236331182120352409193749)
                ·
                  refine ⟨57953024161891519180957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1236331182120352409193749 57953024161891519180957)
                  ·
                    rfl

theorem cell20_126971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 6].length) (baseStart_126971 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_126971 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_126971 prefixEnd_126971 := by exact prefixLift 126971
  have htrace : WordTrace (prefixWord ++ tailWord_126971) baseStart_126971 baseEnd_126971 := by
    simpa [prefixWord, tailWord_126971, baseEnd_126971] using wordTrace_append hprefix tailTrace_126971
  have hstable : (prefixWord ++ tailWord_126971).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126971).length < 2 ^ (prefixWord ++ tailWord_126971).sum := by decide
  have hdescent : baseEnd_126971 < baseStart_126971 := by decide
  rcases family_descends (prefixWord ++ tailWord_126971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127005 : List Nat := [1, 4, 2, 2, 2, 2, 2, 1, 4]
def baseStart_127005 : Nat := 118140960795 + 127005 * 2 ^ 59
def prefixEnd_127005 : Nat := 4983230072969 + 3 ^ 40 * 127005 * 2
def baseEnd_127005 : Nat := 57968542688338512047485

theorem tailTrace_127005 : CollatzResearch.WordTrace tailWord_127005 prefixEnd_127005 57968542688338512047485 := by
  unfold tailWord_127005
  simp only [CollatzResearch.WordTrace]
  refine ⟨4632252904890050572222469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3088168603260033714814979 4632252904890050572222469)
  ·
    refine ⟨868547419666884482291713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4632252904890050572222469 868547419666884482291713)
    ·
      refine ⟨651410564750163361718785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 868547419666884482291713 651410564750163361718785)
      ·
        refine ⟨488557923562622521289089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 651410564750163361718785 488557923562622521289089)
        ·
          refine ⟨366418442671966890966817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488557923562622521289089 366418442671966890966817)
          ·
            refine ⟨274813832003975168225113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366418442671966890966817 274813832003975168225113)
            ·
              refine ⟨206110374002981376168835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274813832003975168225113 206110374002981376168835)
              ·
                refine ⟨309165561004472064253253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206110374002981376168835 309165561004472064253253)
                ·
                  refine ⟨57968542688338512047485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 309165561004472064253253 57968542688338512047485)
                  ·
                    rfl

theorem cell20_127005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_127005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127005 prefixEnd_127005 := by exact prefixLift 127005
  have htrace : WordTrace (prefixWord ++ tailWord_127005) baseStart_127005 baseEnd_127005 := by
    simpa [prefixWord, tailWord_127005, baseEnd_127005] using wordTrace_append hprefix tailTrace_127005
  have hstable : (prefixWord ++ tailWord_127005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127005).length < 2 ^ (prefixWord ++ tailWord_127005).sum := by decide
  have hdescent : baseEnd_127005 < baseStart_127005 := by decide
  rcases family_descends (prefixWord ++ tailWord_127005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127026 : List Nat := [3, 2, 1, 1, 2, 3, 2, 2, 4]
def baseStart_127026 : Nat := 118140960795 + 127026 * 2 ^ 59
def prefixEnd_127026 : Nat := 4983230072969 + 3 ^ 40 * 127026 * 2
def baseEnd_127026 : Nat := 57978127660555772347399

theorem tailTrace_127026 : CollatzResearch.WordTrace tailWord_127026 prefixEnd_127026 57978127660555772347399 := by
  unfold tailWord_127026
  simp only [CollatzResearch.WordTrace]
  refine ⟨1158254709453492789684233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3088679225209314105824621 1158254709453492789684233)
  ·
    refine ⟨868691032090119592263175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1158254709453492789684233 868691032090119592263175)
    ·
      refine ⟨1303036548135179388394763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 868691032090119592263175 1303036548135179388394763)
      ·
        refine ⟨1954554822202769082592145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1303036548135179388394763 1954554822202769082592145)
        ·
          refine ⟨1465916116652076811944109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1954554822202769082592145 1465916116652076811944109)
          ·
            refine ⟨549718543744528804479041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1465916116652076811944109 549718543744528804479041)
            ·
              refine ⟨412288907808396603359281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 549718543744528804479041 412288907808396603359281)
              ·
                refine ⟨309216680856297452519461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 412288907808396603359281 309216680856297452519461)
                ·
                  refine ⟨57978127660555772347399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 309216680856297452519461 57978127660555772347399)
                  ·
                    rfl

theorem cell20_127026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_127026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127026 prefixEnd_127026 := by exact prefixLift 127026
  have htrace : WordTrace (prefixWord ++ tailWord_127026) baseStart_127026 baseEnd_127026 := by
    simpa [prefixWord, tailWord_127026, baseEnd_127026] using wordTrace_append hprefix tailTrace_127026
  have hstable : (prefixWord ++ tailWord_127026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127026).length < 2 ^ (prefixWord ++ tailWord_127026).sum := by decide
  have hdescent : baseEnd_127026 < baseStart_127026 := by decide
  rcases family_descends (prefixWord ++ tailWord_127026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127040 : List Nat := [2, 1, 1, 2, 2, 4, 1, 2, 5]
def baseStart_127040 : Nat := 118140960795 + 127040 * 2 ^ 59
def prefixEnd_127040 : Nat := 4983230072969 + 3 ^ 40 * 127040 * 2
def baseEnd_127040 : Nat := 57984517642033945880675

theorem tailTrace_127040 : CollatzResearch.WordTrace tailWord_127040 prefixEnd_127040 57984517642033945880675 := by
  unfold tailWord_127040
  simp only [CollatzResearch.WordTrace]
  refine ⟨2316764729881625774873287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3089019639842167699831049 2316764729881625774873287)
  ·
    refine ⟨3475147094822438662309931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2316764729881625774873287 3475147094822438662309931)
    ·
      refine ⟨5212720642233657993464897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3475147094822438662309931 5212720642233657993464897)
      ·
        refine ⟨3909540481675243495098673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5212720642233657993464897 3909540481675243495098673)
        ·
          refine ⟨2932155361256432621324005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3909540481675243495098673 2932155361256432621324005)
          ·
            refine ⟨549779130235581116498251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2932155361256432621324005 549779130235581116498251)
            ·
              refine ⟨824668695353371674747377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549779130235581116498251 824668695353371674747377)
              ·
                refine ⟨618501521515028756060533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 824668695353371674747377 618501521515028756060533)
                ·
                  refine ⟨57984517642033945880675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 618501521515028756060533 57984517642033945880675)
                  ·
                    rfl

theorem cell20_127040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_127040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127040 prefixEnd_127040 := by exact prefixLift 127040
  have htrace : WordTrace (prefixWord ++ tailWord_127040) baseStart_127040 baseEnd_127040 := by
    simpa [prefixWord, tailWord_127040, baseEnd_127040] using wordTrace_append hprefix tailTrace_127040
  have hstable : (prefixWord ++ tailWord_127040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127040).length < 2 ^ (prefixWord ++ tailWord_127040).sum := by decide
  have hdescent : baseEnd_127040 < baseStart_127040 := by decide
  rcases family_descends (prefixWord ++ tailWord_127040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127064 : List Nat := [2, 1, 2, 2, 1, 4, 3, 1, 4]
def baseStart_127064 : Nat := 118140960795 + 127064 * 2 ^ 59
def prefixEnd_127064 : Nat := 4983230072969 + 3 ^ 40 * 127064 * 2
def baseEnd_127064 : Nat := 57995471895996529080577

theorem tailTrace_127064 : CollatzResearch.WordTrace tailWord_127064 prefixEnd_127064 57995471895996529080577 := by
  unfold tailWord_127064
  simp only [CollatzResearch.WordTrace]
  refine ⟨2317202405838151824310123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3089603207784202432413497 2317202405838151824310123)
  ·
    refine ⟨3475803608757227736465185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2317202405838151824310123 3475803608757227736465185)
    ·
      refine ⟨2606852706567920802348889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3475803608757227736465185 2606852706567920802348889)
      ·
        refine ⟨1955139529925940601761667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2606852706567920802348889 1955139529925940601761667)
        ·
          refine ⟨2932709294888910902642501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1955139529925940601761667 2932709294888910902642501)
          ·
            refine ⟨549882992791670794245469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2932709294888910902642501 549882992791670794245469)
            ·
              refine ⟨206206122296876547842051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 549882992791670794245469 206206122296876547842051)
              ·
                refine ⟨309309183445314821763077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206206122296876547842051 309309183445314821763077)
                ·
                  refine ⟨57995471895996529080577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 309309183445314821763077 57995471895996529080577)
                  ·
                    rfl

theorem cell20_127064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_127064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127064 prefixEnd_127064 := by exact prefixLift 127064
  have htrace : WordTrace (prefixWord ++ tailWord_127064) baseStart_127064 baseEnd_127064 := by
    simpa [prefixWord, tailWord_127064, baseEnd_127064] using wordTrace_append hprefix tailTrace_127064
  have hstable : (prefixWord ++ tailWord_127064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127064).length < 2 ^ (prefixWord ++ tailWord_127064).sum := by decide
  have hdescent : baseEnd_127064 < baseStart_127064 := by decide
  rcases family_descends (prefixWord ++ tailWord_127064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127070 : List Nat := [4, 4, 1, 1, 2, 1, 1, 3, 3]
def baseStart_127070 : Nat := 118140960795 + 127070 * 2 ^ 59
def prefixEnd_127070 : Nat := 4983230072969 + 3 ^ 40 * 127070 * 2
def baseEnd_127070 : Nat := 57998210459487174880553

theorem tailTrace_127070 : CollatzResearch.WordTrace tailWord_127070 prefixEnd_127070 57998210459487174880553 := by
  unfold tailWord_127070
  simp only [CollatzResearch.WordTrace]
  refine ⟨579327956206820834167333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3089749099769711115559109 579327956206820834167333)
  ·
    refine ⟨108623991788778906406375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 579327956206820834167333 108623991788778906406375)
    ·
      refine ⟨162935987683168359609563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108623991788778906406375 162935987683168359609563)
      ·
        refine ⟨244403981524752539414345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162935987683168359609563 244403981524752539414345)
        ·
          refine ⟨183302986143564404560759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244403981524752539414345 183302986143564404560759)
          ·
            refine ⟨274954479215346606841139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183302986143564404560759 274954479215346606841139)
            ·
              refine ⟨412431718823019910261709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274954479215346606841139 412431718823019910261709)
              ·
                refine ⟨154661894558632466348141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 412431718823019910261709 154661894558632466348141)
                ·
                  refine ⟨57998210459487174880553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154661894558632466348141 57998210459487174880553)
                  ·
                    rfl

theorem cell20_127070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_127070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127070 prefixEnd_127070 := by exact prefixLift 127070
  have htrace : WordTrace (prefixWord ++ tailWord_127070) baseStart_127070 baseEnd_127070 := by
    simpa [prefixWord, tailWord_127070, baseEnd_127070] using wordTrace_append hprefix tailTrace_127070
  have hstable : (prefixWord ++ tailWord_127070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127070).length < 2 ^ (prefixWord ++ tailWord_127070).sum := by decide
  have hdescent : baseEnd_127070 < baseStart_127070 := by decide
  rcases family_descends (prefixWord ++ tailWord_127070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127112 : List Nat := [2, 1, 3, 4, 1, 2, 2, 2, 3]
def baseStart_127112 : Nat := 118140960795 + 127112 * 2 ^ 59
def prefixEnd_127112 : Nat := 4983230072969 + 3 ^ 40 * 127112 * 2
def baseEnd_127112 : Nat := 58017380403921695480381

theorem tailTrace_127112 : CollatzResearch.WordTrace tailWord_127112 prefixEnd_127112 58017380403921695480381 := by
  unfold tailWord_127112
  simp only [CollatzResearch.WordTrace]
  refine ⟨2318077757751203923183795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3090770343668271897578393 2318077757751203923183795)
  ·
    refine ⟨3477116636626805884775693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2318077757751203923183795 3477116636626805884775693)
    ·
      refine ⟨1303918738735052206790885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3477116636626805884775693 1303918738735052206790885)
      ·
        refine ⟨244484763512822288773291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1303918738735052206790885 244484763512822288773291)
        ·
          refine ⟨366727145269233433159937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244484763512822288773291 366727145269233433159937)
          ·
            refine ⟨275045358951925074869953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366727145269233433159937 275045358951925074869953)
            ·
              refine ⟨206284019213943806152465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275045358951925074869953 206284019213943806152465)
              ·
                refine ⟨154713014410457854614349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206284019213943806152465 154713014410457854614349)
                ·
                  refine ⟨58017380403921695480381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154713014410457854614349 58017380403921695480381)
                  ·
                    rfl

theorem cell20_127112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 3].length) (baseStart_127112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127112 prefixEnd_127112 := by exact prefixLift 127112
  have htrace : WordTrace (prefixWord ++ tailWord_127112) baseStart_127112 baseEnd_127112 := by
    simpa [prefixWord, tailWord_127112, baseEnd_127112] using wordTrace_append hprefix tailTrace_127112
  have hstable : (prefixWord ++ tailWord_127112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127112).length < 2 ^ (prefixWord ++ tailWord_127112).sum := by decide
  have hdescent : baseEnd_127112 < baseStart_127112 := by decide
  rcases family_descends (prefixWord ++ tailWord_127112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127123 : List Nat := [1, 1, 1, 2, 1, 2, 3, 5, 4]
def baseStart_127123 : Nat := 118140960795 + 127123 * 2 ^ 59
def prefixEnd_127123 : Nat := 4983230072969 + 3 ^ 40 * 127123 * 2
def baseEnd_127123 : Nat := 58022401103654546113669

theorem tailTrace_127123 : CollatzResearch.WordTrace tailWord_127123 prefixEnd_127123 58022401103654546113669 := by
  unfold tailWord_127123
  simp only [CollatzResearch.WordTrace]
  refine ⟨4636556718462556725018023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3091037812308371150012015 4636556718462556725018023)
  ·
    refine ⟨6954835077693835087527035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4636556718462556725018023 6954835077693835087527035)
    ·
      refine ⟨10432252616540752631290553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6954835077693835087527035 10432252616540752631290553)
      ·
        refine ⟨7824189462405564473467915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10432252616540752631290553 7824189462405564473467915)
        ·
          refine ⟨11736284193608346710201873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7824189462405564473467915 11736284193608346710201873)
          ·
            refine ⟨8802213145206260032651405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11736284193608346710201873 8802213145206260032651405)
            ·
              refine ⟨3300829929452347512244277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8802213145206260032651405 3300829929452347512244277)
              ·
                refine ⟨309452805886157579272901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3300829929452347512244277 309452805886157579272901)
                ·
                  refine ⟨58022401103654546113669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 309452805886157579272901 58022401103654546113669)
                  ·
                    rfl

theorem cell20_127123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 4].length) (baseStart_127123 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127123 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127123 prefixEnd_127123 := by exact prefixLift 127123
  have htrace : WordTrace (prefixWord ++ tailWord_127123) baseStart_127123 baseEnd_127123 := by
    simpa [prefixWord, tailWord_127123, baseEnd_127123] using wordTrace_append hprefix tailTrace_127123
  have hstable : (prefixWord ++ tailWord_127123).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127123).length < 2 ^ (prefixWord ++ tailWord_127123).sum := by decide
  have hdescent : baseEnd_127123 < baseStart_127123 := by decide
  rcases family_descends (prefixWord ++ tailWord_127123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127133 : List Nat := [1, 4, 2, 1, 1, 3, 2, 3, 3]
def baseStart_127133 : Nat := 118140960795 + 127133 * 2 ^ 59
def prefixEnd_127133 : Nat := 4983230072969 + 3 ^ 40 * 127133 * 2
def baseEnd_127133 : Nat := 58026965376138955780295

theorem tailTrace_127133 : CollatzResearch.WordTrace tailWord_127133 prefixEnd_127133 58026965376138955780295 := by
  unfold tailWord_127133
  simp only [CollatzResearch.WordTrace]
  refine ⟨4636921448426328432882053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3091280965617552288588035 4636921448426328432882053)
  ·
    refine ⟨869422771579936581165385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4636921448426328432882053 869422771579936581165385)
    ·
      refine ⟨652067078684952435874039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 869422771579936581165385 652067078684952435874039)
      ·
        refine ⟨978100618027428653811059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652067078684952435874039 978100618027428653811059)
        ·
          refine ⟨1467150927041142980716589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 978100618027428653811059 1467150927041142980716589)
          ·
            refine ⟨550181597640428617768721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1467150927041142980716589 550181597640428617768721)
            ·
              refine ⟨412636198230321463326541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 550181597640428617768721 412636198230321463326541)
              ·
                refine ⟨154738574336370548747453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 412636198230321463326541 154738574336370548747453)
                ·
                  refine ⟨58026965376138955780295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154738574336370548747453 58026965376138955780295)
                  ·
                    rfl

theorem cell20_127133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_127133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127133 prefixEnd_127133 := by exact prefixLift 127133
  have htrace : WordTrace (prefixWord ++ tailWord_127133) baseStart_127133 baseEnd_127133 := by
    simpa [prefixWord, tailWord_127133, baseEnd_127133] using wordTrace_append hprefix tailTrace_127133
  have hstable : (prefixWord ++ tailWord_127133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127133).length < 2 ^ (prefixWord ++ tailWord_127133).sum := by decide
  have hdescent : baseEnd_127133 < baseStart_127133 := by decide
  rcases family_descends (prefixWord ++ tailWord_127133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127143 : List Nat := [1, 1, 6, 2, 2, 1, 3, 4]
def baseStart_127143 : Nat := 118140960795 + 127143 * 2 ^ 59
def prefixEnd_127143 : Nat := 4983230072969 + 3 ^ 40 * 127143 * 2
def baseEnd_127143 : Nat := 19343843216207788482307

theorem tailTrace_127143 : CollatzResearch.WordTrace tailWord_127143 prefixEnd_127143 19343843216207788482307 := by
  unfold tailWord_127143
  simp only [CollatzResearch.WordTrace]
  refine ⟨4637286178390100140746083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3091524118926733427164055 4637286178390100140746083)
  ·
    refine ⟨6955929267585150211119125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4637286178390100140746083 6955929267585150211119125)
    ·
      refine ⟨326059184418053916146209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6955929267585150211119125 326059184418053916146209)
      ·
        refine ⟨244544388313540437109657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326059184418053916146209 244544388313540437109657)
        ·
          refine ⟨183408291235155327832243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244544388313540437109657 183408291235155327832243)
          ·
            refine ⟨275112436852732991748365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183408291235155327832243 275112436852732991748365)
            ·
              refine ⟨103167163819774871905637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275112436852732991748365 103167163819774871905637)
              ·
                refine ⟨19343843216207788482307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103167163819774871905637 19343843216207788482307)
                ·
                  rfl

theorem cell20_127143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 4].length) (baseStart_127143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127143 prefixEnd_127143 := by exact prefixLift 127143
  have htrace : WordTrace (prefixWord ++ tailWord_127143) baseStart_127143 baseEnd_127143 := by
    simpa [prefixWord, tailWord_127143, baseEnd_127143] using wordTrace_append hprefix tailTrace_127143
  have hstable : (prefixWord ++ tailWord_127143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127143).length < 2 ^ (prefixWord ++ tailWord_127143).sum := by decide
  have hdescent : baseEnd_127143 < baseStart_127143 := by decide
  rcases family_descends (prefixWord ++ tailWord_127143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127154 : List Nat := [3, 2, 1, 1, 1, 3, 2, 2, 5]
def baseStart_127154 : Nat := 118140960795 + 127154 * 2 ^ 59
def prefixEnd_127154 : Nat := 4983230072969 + 3 ^ 40 * 127154 * 2
def baseEnd_127154 : Nat := 58036550348356216080209

theorem tailTrace_127154 : CollatzResearch.WordTrace tailWord_127154 prefixEnd_127154 58036550348356216080209 := by
  unfold tailWord_127154
  simp only [CollatzResearch.WordTrace]
  refine ⟨1159421845337562254849129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3091791587566832679597677 1159421845337562254849129)
  ·
    refine ⟨869566384003171691136847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1159421845337562254849129 869566384003171691136847)
    ·
      refine ⟨1304349576004757536705271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 869566384003171691136847 1304349576004757536705271)
      ·
        refine ⟨1956524364007136305057907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1304349576004757536705271 1956524364007136305057907)
        ·
          refine ⟨2934786546010704457586861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1956524364007136305057907 2934786546010704457586861)
          ·
            refine ⟨1100544954754014171595073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2934786546010704457586861 1100544954754014171595073)
            ·
              refine ⟨825408716065510628696305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1100544954754014171595073 825408716065510628696305)
              ·
                refine ⟨619056537049132971522229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 825408716065510628696305 619056537049132971522229)
                ·
                  refine ⟨58036550348356216080209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 619056537049132971522229 58036550348356216080209)
                  ·
                    rfl

theorem cell20_127154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_127154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127154 prefixEnd_127154 := by exact prefixLift 127154
  have htrace : WordTrace (prefixWord ++ tailWord_127154) baseStart_127154 baseEnd_127154 := by
    simpa [prefixWord, tailWord_127154, baseEnd_127154] using wordTrace_append hprefix tailTrace_127154
  have hstable : (prefixWord ++ tailWord_127154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127154).length < 2 ^ (prefixWord ++ tailWord_127154).sum := by decide
  have hdescent : baseEnd_127154 < baseStart_127154 := by decide
  rcases family_descends (prefixWord ++ tailWord_127154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127161 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 6]
def baseStart_127161 : Nat := 118140960795 + 127161 * 2 ^ 59
def prefixEnd_127161 : Nat := 4983230072969 + 3 ^ 40 * 127161 * 2
def baseEnd_127161 : Nat := 58039745339095302846847

theorem tailTrace_127161 : CollatzResearch.WordTrace tailWord_127161 prefixEnd_127161 58039745339095302846847 := by
  unfold tailWord_127161
  simp only [CollatzResearch.WordTrace]
  refine ⟨4637942692324889214901337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3091961794883259476600891 4637942692324889214901337)
  ·
    refine ⟨3478457019243666911176003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4637942692324889214901337 3478457019243666911176003)
    ·
      refine ⟨5217685528865500366764005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3478457019243666911176003 5217685528865500366764005)
      ·
        refine ⟨978316036662281318768251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5217685528865500366764005 978316036662281318768251)
        ·
          refine ⟨1467474054993421978152377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 978316036662281318768251 1467474054993421978152377)
          ·
            refine ⟨1100605541245066483614283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1467474054993421978152377 1100605541245066483614283)
            ·
              refine ⟨1650908311867599725421425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1100605541245066483614283 1650908311867599725421425)
              ·
                refine ⟨1238181233900699794066069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1650908311867599725421425 1238181233900699794066069)
                ·
                  refine ⟨58039745339095302846847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1238181233900699794066069 58039745339095302846847)
                  ·
                    rfl

theorem cell20_127161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_127161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127161 prefixEnd_127161 := by exact prefixLift 127161
  have htrace : WordTrace (prefixWord ++ tailWord_127161) baseStart_127161 baseEnd_127161 := by
    simpa [prefixWord, tailWord_127161, baseEnd_127161] using wordTrace_append hprefix tailTrace_127161
  have hstable : (prefixWord ++ tailWord_127161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127161).length < 2 ^ (prefixWord ++ tailWord_127161).sum := by decide
  have hdescent : baseEnd_127161 < baseStart_127161 := by decide
  rcases family_descends (prefixWord ++ tailWord_127161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127178 : List Nat := [3, 1, 2, 1, 3, 1, 4, 1, 4]
def baseStart_127178 : Nat := 118140960795 + 127178 * 2 ^ 59
def prefixEnd_127178 : Nat := 4983230072969 + 3 ^ 40 * 127178 * 2
def baseEnd_127178 : Nat := 58047504602318799280111

theorem tailTrace_127178 : CollatzResearch.WordTrace tailWord_127178 prefixEnd_127178 58047504602318799280111 := by
  unfold tailWord_127178
  simp only [CollatzResearch.WordTrace]
  refine ⟨1159640683315825279567547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3092375155508867412180125 1159640683315825279567547)
  ·
    refine ⟨1739461024973737919351321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1159640683315825279567547 1739461024973737919351321)
    ·
      refine ⟨1304595768730303439513491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1739461024973737919351321 1304595768730303439513491)
      ·
        refine ⟨1956893653095455159270237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1304595768730303439513491 1956893653095455159270237)
        ·
          refine ⟨733835119910795684726339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1956893653095455159270237 733835119910795684726339)
          ·
            refine ⟨1100752679866193527089509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733835119910795684726339 1100752679866193527089509)
            ·
              refine ⟨206391127474911286329283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1100752679866193527089509 206391127474911286329283)
              ·
                refine ⟨309586691212366929493925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206391127474911286329283 309586691212366929493925)
                ·
                  refine ⟨58047504602318799280111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 309586691212366929493925 58047504602318799280111)
                  ·
                    rfl

theorem cell20_127178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_127178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127178 prefixEnd_127178 := by exact prefixLift 127178
  have htrace : WordTrace (prefixWord ++ tailWord_127178) baseStart_127178 baseEnd_127178 := by
    simpa [prefixWord, tailWord_127178, baseEnd_127178] using wordTrace_append hprefix tailTrace_127178
  have hstable : (prefixWord ++ tailWord_127178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127178).length < 2 ^ (prefixWord ++ tailWord_127178).sum := by decide
  have hdescent : baseEnd_127178 < baseStart_127178 := by decide
  rcases family_descends (prefixWord ++ tailWord_127178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127237 : List Nat := [1, 3, 1, 1, 2, 1, 2, 5, 4]
def baseStart_127237 : Nat := 118140960795 + 127237 * 2 ^ 59
def prefixEnd_127237 : Nat := 4983230072969 + 3 ^ 40 * 127237 * 2
def baseEnd_127237 : Nat := 58074433809976816313203

theorem tailTrace_127237 : CollatzResearch.WordTrace tailWord_127237 prefixEnd_127237 58074433809976816313203 := by
  unfold tailWord_127237
  simp only [CollatzResearch.WordTrace]
  refine ⟨4640714640049554194667965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3093809760033036129778643 4640714640049554194667965)
  ·
    refine ⟨1740267990018582823000487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4640714640049554194667965 1740267990018582823000487)
    ·
      refine ⟨2610401985027874234500731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1740267990018582823000487 2610401985027874234500731)
      ·
        refine ⟨3915602977541811351751097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2610401985027874234500731 3915602977541811351751097)
        ·
          refine ⟨2936702233156358513813323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3915602977541811351751097 2936702233156358513813323)
          ·
            refine ⟨4405053349734537770719985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2936702233156358513813323 4405053349734537770719985)
            ·
              refine ⟨3303790012300903328039989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4405053349734537770719985 3303790012300903328039989)
              ·
                refine ⟨309730313653209687003749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3303790012300903328039989 309730313653209687003749)
                ·
                  refine ⟨58074433809976816313203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 309730313653209687003749 58074433809976816313203)
                  ·
                    rfl

theorem cell20_127237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_127237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127237 prefixEnd_127237 := by exact prefixLift 127237
  have htrace : WordTrace (prefixWord ++ tailWord_127237) baseStart_127237 baseEnd_127237 := by
    simpa [prefixWord, tailWord_127237, baseEnd_127237] using wordTrace_append hprefix tailTrace_127237
  have hstable : (prefixWord ++ tailWord_127237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127237).length < 2 ^ (prefixWord ++ tailWord_127237).sum := by decide
  have hdescent : baseEnd_127237 < baseStart_127237 := by decide
  rcases family_descends (prefixWord ++ tailWord_127237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127278 : List Nat := [4, 1, 3, 3, 1, 8]
def baseStart_127278 : Nat := 118140960795 + 127278 * 2 ^ 59
def prefixEnd_127278 : Nat := 4983230072969 + 3 ^ 40 * 127278 * 2
def baseEnd_127278 : Nat := 2151598049154181331347

theorem tailTrace_127278 : CollatzResearch.WordTrace tailWord_127278 prefixEnd_127278 2151598049154181331347 := by
  unfold tailWord_127278
  simp only [CollatzResearch.WordTrace]
  refine ⟨580276254112627274613811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3094806688600678797940325 580276254112627274613811)
  ·
    refine ⟨870414381168940911920717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 580276254112627274613811 870414381168940911920717)
    ·
      refine ⟨326405392938352841970269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 870414381168940911920717 326405392938352841970269)
      ·
        refine ⟨122402022351882315738851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326405392938352841970269 122402022351882315738851)
        ·
          refine ⟨183603033527823473608277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122402022351882315738851 183603033527823473608277)
          ·
            refine ⟨2151598049154181331347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 183603033527823473608277 2151598049154181331347)
            ·
              rfl

theorem cell20_127278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 8].length) (baseStart_127278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127278 prefixEnd_127278 := by exact prefixLift 127278
  have htrace : WordTrace (prefixWord ++ tailWord_127278) baseStart_127278 baseEnd_127278 := by
    simpa [prefixWord, tailWord_127278, baseEnd_127278] using wordTrace_append hprefix tailTrace_127278
  have hstable : (prefixWord ++ tailWord_127278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127278).length < 2 ^ (prefixWord ++ tailWord_127278).sum := by decide
  have hdescent : baseEnd_127278 < baseStart_127278 := by decide
  rcases family_descends (prefixWord ++ tailWord_127278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127282 : List Nat := [3, 2, 1, 1, 13]
def baseStart_127282 : Nat := 118140960795 + 127282 * 2 ^ 59
def prefixEnd_127282 : Nat := 4983230072969 + 3 ^ 40 * 127282 * 2
def baseEnd_127282 : Nat := 717221889335267405099

theorem tailTrace_127282 : CollatzResearch.WordTrace tailWord_127282 prefixEnd_127282 717221889335267405099 := by
  unfold tailWord_127282
  simp only [CollatzResearch.WordTrace]
  refine ⟨1160588981221631720014025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3094903949924351253370733 1160588981221631720014025)
  ·
    refine ⟨870441735916223790010519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1160588981221631720014025 870441735916223790010519)
    ·
      refine ⟨1305662603874335685015779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 870441735916223790010519 1305662603874335685015779)
      ·
        refine ⟨1958493905811503527523669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1305662603874335685015779 1958493905811503527523669)
        ·
          refine ⟨717221889335267405099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 1958493905811503527523669 717221889335267405099)
          ·
            rfl

theorem cell20_127282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 13].length) (baseStart_127282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127282 prefixEnd_127282 := by exact prefixLift 127282
  have htrace : WordTrace (prefixWord ++ tailWord_127282) baseStart_127282 baseEnd_127282 := by
    simpa [prefixWord, tailWord_127282, baseEnd_127282] using wordTrace_append hprefix tailTrace_127282
  have hstable : (prefixWord ++ tailWord_127282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127282).length < 2 ^ (prefixWord ++ tailWord_127282).sum := by decide
  have hdescent : baseEnd_127282 < baseStart_127282 := by decide
  rcases family_descends (prefixWord ++ tailWord_127282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127285 : List Nat := [1, 3, 3, 1, 2, 1, 4, 2, 3]
def baseStart_127285 : Nat := 118140960795 + 127285 * 2 ^ 59
def prefixEnd_127285 : Nat := 4983230072969 + 3 ^ 40 * 127285 * 2
def baseEnd_127285 : Nat := 58096342317901982713007

theorem tailTrace_127285 : CollatzResearch.WordTrace tailWord_127285 prefixEnd_127285 58096342317901982713007 := by
  unfold tailWord_127285
  simp only [CollatzResearch.WordTrace]
  refine ⟨4642465343875658392415309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3094976895917105594943539 4642465343875658392415309)
  ·
    refine ⟨1740924503953371897155741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4642465343875658392415309 1740924503953371897155741)
    ·
      refine ⟨652846688982514461433403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1740924503953371897155741 652846688982514461433403)
      ·
        refine ⟨979270033473771692150105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652846688982514461433403 979270033473771692150105)
        ·
          refine ⟨734452525105328769112579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 979270033473771692150105 734452525105328769112579)
          ·
            refine ⟨1101678787657993153668869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734452525105328769112579 1101678787657993153668869)
            ·
              refine ⟨206564772685873716312913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1101678787657993153668869 206564772685873716312913)
              ·
                refine ⟨154923579514405287234685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206564772685873716312913 154923579514405287234685)
                ·
                  refine ⟨58096342317901982713007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154923579514405287234685 58096342317901982713007)
                  ·
                    rfl

theorem cell20_127285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_127285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127285 prefixEnd_127285 := by exact prefixLift 127285
  have htrace : WordTrace (prefixWord ++ tailWord_127285) baseStart_127285 baseEnd_127285 := by
    simpa [prefixWord, tailWord_127285, baseEnd_127285] using wordTrace_append hprefix tailTrace_127285
  have hstable : (prefixWord ++ tailWord_127285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127285).length < 2 ^ (prefixWord ++ tailWord_127285).sum := by decide
  have hdescent : baseEnd_127285 < baseStart_127285 := by decide
  rcases family_descends (prefixWord ++ tailWord_127285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127313 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 6]
def baseStart_127313 : Nat := 118140960795 + 127313 * 2 ^ 59
def prefixEnd_127313 : Nat := 4983230072969 + 3 ^ 40 * 127313 * 2
def baseEnd_127313 : Nat := 58109122280858329779559

theorem tailTrace_127313 : CollatzResearch.WordTrace tailWord_127313 prefixEnd_127313 58109122280858329779559 := by
  unfold tailWord_127313
  simp only [CollatzResearch.WordTrace]
  refine ⟨4643486587774219174434593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3095657725182812782956395 4643486587774219174434593)
  ·
    refine ⟨3482614940830664380825945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4643486587774219174434593 3482614940830664380825945)
    ·
      refine ⟨2611961205622998285619459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3482614940830664380825945 2611961205622998285619459)
      ·
        refine ⟨3917941808434497428429189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2611961205622998285619459 3917941808434497428429189)
        ·
          refine ⟨734614089081468267830473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3917941808434497428429189 734614089081468267830473)
          ·
            refine ⟨550960566811101200872855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 734614089081468267830473 550960566811101200872855)
            ·
              refine ⟨826440850216651801309283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550960566811101200872855 826440850216651801309283)
              ·
                refine ⟨1239661275324977701963925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 826440850216651801309283 1239661275324977701963925)
                ·
                  refine ⟨58109122280858329779559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1239661275324977701963925 58109122280858329779559)
                  ·
                    rfl

theorem cell20_127313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_127313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127313 prefixEnd_127313 := by exact prefixLift 127313
  have htrace : WordTrace (prefixWord ++ tailWord_127313) baseStart_127313 baseEnd_127313 := by
    simpa [prefixWord, tailWord_127313, baseEnd_127313] using wordTrace_append hprefix tailTrace_127313
  have hstable : (prefixWord ++ tailWord_127313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127313).length < 2 ^ (prefixWord ++ tailWord_127313).sum := by decide
  have hdescent : baseEnd_127313 < baseStart_127313 := by decide
  rcases family_descends (prefixWord ++ tailWord_127313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127316 : List Nat := [2, 4, 1, 1, 2, 3, 3, 4]
def baseStart_127316 : Nat := 118140960795 + 127316 * 2 ^ 59
def prefixEnd_127316 : Nat := 4983230072969 + 3 ^ 40 * 127316 * 2
def baseEnd_127316 : Nat := 19370163854201217559849

theorem tailTrace_127316 : CollatzResearch.WordTrace tailWord_127316 prefixEnd_127316 19370163854201217559849 := by
  unfold tailWord_127316
  simp only [CollatzResearch.WordTrace]
  refine ⟨2321798003381675343396901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3095730671175567124529201 2321798003381675343396901)
  ·
    refine ⟨435337125634064126886919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2321798003381675343396901 435337125634064126886919)
    ·
      refine ⟨653005688451096190330379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435337125634064126886919 653005688451096190330379)
      ·
        refine ⟨979508532676644285495569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653005688451096190330379 979508532676644285495569)
        ·
          refine ⟨734631399507483214121677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 979508532676644285495569 734631399507483214121677)
          ·
            refine ⟨275486774815306205295629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 734631399507483214121677 275486774815306205295629)
            ·
              refine ⟨103307540555739826985861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275486774815306205295629 103307540555739826985861)
              ·
                refine ⟨19370163854201217559849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103307540555739826985861 19370163854201217559849)
                ·
                  rfl

theorem cell20_127316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 4].length) (baseStart_127316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127316 prefixEnd_127316 := by exact prefixLift 127316
  have htrace : WordTrace (prefixWord ++ tailWord_127316) baseStart_127316 baseEnd_127316 := by
    simpa [prefixWord, tailWord_127316, baseEnd_127316] using wordTrace_append hprefix tailTrace_127316
  have hstable : (prefixWord ++ tailWord_127316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127316).length < 2 ^ (prefixWord ++ tailWord_127316).sum := by decide
  have hdescent : baseEnd_127316 < baseStart_127316 := by decide
  rcases family_descends (prefixWord ++ tailWord_127316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127340 : List Nat := [2, 2, 1, 1, 6, 2, 1, 2, 3]
def baseStart_127340 : Nat := 118140960795 + 127340 * 2 ^ 59
def prefixEnd_127340 : Nat := 4983230072969 + 3 ^ 40 * 127340 * 2
def baseEnd_127340 : Nat := 58121445816566235879449

theorem tailTrace_127340 : CollatzResearch.WordTrace tailWord_127340 prefixEnd_127340 58121445816566235879449 := by
  unfold tailWord_127340
  simp only [CollatzResearch.WordTrace]
  refine ⟨2322235679338201392833737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3096314239117601857111649 2322235679338201392833737)
  ·
    refine ⟨1741676759503651044625303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2322235679338201392833737 1741676759503651044625303)
    ·
      refine ⟨2612515139255476566937955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1741676759503651044625303 2612515139255476566937955)
      ·
        refine ⟨3918772708883214850406933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2612515139255476566937955 3918772708883214850406933)
        ·
          refine ⟨183692470728900696112825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3918772708883214850406933 183692470728900696112825)
          ·
            refine ⟨137769353046675522084619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183692470728900696112825 137769353046675522084619)
            ·
              refine ⟨206654029570013283126929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137769353046675522084619 206654029570013283126929)
              ·
                refine ⟨154990522177509962345197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206654029570013283126929 154990522177509962345197)
                ·
                  refine ⟨58121445816566235879449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154990522177509962345197 58121445816566235879449)
                  ·
                    rfl

theorem cell20_127340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_127340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127340 prefixEnd_127340 := by exact prefixLift 127340
  have htrace : WordTrace (prefixWord ++ tailWord_127340) baseStart_127340 baseEnd_127340 := by
    simpa [prefixWord, tailWord_127340, baseEnd_127340] using wordTrace_append hprefix tailTrace_127340
  have hstable : (prefixWord ++ tailWord_127340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127340).length < 2 ^ (prefixWord ++ tailWord_127340).sum := by decide
  have hdescent : baseEnd_127340 < baseStart_127340 := by decide
  rcases family_descends (prefixWord ++ tailWord_127340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127344 : List Nat := [2, 1, 1, 1, 4, 4, 1, 1, 5]
def baseStart_127344 : Nat := 118140960795 + 127344 * 2 ^ 59
def prefixEnd_127344 : Nat := 4983230072969 + 3 ^ 40 * 127344 * 2
def baseEnd_127344 : Nat := 58123271525559999746099

theorem tailTrace_127344 : CollatzResearch.WordTrace tailWord_127344 prefixEnd_127344 58123271525559999746099 := by
  unfold tailWord_127344
  simp only [CollatzResearch.WordTrace]
  refine ⟨2322308625330955734406543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3096411500441274312542057 2322308625330955734406543)
  ·
    refine ⟨3483462937996433601609815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2322308625330955734406543 3483462937996433601609815)
    ·
      refine ⟨5225194406994650402414723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3483462937996433601609815 5225194406994650402414723)
      ·
        refine ⟨7837791610491975603622085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5225194406994650402414723 7837791610491975603622085)
        ·
          refine ⟨1469585926967245425679141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7837791610491975603622085 1469585926967245425679141)
          ·
            refine ⟨275547361306358517314839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1469585926967245425679141 275547361306358517314839)
            ·
              refine ⟨413321041959537775972259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275547361306358517314839 413321041959537775972259)
              ·
                refine ⟨619981562939306663958389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413321041959537775972259 619981562939306663958389)
                ·
                  refine ⟨58123271525559999746099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 619981562939306663958389 58123271525559999746099)
                  ·
                    rfl

theorem cell20_127344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_127344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127344 prefixEnd_127344 := by exact prefixLift 127344
  have htrace : WordTrace (prefixWord ++ tailWord_127344) baseStart_127344 baseEnd_127344 := by
    simpa [prefixWord, tailWord_127344, baseEnd_127344] using wordTrace_append hprefix tailTrace_127344
  have hstable : (prefixWord ++ tailWord_127344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127344).length < 2 ^ (prefixWord ++ tailWord_127344).sum := by decide
  have hdescent : baseEnd_127344 < baseStart_127344 := by decide
  rcases family_descends (prefixWord ++ tailWord_127344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127396 : List Nat := [2, 3, 1, 2, 1, 1, 10]
def baseStart_127396 : Nat := 118140960795 + 127396 * 2 ^ 59
def prefixEnd_127396 : Nat := 4983230072969 + 3 ^ 40 * 127396 * 2
def baseEnd_127396 : Nat := 6460778415830992223617

theorem tailTrace_127396 : CollatzResearch.WordTrace tailWord_127396 prefixEnd_127396 6460778415830992223617 := by
  unfold tailWord_127396
  simp only [CollatzResearch.WordTrace]
  refine ⟨2323256923236762174853021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3097675897649016233137361 2323256923236762174853021)
  ·
    refine ⟨871221346213785815569883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2323256923236762174853021 871221346213785815569883)
    ·
      refine ⟨1306832019320678723354825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 871221346213785815569883 1306832019320678723354825)
      ·
        refine ⟨980124014490509042516119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1306832019320678723354825 980124014490509042516119)
        ·
          refine ⟨1470186021735763563774179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 980124014490509042516119 1470186021735763563774179)
          ·
            refine ⟨2205279032603645345661269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470186021735763563774179 2205279032603645345661269)
            ·
              refine ⟨6460778415830992223617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2205279032603645345661269 6460778415830992223617)
              ·
                rfl

theorem cell20_127396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 10].length) (baseStart_127396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127396 prefixEnd_127396 := by exact prefixLift 127396
  have htrace : WordTrace (prefixWord ++ tailWord_127396) baseStart_127396 baseEnd_127396 := by
    simpa [prefixWord, tailWord_127396, baseEnd_127396] using wordTrace_append hprefix tailTrace_127396
  have hstable : (prefixWord ++ tailWord_127396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127396).length < 2 ^ (prefixWord ++ tailWord_127396).sum := by decide
  have hdescent : baseEnd_127396 < baseStart_127396 := by decide
  rcases family_descends (prefixWord ++ tailWord_127396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127434 : List Nat := [3, 1, 2, 1, 2, 2, 1, 8]
def baseStart_127434 : Nat := 118140960795 + 127434 * 2 ^ 59
def prefixEnd_127434 : Nat := 4983230072969 + 3 ^ 40 * 127434 * 2
def baseEnd_127434 : Nat := 19388116659306562248577

theorem tailTrace_127434 : CollatzResearch.WordTrace tailWord_127434 prefixEnd_127434 19388116659306562248577 := by
  unfold tailWord_127434
  simp only [CollatzResearch.WordTrace]
  refine ⟨1161974955083964209897339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3098599880223904559726237 1161974955083964209897339)
  ·
    refine ⟨1742962432625946314846009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1161974955083964209897339 1742962432625946314846009)
    ·
      refine ⟨1307221824469459736134507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1742962432625946314846009 1307221824469459736134507)
      ·
        refine ⟨1960832736704189604201761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1307221824469459736134507 1960832736704189604201761)
        ·
          refine ⟨1470624552528142203151321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1960832736704189604201761 1470624552528142203151321)
          ·
            refine ⟨1102968414396106652363491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1470624552528142203151321 1102968414396106652363491)
            ·
              refine ⟨1654452621594159978545237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1102968414396106652363491 1654452621594159978545237)
              ·
                refine ⟨19388116659306562248577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1654452621594159978545237 19388116659306562248577)
                ·
                  rfl

theorem cell20_127434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_127434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127434 prefixEnd_127434 := by exact prefixLift 127434
  have htrace : WordTrace (prefixWord ++ tailWord_127434) baseStart_127434 baseEnd_127434 := by
    simpa [prefixWord, tailWord_127434, baseEnd_127434] using wordTrace_append hprefix tailTrace_127434
  have hstable : (prefixWord ++ tailWord_127434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127434).length < 2 ^ (prefixWord ++ tailWord_127434).sum := by decide
  have hdescent : baseEnd_127434 < baseStart_127434 := by decide
  rcases family_descends (prefixWord ++ tailWord_127434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127441 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 7]
def baseStart_127441 : Nat := 118140960795 + 127441 * 2 ^ 59
def prefixEnd_127441 : Nat := 4983230072969 + 3 ^ 40 * 127441 * 2
def baseEnd_127441 : Nat := 58167544968658773512369

theorem tailTrace_127441 : CollatzResearch.WordTrace tailWord_127441 prefixEnd_127441 58167544968658773512369 := by
  unfold tailWord_127441
  simp only [CollatzResearch.WordTrace]
  refine ⟨4648155131310497035094177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3098770087540331356729451 4648155131310497035094177)
  ·
    refine ⟨3486116348482872776320633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4648155131310497035094177 3486116348482872776320633)
    ·
      refine ⟨2614587261362154582240475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3486116348482872776320633 2614587261362154582240475)
      ·
        refine ⟨3921880892043231873360713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2614587261362154582240475 3921880892043231873360713)
        ·
          refine ⟨2941410669032423905020535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3921880892043231873360713 2941410669032423905020535)
          ·
            refine ⟨4412116003548635857530803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2941410669032423905020535 4412116003548635857530803)
            ·
              refine ⟨6618174005322953786296205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4412116003548635857530803 6618174005322953786296205)
              ·
                refine ⟨2481815251996107669861077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6618174005322953786296205 2481815251996107669861077)
                ·
                  refine ⟨58167544968658773512369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2481815251996107669861077 58167544968658773512369)
                  ·
                    rfl

theorem cell20_127441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_127441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127441 prefixEnd_127441 := by exact prefixLift 127441
  have htrace : WordTrace (prefixWord ++ tailWord_127441) baseStart_127441 baseEnd_127441 := by
    simpa [prefixWord, tailWord_127441, baseEnd_127441] using wordTrace_append hprefix tailTrace_127441
  have hstable : (prefixWord ++ tailWord_127441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127441).length < 2 ^ (prefixWord ++ tailWord_127441).sum := by decide
  have hdescent : baseEnd_127441 < baseStart_127441 := by decide
  rcases family_descends (prefixWord ++ tailWord_127441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127499 : List Nat := [1, 1, 1, 1, 7, 2, 2, 3, 2]
def baseStart_127499 : Nat := 118140960795 + 127499 * 2 ^ 59
def prefixEnd_127499 : Nat := 4983230072969 + 3 ^ 40 * 127499 * 2
def baseEnd_127499 : Nat := 58194017749068349578799

theorem tailTrace_127499 : CollatzResearch.WordTrace tailWord_127499 prefixEnd_127499 58194017749068349578799 := by
  unfold tailWord_127499
  simp only [CollatzResearch.WordTrace]
  refine ⟨4650270565100372940705551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3100180376733581960470367 4650270565100372940705551)
  ·
    refine ⟨6975405847650559411058327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4650270565100372940705551 6975405847650559411058327)
    ·
      refine ⟨10463108771475839116587491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6975405847650559411058327 10463108771475839116587491)
      ·
        refine ⟨15694663157213758674881237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10463108771475839116587491 15694663157213758674881237)
        ·
          refine ⟨367843667747197468942529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 15694663157213758674881237 367843667747197468942529)
          ·
            refine ⟨275882750810398101706897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367843667747197468942529 275882750810398101706897)
            ·
              refine ⟨206912063107798576280173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275882750810398101706897 206912063107798576280173)
              ·
                refine ⟨77592023665424466105065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206912063107798576280173 77592023665424466105065)
                ·
                  refine ⟨58194017749068349578799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77592023665424466105065 58194017749068349578799)
                  ·
                    rfl

theorem cell20_127499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 3, 2].length) (baseStart_127499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127499 prefixEnd_127499 := by exact prefixLift 127499
  have htrace : WordTrace (prefixWord ++ tailWord_127499) baseStart_127499 baseEnd_127499 := by
    simpa [prefixWord, tailWord_127499, baseEnd_127499] using wordTrace_append hprefix tailTrace_127499
  have hstable : (prefixWord ++ tailWord_127499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127499).length < 2 ^ (prefixWord ++ tailWord_127499).sum := by decide
  have hdescent : baseEnd_127499 < baseStart_127499 := by decide
  rcases family_descends (prefixWord ++ tailWord_127499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127530 : List Nat := [3, 1, 4, 1, 1, 3, 3, 1, 3]
def baseStart_127530 : Nat := 118140960795 + 127530 * 2 ^ 59
def prefixEnd_127530 : Nat := 4983230072969 + 3 ^ 40 * 127530 * 2
def baseEnd_127530 : Nat := 58208166993770019545339

theorem tailTrace_127530 : CollatzResearch.WordTrace tailWord_127530 prefixEnd_127530 58208166993770019545339 := by
  unfold tailWord_127530
  simp only [CollatzResearch.WordTrace]
  refine ⟨1162850306997016308771011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3100934151992043490056029 1162850306997016308771011)
  ·
    refine ⟨1744275460495524463156517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1162850306997016308771011 1744275460495524463156517)
    ·
      refine ⟨327051648842910836841847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1744275460495524463156517 327051648842910836841847)
      ·
        refine ⟨490577473264366255262771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327051648842910836841847 490577473264366255262771)
        ·
          refine ⟨735866209896549382894157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490577473264366255262771 735866209896549382894157)
          ·
            refine ⟨275949828711206018585309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 735866209896549382894157 275949828711206018585309)
            ·
              refine ⟨103481185766702256969491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275949828711206018585309 103481185766702256969491)
              ·
                refine ⟨155221778650053385454237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103481185766702256969491 155221778650053385454237)
                ·
                  refine ⟨58208166993770019545339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155221778650053385454237 58208166993770019545339)
                  ·
                    rfl

theorem cell20_127530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_127530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127530 prefixEnd_127530 := by exact prefixLift 127530
  have htrace : WordTrace (prefixWord ++ tailWord_127530) baseStart_127530 baseEnd_127530 := by
    simpa [prefixWord, tailWord_127530, baseEnd_127530] using wordTrace_append hprefix tailTrace_127530
  have hstable : (prefixWord ++ tailWord_127530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127530).length < 2 ^ (prefixWord ++ tailWord_127530).sum := by decide
  have hdescent : baseEnd_127530 < baseStart_127530 := by decide
  rcases family_descends (prefixWord ++ tailWord_127530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127540 : List Nat := [2, 5, 1, 3, 1, 2, 2, 4]
def baseStart_127540 : Nat := 118140960795 + 127540 * 2 ^ 59
def prefixEnd_127540 : Nat := 4983230072969 + 3 ^ 40 * 127540 * 2
def baseEnd_127540 : Nat := 19404243755418143070655

theorem tailTrace_127540 : CollatzResearch.WordTrace tailWord_127540 prefixEnd_127540 19404243755418143070655 := by
  unfold tailWord_127540
  simp only [CollatzResearch.WordTrace]
  refine ⟨2325882978975918471474037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3101177305301224628632049 2325882978975918471474037)
  ·
    refine ⟨218051529278992356700691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2325882978975918471474037 218051529278992356700691)
    ·
      refine ⟨327077293918488535051037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218051529278992356700691 327077293918488535051037)
      ·
        refine ⟨122653985219433200644139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327077293918488535051037 122653985219433200644139)
        ·
          refine ⟨183980977829149800966209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122653985219433200644139 183980977829149800966209)
          ·
            refine ⟨137985733371862350724657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183980977829149800966209 137985733371862350724657)
            ·
              refine ⟨103489300028896763043493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137985733371862350724657 103489300028896763043493)
              ·
                refine ⟨19404243755418143070655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103489300028896763043493 19404243755418143070655)
                ·
                  rfl

theorem cell20_127540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 4].length) (baseStart_127540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127540 prefixEnd_127540 := by exact prefixLift 127540
  have htrace : WordTrace (prefixWord ++ tailWord_127540) baseStart_127540 baseEnd_127540 := by
    simpa [prefixWord, tailWord_127540, baseEnd_127540] using wordTrace_append hprefix tailTrace_127540
  have hstable : (prefixWord ++ tailWord_127540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127540).length < 2 ^ (prefixWord ++ tailWord_127540).sum := by decide
  have hdescent : baseEnd_127540 < baseStart_127540 := by decide
  rcases family_descends (prefixWord ++ tailWord_127540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127541 : List Nat := [1, 3, 3, 1, 1, 2, 1, 4, 4]
def baseStart_127541 : Nat := 118140960795 + 127541 * 2 ^ 59
def prefixEnd_127541 : Nat := 4983230072969 + 3 ^ 40 * 127541 * 2
def baseEnd_127541 : Nat := 58213187693502870178627

theorem tailTrace_127541 : CollatzResearch.WordTrace tailWord_127541 prefixEnd_127541 58213187693502870178627 := by
  unfold tailWord_127541
  simp only [CollatzResearch.WordTrace]
  refine ⟨4651802430948214113734477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3101201620632142742489651 4651802430948214113734477)
  ·
    refine ⟨1744425911605580292650429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4651802430948214113734477 1744425911605580292650429)
    ·
      refine ⟨654159716852092609743911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1744425911605580292650429 654159716852092609743911)
      ·
        refine ⟨981239575278138914615867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654159716852092609743911 981239575278138914615867)
        ·
          refine ⟨1471859362917208371923801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 981239575278138914615867 1471859362917208371923801)
          ·
            refine ⟨1103894522187906278942851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1471859362917208371923801 1103894522187906278942851)
            ·
              refine ⟨1655841783281859418414277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1103894522187906278942851 1655841783281859418414277)
              ·
                refine ⟨310470334365348640952677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1655841783281859418414277 310470334365348640952677)
                ·
                  refine ⟨58213187693502870178627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 310470334365348640952677 58213187693502870178627)
                  ·
                    rfl

theorem cell20_127541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_127541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127541 prefixEnd_127541 := by exact prefixLift 127541
  have htrace : WordTrace (prefixWord ++ tailWord_127541) baseStart_127541 baseEnd_127541 := by
    simpa [prefixWord, tailWord_127541, baseEnd_127541] using wordTrace_append hprefix tailTrace_127541
  have hstable : (prefixWord ++ tailWord_127541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127541).length < 2 ^ (prefixWord ++ tailWord_127541).sum := by decide
  have hdescent : baseEnd_127541 < baseStart_127541 := by decide
  rcases family_descends (prefixWord ++ tailWord_127541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127550 : List Nat := [4, 2, 1, 4, 2, 1, 1, 3, 2]
def baseStart_127550 : Nat := 118140960795 + 127550 * 2 ^ 59
def prefixEnd_127550 : Nat := 4983230072969 + 3 ^ 40 * 127550 * 2
def baseEnd_127550 : Nat := 58217295538738838878591

theorem tailTrace_127550 : CollatzResearch.WordTrace tailWord_127550 prefixEnd_127550 58217295538738838878591 := by
  unfold tailWord_127550
  simp only [CollatzResearch.WordTrace]
  refine ⟨581516335989451081351513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3101420458610405767208069 581516335989451081351513)
  ·
    refine ⟨436137251992088311013635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 581516335989451081351513 436137251992088311013635)
    ·
      refine ⟨654205877988132466520453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436137251992088311013635 654205877988132466520453)
      ·
        refine ⟨122663602122774837472585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 654205877988132466520453 122663602122774837472585)
        ·
          refine ⟨91997701592081128104439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122663602122774837472585 91997701592081128104439)
          ·
            refine ⟨137996552388121692156659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91997701592081128104439 137996552388121692156659)
            ·
              refine ⟨206994828582182538234989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137996552388121692156659 206994828582182538234989)
              ·
                refine ⟨77623060718318451838121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206994828582182538234989 77623060718318451838121)
                ·
                  refine ⟨58217295538738838878591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77623060718318451838121 58217295538738838878591)
                  ·
                    rfl

theorem cell20_127550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_127550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127550 prefixEnd_127550 := by exact prefixLift 127550
  have htrace : WordTrace (prefixWord ++ tailWord_127550) baseStart_127550 baseEnd_127550 := by
    simpa [prefixWord, tailWord_127550, baseEnd_127550] using wordTrace_append hprefix tailTrace_127550
  have hstable : (prefixWord ++ tailWord_127550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127550).length < 2 ^ (prefixWord ++ tailWord_127550).sum := by decide
  have hdescent : baseEnd_127550 < baseStart_127550 := by decide
  rcases family_descends (prefixWord ++ tailWord_127550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127565 : List Nat := [1, 6, 1, 1, 2, 1, 8]
def baseStart_127565 : Nat := 118140960795 + 127565 * 2 ^ 59
def prefixEnd_127565 : Nat := 4983230072969 + 3 ^ 40 * 127565 * 2
def baseEnd_127565 : Nat := 6469349105273939264281

theorem tailTrace_127565 : CollatzResearch.WordTrace tailWord_127565 prefixEnd_127565 6469349105273939264281 := by
  unfold tailWord_127565
  simp only [CollatzResearch.WordTrace]
  refine ⟨4652677782861266212608149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3101785188574177475072099 4652677782861266212608149)
  ·
    refine ⟨218094271071621853716007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4652677782861266212608149 218094271071621853716007)
    ·
      refine ⟨327141406607432780574011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218094271071621853716007 327141406607432780574011)
      ·
        refine ⟨490712109911149170861017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327141406607432780574011 490712109911149170861017)
        ·
          refine ⟨368034082433361878145763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490712109911149170861017 368034082433361878145763)
          ·
            refine ⟨552051123650042817218645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368034082433361878145763 552051123650042817218645)
            ·
              refine ⟨6469349105273939264281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 552051123650042817218645 6469349105273939264281)
              ·
                rfl

theorem cell20_127565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 8].length) (baseStart_127565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127565 prefixEnd_127565 := by exact prefixLift 127565
  have htrace : WordTrace (prefixWord ++ tailWord_127565) baseStart_127565 baseEnd_127565 := by
    simpa [prefixWord, tailWord_127565, baseEnd_127565] using wordTrace_append hprefix tailTrace_127565
  have hstable : (prefixWord ++ tailWord_127565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127565).length < 2 ^ (prefixWord ++ tailWord_127565).sum := by decide
  have hdescent : baseEnd_127565 < baseStart_127565 := by decide
  rcases family_descends (prefixWord ++ tailWord_127565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127572 : List Nat := [2, 4, 1, 1, 1, 3, 2, 1, 5]
def baseStart_127572 : Nat := 118140960795 + 127572 * 2 ^ 59
def prefixEnd_127572 : Nat := 4983230072969 + 3 ^ 40 * 127572 * 2
def baseEnd_127572 : Nat := 58227336938204540145167

theorem tailTrace_127572 : CollatzResearch.WordTrace tailWord_127572 prefixEnd_127572 58227336938204540145167 := by
  unfold tailWord_127572
  simp only [CollatzResearch.WordTrace]
  refine ⟨2326466546917953204056485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3101955395890604272075313 2326466546917953204056485)
  ·
    refine ⟨436212477547116225760591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2326466546917953204056485 436212477547116225760591)
    ·
      refine ⟨654318716320674338640887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436212477547116225760591 654318716320674338640887)
      ·
        refine ⟨981478074481011507961331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654318716320674338640887 981478074481011507961331)
        ·
          refine ⟨1472217111721517261941997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 981478074481011507961331 1472217111721517261941997)
          ·
            refine ⟨552081416895568973228249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1472217111721517261941997 552081416895568973228249)
            ·
              refine ⟨414061062671676729921187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 552081416895568973228249 414061062671676729921187)
              ·
                refine ⟨621091594007515094881781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414061062671676729921187 621091594007515094881781)
                ·
                  refine ⟨58227336938204540145167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 621091594007515094881781 58227336938204540145167)
                  ·
                    rfl

theorem cell20_127572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_127572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127572 prefixEnd_127572 := by exact prefixLift 127572
  have htrace : WordTrace (prefixWord ++ tailWord_127572) baseStart_127572 baseEnd_127572 := by
    simpa [prefixWord, tailWord_127572, baseEnd_127572] using wordTrace_append hprefix tailTrace_127572
  have hstable : (prefixWord ++ tailWord_127572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127572).length < 2 ^ (prefixWord ++ tailWord_127572).sum := by decide
  have hdescent : baseEnd_127572 < baseStart_127572 := by decide
  rcases family_descends (prefixWord ++ tailWord_127572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
