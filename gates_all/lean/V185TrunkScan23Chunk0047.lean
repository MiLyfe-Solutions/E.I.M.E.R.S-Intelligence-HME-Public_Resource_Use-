import V185TrunkScan23Chunk0046

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_278297 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 8]
def baseStart_278297 : Nat := 118140960795 + 278297 * 2 ^ 59
def prefixEnd_278297 : Nat := 4983230072969 + 3 ^ 40 * 278297 * 2
def baseEnd_278297 : Nat := 142900125704402895407641

theorem tailTrace_278297 : CollatzResearch.WordTrace tailWord_278297 prefixEnd_278297 142900125704402895407641 := by
  unfold tailWord_278297
  simp only [CollatzResearch.WordTrace]
  refine ⟨10150325472784973188705145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6766883648523315459136763 10150325472784973188705145)
  ·
    refine ⟨7612744104588729891528859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10150325472784973188705145 7612744104588729891528859)
    ·
      refine ⟨11419116156883094837293289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7612744104588729891528859 11419116156883094837293289)
      ·
        refine ⟨8564337117662321127969967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11419116156883094837293289 8564337117662321127969967)
        ·
          refine ⟨12846505676493481691954951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8564337117662321127969967 12846505676493481691954951)
          ·
            refine ⟨19269758514740222537932427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12846505676493481691954951 19269758514740222537932427)
            ·
              refine ⟨28904637772110333806898641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19269758514740222537932427 28904637772110333806898641)
              ·
                refine ⟨21678478329082750355173981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28904637772110333806898641 21678478329082750355173981)
                ·
                  refine ⟨8129429373406031383190243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21678478329082750355173981 8129429373406031383190243)
                  ·
                    refine ⟨12194144060109047074785365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8129429373406031383190243 12194144060109047074785365)
                    ·
                      refine ⟨142900125704402895407641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 12194144060109047074785365 142900125704402895407641)
                      ·
                        rfl

theorem cell23_278297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_278297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278297 prefixEnd_278297 := by exact prefixLift 278297
  have htrace : WordTrace (prefixWord ++ tailWord_278297) baseStart_278297 baseEnd_278297 := by
    simpa [prefixWord, tailWord_278297, baseEnd_278297] using wordTrace_append hprefix tailTrace_278297
  have hstable : (prefixWord ++ tailWord_278297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278297).length < 2 ^ (prefixWord ++ tailWord_278297).sum := by decide
  have hdescent : baseEnd_278297 < baseStart_278297 := by decide
  rcases family_descends (prefixWord ++ tailWord_278297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278308 : List Nat := [2, 3, 1, 3, 2, 2, 2, 1, 2, 2, 3]
def baseStart_278308 : Nat := 118140960795 + 278308 * 2 ^ 59
def prefixEnd_278308 : Nat := 4983230072969 + 3 ^ 40 * 278308 * 2
def baseEnd_278308 : Nat := 142905773991602352370091

theorem tailTrace_278308 : CollatzResearch.WordTrace tailWord_278308 prefixEnd_278308 142905773991602352370091 := by
  unfold tailWord_278308
  simp only [CollatzResearch.WordTrace]
  refine ⟨5075363337872561033677789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6767151117163414711570385 5075363337872561033677789)
  ·
    refine ⟨1903261251702210387629171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5075363337872561033677789 1903261251702210387629171)
    ·
      refine ⟨2854891877553315581443757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1903261251702210387629171 2854891877553315581443757)
      ·
        refine ⟨1070584454082493343041409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2854891877553315581443757 1070584454082493343041409)
        ·
          refine ⟨802938340561870007281057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1070584454082493343041409 802938340561870007281057)
          ·
            refine ⟨602203755421402505460793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 802938340561870007281057 602203755421402505460793)
            ·
              refine ⟨451652816566051879095595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 602203755421402505460793 451652816566051879095595)
              ·
                refine ⟨677479224849077818643393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 451652816566051879095595 677479224849077818643393)
                ·
                  refine ⟨508109418636808363982545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 677479224849077818643393 508109418636808363982545)
                  ·
                    refine ⟨381082063977606272986909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 508109418636808363982545 381082063977606272986909)
                    ·
                      refine ⟨142905773991602352370091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 381082063977606272986909 142905773991602352370091)
                      ·
                        rfl

theorem cell23_278308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_278308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278308 prefixEnd_278308 := by exact prefixLift 278308
  have htrace : WordTrace (prefixWord ++ tailWord_278308) baseStart_278308 baseEnd_278308 := by
    simpa [prefixWord, tailWord_278308, baseEnd_278308] using wordTrace_append hprefix tailTrace_278308
  have hstable : (prefixWord ++ tailWord_278308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278308).length < 2 ^ (prefixWord ++ tailWord_278308).sum := by decide
  have hdescent : baseEnd_278308 < baseStart_278308 := by decide
  rcases family_descends (prefixWord ++ tailWord_278308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278361 : List Nat := [1, 2, 1, 2, 2, 3, 2, 4, 1, 1, 4]
def baseStart_278361 : Nat := 118140960795 + 278361 * 2 ^ 59
def prefixEnd_278361 : Nat := 4983230072969 + 3 ^ 40 * 278361 * 2
def baseEnd_278361 : Nat := 142932988466290645007347

theorem tailTrace_278361 : CollatzResearch.WordTrace tailWord_278361 prefixEnd_278361 142932988466290645007347 := by
  unfold tailWord_278361
  simp only [CollatzResearch.WordTrace]
  refine ⟨10152659744553112119034937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6768439829702074746023291 10152659744553112119034937)
  ·
    refine ⟨7614494808414834089276203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10152659744553112119034937 7614494808414834089276203)
    ·
      refine ⟨11421742212622251133914305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7614494808414834089276203 11421742212622251133914305)
      ·
        refine ⟨8566306659466688350435729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11421742212622251133914305 8566306659466688350435729)
        ·
          refine ⟨6424729994600016262826797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8566306659466688350435729 6424729994600016262826797)
          ·
            refine ⟨2409273747975006098560049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6424729994600016262826797 2409273747975006098560049)
            ·
              refine ⟨1806955310981254573920037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2409273747975006098560049 1806955310981254573920037)
              ·
                refine ⟨338804120808985232610007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1806955310981254573920037 338804120808985232610007)
                ·
                  refine ⟨508206181213477848915011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 338804120808985232610007 508206181213477848915011)
                  ·
                    refine ⟨762309271820216773372517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 508206181213477848915011 762309271820216773372517)
                    ·
                      refine ⟨142932988466290645007347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 762309271820216773372517 142932988466290645007347)
                      ·
                        rfl

theorem cell23_278361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 1, 4].length) (baseStart_278361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278361 prefixEnd_278361 := by exact prefixLift 278361
  have htrace : WordTrace (prefixWord ++ tailWord_278361) baseStart_278361 baseEnd_278361 := by
    simpa [prefixWord, tailWord_278361, baseEnd_278361] using wordTrace_append hprefix tailTrace_278361
  have hstable : (prefixWord ++ tailWord_278361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278361).length < 2 ^ (prefixWord ++ tailWord_278361).sum := by decide
  have hdescent : baseEnd_278361 < baseStart_278361 := by decide
  rcases family_descends (prefixWord ++ tailWord_278361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278372 : List Nat := [2, 3, 1, 1, 5, 1, 2, 3, 1, 1, 3]
def baseStart_278372 : Nat := 118140960795 + 278372 * 2 ^ 59
def prefixEnd_278372 : Nat := 4983230072969 + 3 ^ 40 * 278372 * 2
def baseEnd_278372 : Nat := 142938636753490101969797

theorem tailTrace_278372 : CollatzResearch.WordTrace tailWord_278372 prefixEnd_278372 142938636753490101969797 := by
  unfold tailWord_278372
  simp only [CollatzResearch.WordTrace]
  refine ⟨5076530473756630498842685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6768707298342173998456913 5076530473756630498842685)
  ·
    refine ⟨1903698927658736437066007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5076530473756630498842685 1903698927658736437066007)
    ·
      refine ⟨2855548391488104655599011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1903698927658736437066007 2855548391488104655599011)
      ·
        refine ⟨4283322587232156983398517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2855548391488104655599011 4283322587232156983398517)
        ·
          refine ⟨401561492553014717193611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4283322587232156983398517 401561492553014717193611)
          ·
            refine ⟨602342238829522075790417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401561492553014717193611 602342238829522075790417)
            ·
              refine ⟨451756679122141556842813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 602342238829522075790417 451756679122141556842813)
              ·
                refine ⟨169408754670803083816055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 451756679122141556842813 169408754670803083816055)
                ·
                  refine ⟨254113132006204625724083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169408754670803083816055 254113132006204625724083)
                  ·
                    refine ⟨381169698009306938586125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 254113132006204625724083 381169698009306938586125)
                    ·
                      refine ⟨142938636753490101969797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 381169698009306938586125 142938636753490101969797)
                      ·
                        rfl

theorem cell23_278372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 3, 1, 1, 3].length) (baseStart_278372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278372 prefixEnd_278372 := by exact prefixLift 278372
  have htrace : WordTrace (prefixWord ++ tailWord_278372) baseStart_278372 baseEnd_278372 := by
    simpa [prefixWord, tailWord_278372, baseEnd_278372] using wordTrace_append hprefix tailTrace_278372
  have hstable : (prefixWord ++ tailWord_278372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278372).length < 2 ^ (prefixWord ++ tailWord_278372).sum := by decide
  have hdescent : baseEnd_278372 < baseStart_278372 := by decide
  rcases family_descends (prefixWord ++ tailWord_278372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278398 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_278398 : Nat := 118140960795 + 278398 * 2 ^ 59
def prefixEnd_278398 : Nat := 4983230072969 + 3 ^ 40 * 278398 * 2
def baseEnd_278398 : Nat := 142951987250507000244677

theorem tailTrace_278398 : CollatzResearch.WordTrace tailWord_278398 prefixEnd_278398 142951987250507000244677 := by
  unfold tailWord_278398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1269251155677383429766481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6769339496946044958754565 1269251155677383429766481)
  ·
    refine ⟨951938366758037572324861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1269251155677383429766481 951938366758037572324861)
    ·
      refine ⟨356976887534264089621823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 951938366758037572324861 356976887534264089621823)
      ·
        refine ⟨535465331301396134432735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356976887534264089621823 535465331301396134432735)
        ·
          refine ⟨803197996952094201649103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 535465331301396134432735 803197996952094201649103)
          ·
            refine ⟨1204796995428141302473655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 803197996952094201649103 1204796995428141302473655)
            ·
              refine ⟨1807195493142211953710483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1204796995428141302473655 1807195493142211953710483)
              ·
                refine ⟨2710793239713317930565725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1807195493142211953710483 2710793239713317930565725)
                ·
                  refine ⟨1016547464892494223962147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2710793239713317930565725 1016547464892494223962147)
                  ·
                    refine ⟨1524821197338741335943221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1016547464892494223962147 1524821197338741335943221)
                    ·
                      refine ⟨142951987250507000244677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1524821197338741335943221 142951987250507000244677)
                      ·
                        rfl

theorem cell23_278398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_278398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278398 prefixEnd_278398 := by exact prefixLift 278398
  have htrace : WordTrace (prefixWord ++ tailWord_278398) baseStart_278398 baseEnd_278398 := by
    simpa [prefixWord, tailWord_278398, baseEnd_278398] using wordTrace_append hprefix tailTrace_278398
  have hstable : (prefixWord ++ tailWord_278398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278398).length < 2 ^ (prefixWord ++ tailWord_278398).sum := by decide
  have hdescent : baseEnd_278398 < baseStart_278398 := by decide
  rcases family_descends (prefixWord ++ tailWord_278398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278418 : List Nat := [3, 2, 3, 2, 1, 1, 4, 7]
def baseStart_278418 : Nat := 118140960795 + 278418 * 2 ^ 59
def prefixEnd_278418 : Nat := 4983230072969 + 3 ^ 40 * 278418 * 2
def baseEnd_278418 : Nat := 5294898402355441555355

theorem tailTrace_278418 : CollatzResearch.WordTrace tailWord_278418 prefixEnd_278418 5294898402355441555355 := by
  unfold tailWord_278418
  simp only [CollatzResearch.WordTrace]
  refine ⟨2538684676336652713464977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6769825803564407235906605 2538684676336652713464977)
  ·
    refine ⟨1904013507252489535098733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2538684676336652713464977 1904013507252489535098733)
    ·
      refine ⟨714005065219683575662025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1904013507252489535098733 714005065219683575662025)
      ·
        refine ⟨535503798914762681746519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 714005065219683575662025 535503798914762681746519)
        ·
          refine ⟨803255698372144022619779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 535503798914762681746519 803255698372144022619779)
          ·
            refine ⟨1204883547558216033929669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 803255698372144022619779 1204883547558216033929669)
            ·
              refine ⟨225915665167165506361813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1204883547558216033929669 225915665167165506361813)
              ·
                refine ⟨5294898402355441555355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 225915665167165506361813 5294898402355441555355)
                ·
                  rfl

theorem cell23_278418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 7].length) (baseStart_278418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278418 prefixEnd_278418 := by exact prefixLift 278418
  have htrace : WordTrace (prefixWord ++ tailWord_278418) baseStart_278418 baseEnd_278418 := by
    simpa [prefixWord, tailWord_278418, baseEnd_278418] using wordTrace_append hprefix tailTrace_278418
  have hstable : (prefixWord ++ tailWord_278418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278418).length < 2 ^ (prefixWord ++ tailWord_278418).sum := by decide
  have hdescent : baseEnd_278418 < baseStart_278418 := by decide
  rcases family_descends (prefixWord ++ tailWord_278418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278429 : List Nat := [1, 4, 2, 1, 2, 4, 1, 3, 1, 2, 2]
def baseStart_278429 : Nat := 118140960795 + 278429 * 2 ^ 59
def prefixEnd_278429 : Nat := 4983230072969 + 3 ^ 40 * 278429 * 2
def baseEnd_278429 : Nat := 142967905150796378957035

theorem tailTrace_278429 : CollatzResearch.WordTrace tailWord_278429 prefixEnd_278429 142967905150796378957035 := by
  unfold tailWord_278429
  simp only [CollatzResearch.WordTrace]
  refine ⟨10155139908306759732510341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6770093272204506488340227 10155139908306759732510341)
  ·
    refine ⟨1904088732807517449845689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10155139908306759732510341 1904088732807517449845689)
    ·
      refine ⟨1428066549605638087384267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1904088732807517449845689 1428066549605638087384267)
      ·
        refine ⟨2142099824408457131076401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1428066549605638087384267 2142099824408457131076401)
        ·
          refine ⟨1606574868306342848307301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2142099824408457131076401 1606574868306342848307301)
          ·
            refine ⟨301232787807439284057619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1606574868306342848307301 301232787807439284057619)
            ·
              refine ⟨451849181711158926086429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301232787807439284057619 451849181711158926086429)
              ·
                refine ⟨169443443141684597282411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 451849181711158926086429 169443443141684597282411)
                ·
                  refine ⟨254165164712526895923617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169443443141684597282411 254165164712526895923617)
                  ·
                    refine ⟨190623873534395171942713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 254165164712526895923617 190623873534395171942713)
                    ·
                      refine ⟨142967905150796378957035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 190623873534395171942713 142967905150796378957035)
                      ·
                        rfl

theorem cell23_278429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_278429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278429 prefixEnd_278429 := by exact prefixLift 278429
  have htrace : WordTrace (prefixWord ++ tailWord_278429) baseStart_278429 baseEnd_278429 := by
    simpa [prefixWord, tailWord_278429, baseEnd_278429] using wordTrace_append hprefix tailTrace_278429
  have hstable : (prefixWord ++ tailWord_278429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278429).length < 2 ^ (prefixWord ++ tailWord_278429).sum := by decide
  have hdescent : baseEnd_278429 < baseStart_278429 := by decide
  rcases family_descends (prefixWord ++ tailWord_278429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278462 : List Nat := [4, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3]
def baseStart_278462 : Nat := 118140960795 + 278462 * 2 ^ 59
def prefixEnd_278462 : Nat := 4983230072969 + 3 ^ 40 * 278462 * 2
def baseEnd_278462 : Nat := 142984850012394749844383

theorem tailTrace_278462 : CollatzResearch.WordTrace tailWord_278462 prefixEnd_278462 142984850012394749844383 := by
  unfold tailWord_278462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1269542939648400796057705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6770895678124804245641093 1269542939648400796057705)
  ·
    refine ⟨952157204736300597043279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1269542939648400796057705 952157204736300597043279)
    ·
      refine ⟨1428235807104450895564919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 952157204736300597043279 1428235807104450895564919)
      ·
        refine ⟨2142353710656676343347379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1428235807104450895564919 2142353710656676343347379)
        ·
          refine ⟨3213530565985014515021069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2142353710656676343347379 3213530565985014515021069)
          ·
            refine ⟨1205073962244380443132901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3213530565985014515021069 1205073962244380443132901)
            ·
              refine ⟨225951367920821333087419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1205073962244380443132901 225951367920821333087419)
              ·
                refine ⟨338927051881231999631129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225951367920821333087419 338927051881231999631129)
                ·
                  refine ⟨254195288910923999723347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 338927051881231999631129 254195288910923999723347)
                  ·
                    refine ⟨381292933366385999585021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 254195288910923999723347 381292933366385999585021)
                    ·
                      refine ⟨142984850012394749844383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 381292933366385999585021 142984850012394749844383)
                      ·
                        rfl

theorem cell23_278462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_278462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278462 prefixEnd_278462 := by exact prefixLift 278462
  have htrace : WordTrace (prefixWord ++ tailWord_278462) baseStart_278462 baseEnd_278462 := by
    simpa [prefixWord, tailWord_278462, baseEnd_278462] using wordTrace_append hprefix tailTrace_278462
  have hstable : (prefixWord ++ tailWord_278462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278462).length < 2 ^ (prefixWord ++ tailWord_278462).sum := by decide
  have hdescent : baseEnd_278462 < baseStart_278462 := by decide
  rcases family_descends (prefixWord ++ tailWord_278462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278472 : List Nat := [2, 1, 3, 1, 4, 3, 1, 2, 1, 3, 2]
def baseStart_278472 : Nat := 118140960795 + 278472 * 2 ^ 59
def prefixEnd_278472 : Nat := 4983230072969 + 3 ^ 40 * 278472 * 2
def baseEnd_278472 : Nat := 142989984818939710719337

theorem tailTrace_278472 : CollatzResearch.WordTrace tailWord_278472 prefixEnd_278472 142989984818939710719337 := by
  unfold tailWord_278472
  simp only [CollatzResearch.WordTrace]
  refine ⟨5078354123575489038162835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6771138831433985384217113 5078354123575489038162835)
  ·
    refine ⟨7617531185363233557244253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5078354123575489038162835 7617531185363233557244253)
    ·
      refine ⟨2856574194511212583966595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7617531185363233557244253 2856574194511212583966595)
      ·
        refine ⟨4284861291766818875949893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2856574194511212583966595 4284861291766818875949893)
        ·
          refine ⟨803411492206278539240605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4284861291766818875949893 803411492206278539240605)
          ·
            refine ⟨301279309577354452215227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 803411492206278539240605 301279309577354452215227)
            ·
              refine ⟨451918964366031678322841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301279309577354452215227 451918964366031678322841)
              ·
                refine ⟨338939223274523758742131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 451918964366031678322841 338939223274523758742131)
                ·
                  refine ⟨508408834911785638113197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 338939223274523758742131 508408834911785638113197)
                  ·
                    refine ⟨190653313091919614292449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 508408834911785638113197 190653313091919614292449)
                    ·
                      refine ⟨142989984818939710719337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 190653313091919614292449 142989984818939710719337)
                      ·
                        rfl

theorem cell23_278472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 1, 3, 2].length) (baseStart_278472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278472 prefixEnd_278472 := by exact prefixLift 278472
  have htrace : WordTrace (prefixWord ++ tailWord_278472) baseStart_278472 baseEnd_278472 := by
    simpa [prefixWord, tailWord_278472, baseEnd_278472] using wordTrace_append hprefix tailTrace_278472
  have hstable : (prefixWord ++ tailWord_278472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278472).length < 2 ^ (prefixWord ++ tailWord_278472).sum := by decide
  have hdescent : baseEnd_278472 < baseStart_278472 := by decide
  rcases family_descends (prefixWord ++ tailWord_278472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278485 : List Nat := [1, 3, 2, 3, 2, 2, 1, 2, 1, 4, 2]
def baseStart_278485 : Nat := 118140960795 + 278485 * 2 ^ 59
def prefixEnd_278485 : Nat := 4983230072969 + 3 ^ 40 * 278485 * 2
def baseEnd_278485 : Nat := 142996660067448159856777

theorem tailTrace_278485 : CollatzResearch.WordTrace tailWord_278485 prefixEnd_278485 142996660067448159856777 := by
  unfold tailWord_278485
  simp only [CollatzResearch.WordTrace]
  refine ⟨10157182396103881296548909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6771454930735920864365939 10157182396103881296548909)
  ·
    refine ⟨3808943398538955486205841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10157182396103881296548909 3808943398538955486205841)
    ·
      refine ⟨2856707548904216614654381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3808943398538955486205841 2856707548904216614654381)
      ·
        refine ⟨1071265330839081230495393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2856707548904216614654381 1071265330839081230495393)
        ·
          refine ⟨803448998129310922871545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1071265330839081230495393 803448998129310922871545)
          ·
            refine ⟨602586748596983192153659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 803448998129310922871545 602586748596983192153659)
            ·
              refine ⟨903880122895474788230489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 602586748596983192153659 903880122895474788230489)
              ·
                refine ⟨677910092171606091172867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 903880122895474788230489 677910092171606091172867)
                ·
                  refine ⟨1016865138257409136759301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 677910092171606091172867 1016865138257409136759301)
                  ·
                    refine ⟨190662213423264213142369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1016865138257409136759301 190662213423264213142369)
                    ·
                      refine ⟨142996660067448159856777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 190662213423264213142369 142996660067448159856777)
                      ·
                        rfl

theorem cell23_278485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_278485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278485 prefixEnd_278485 := by exact prefixLift 278485
  have htrace : WordTrace (prefixWord ++ tailWord_278485) baseStart_278485 baseEnd_278485 := by
    simpa [prefixWord, tailWord_278485, baseEnd_278485] using wordTrace_append hprefix tailTrace_278485
  have hstable : (prefixWord ++ tailWord_278485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278485).length < 2 ^ (prefixWord ++ tailWord_278485).sum := by decide
  have hdescent : baseEnd_278485 < baseStart_278485 := by decide
  rcases family_descends (prefixWord ++ tailWord_278485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278538 : List Nat := [3, 1, 2, 2, 4, 1, 1, 1, 1, 7]
def baseStart_278538 : Nat := 118140960795 + 278538 * 2 ^ 59
def prefixEnd_278538 : Nat := 4983230072969 + 3 ^ 40 * 278538 * 2
def baseEnd_278538 : Nat := 47674624847378817498011

theorem tailTrace_278538 : CollatzResearch.WordTrace tailWord_278538 prefixEnd_278538 47674624847378817498011 := by
  unfold tailWord_278538
  simp only [CollatzResearch.WordTrace]
  refine ⟨2539778866227967837057067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6772743643274580898818845 2539778866227967837057067)
  ·
    refine ⟨3809668299341951755585601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2539778866227967837057067 3809668299341951755585601)
    ·
      refine ⟨2857251224506463816689201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3809668299341951755585601 2857251224506463816689201)
      ·
        refine ⟨2142938418379847862516901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2857251224506463816689201 2142938418379847862516901)
        ·
          refine ⟨401800953446221474221919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2142938418379847862516901 401800953446221474221919)
          ·
            refine ⟨602701430169332211332879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401800953446221474221919 602701430169332211332879)
            ·
              refine ⟨904052145253998316999319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 602701430169332211332879 904052145253998316999319)
              ·
                refine ⟨1356078217880997475498979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 904052145253998316999319 1356078217880997475498979)
                ·
                  refine ⟨2034117326821496213248469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1356078217880997475498979 2034117326821496213248469)
                  ·
                    refine ⟨47674624847378817498011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2034117326821496213248469 47674624847378817498011)
                    ·
                      rfl

theorem cell23_278538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_278538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278538 prefixEnd_278538 := by exact prefixLift 278538
  have htrace : WordTrace (prefixWord ++ tailWord_278538) baseStart_278538 baseEnd_278538 := by
    simpa [prefixWord, tailWord_278538, baseEnd_278538] using wordTrace_append hprefix tailTrace_278538
  have hstable : (prefixWord ++ tailWord_278538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278538).length < 2 ^ (prefixWord ++ tailWord_278538).sum := by decide
  have hdescent : baseEnd_278538 < baseStart_278538 := by decide
  rcases family_descends (prefixWord ++ tailWord_278538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278578 : List Nat := [3, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3]
def baseStart_278578 : Nat := 118140960795 + 278578 * 2 ^ 59
def prefixEnd_278578 : Nat := 4983230072969 + 3 ^ 40 * 278578 * 2
def baseEnd_278578 : Nat := 143044413768316295993849

theorem tailTrace_278578 : CollatzResearch.WordTrace tailWord_278578 prefixEnd_278578 143044413768316295993849 := by
  unfold tailWord_278578
  simp only [CollatzResearch.WordTrace]
  refine ⟨2540143596191739544921097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6773716256511305453122925 2540143596191739544921097)
  ·
    refine ⟨1905107697143804658690823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2540143596191739544921097 1905107697143804658690823)
    ·
      refine ⟨2857661545715706988036235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1905107697143804658690823 2857661545715706988036235)
      ·
        refine ⟨4286492318573560482054353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2857661545715706988036235 4286492318573560482054353)
        ·
          refine ⟨3214869238930170361540765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4286492318573560482054353 3214869238930170361540765)
          ·
            refine ⟨1205575964598813885577787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3214869238930170361540765 1205575964598813885577787)
            ·
              refine ⟨1808363946898220828366681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1205575964598813885577787 1808363946898220828366681)
              ·
                refine ⟨1356272960173665621275011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1808363946898220828366681 1356272960173665621275011)
                ·
                  refine ⟨2034409440260498431912517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1356272960173665621275011 2034409440260498431912517)
                  ·
                    refine ⟨381451770048843455983597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2034409440260498431912517 381451770048843455983597)
                    ·
                      refine ⟨143044413768316295993849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 381451770048843455983597 143044413768316295993849)
                      ·
                        rfl

theorem cell23_278578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_278578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278578 prefixEnd_278578 := by exact prefixLift 278578
  have htrace : WordTrace (prefixWord ++ tailWord_278578) baseStart_278578 baseEnd_278578 := by
    simpa [prefixWord, tailWord_278578, baseEnd_278578] using wordTrace_append hprefix tailTrace_278578
  have hstable : (prefixWord ++ tailWord_278578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278578).length < 2 ^ (prefixWord ++ tailWord_278578).sum := by decide
  have hdescent : baseEnd_278578 < baseStart_278578 := by decide
  rcases family_descends (prefixWord ++ tailWord_278578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278651 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 5]
def baseStart_278651 : Nat := 118140960795 + 278651 * 2 ^ 59
def prefixEnd_278651 : Nat := 4983230072969 + 3 ^ 40 * 278651 * 2
def baseEnd_278651 : Nat := 143081897856094510381013

theorem tailTrace_278651 : CollatzResearch.WordTrace tailWord_278651 prefixEnd_278651 143081897856094510381013 := by
  unfold tailWord_278651
  simp only [CollatzResearch.WordTrace]
  refine ⟨10163236913502491647091807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6775491275668327764727871 10163236913502491647091807)
  ·
    refine ⟨15244855370253737470637711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10163236913502491647091807 15244855370253737470637711)
    ·
      refine ⟨22867283055380606205956567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15244855370253737470637711 22867283055380606205956567)
      ·
        refine ⟨34300924583070909308934851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22867283055380606205956567 34300924583070909308934851)
        ·
          refine ⟨51451386874606363963402277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34300924583070909308934851 51451386874606363963402277)
          ·
            refine ⟨9647135038988693243137927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51451386874606363963402277 9647135038988693243137927)
            ·
              refine ⟨14470702558483039864706891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9647135038988693243137927 14470702558483039864706891)
              ·
                refine ⟨21706053837724559797060337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14470702558483039864706891 21706053837724559797060337)
                ·
                  refine ⟨16279540378293419847795253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21706053837724559797060337 16279540378293419847795253)
                  ·
                    refine ⟨1526206910465008110730805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16279540378293419847795253 1526206910465008110730805)
                    ·
                      refine ⟨143081897856094510381013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1526206910465008110730805 143081897856094510381013)
                      ·
                        rfl

theorem cell23_278651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 5].length) (baseStart_278651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278651 prefixEnd_278651 := by exact prefixLift 278651
  have htrace : WordTrace (prefixWord ++ tailWord_278651) baseStart_278651 baseEnd_278651 := by
    simpa [prefixWord, tailWord_278651, baseEnd_278651] using wordTrace_append hprefix tailTrace_278651
  have hstable : (prefixWord ++ tailWord_278651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278651).length < 2 ^ (prefixWord ++ tailWord_278651).sum := by decide
  have hdescent : baseEnd_278651 < baseStart_278651 := by decide
  rcases family_descends (prefixWord ++ tailWord_278651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278652 : List Nat := [2, 2, 2, 1, 1, 5, 2, 1, 2, 3, 2]
def baseStart_278652 : Nat := 118140960795 + 278652 * 2 ^ 59
def prefixEnd_278652 : Nat := 4983230072969 + 3 ^ 40 * 278652 * 2
def baseEnd_278652 : Nat := 143082411336749006468509

theorem tailTrace_278652 : CollatzResearch.WordTrace tailWord_278652 prefixEnd_278652 143082411336749006468509 := by
  unfold tailWord_278652
  simp only [CollatzResearch.WordTrace]
  refine ⟨5081636693249434408939105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6775515590999245878585473 5081636693249434408939105)
  ·
    refine ⟨3811227519937075806704329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5081636693249434408939105 3811227519937075806704329)
    ·
      refine ⟨2858420639952806855028247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3811227519937075806704329 2858420639952806855028247)
      ·
        refine ⟨4287630959929210282542371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2858420639952806855028247 4287630959929210282542371)
        ·
          refine ⟨6431446439893815423813557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4287630959929210282542371 6431446439893815423813557)
          ·
            refine ⟨602948103740045195982521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6431446439893815423813557 602948103740045195982521)
            ·
              refine ⟨452211077805033896986891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 602948103740045195982521 452211077805033896986891)
              ·
                refine ⟨678316616707550845480337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 452211077805033896986891 678316616707550845480337)
                ·
                  refine ⟨508737462530663134110253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 678316616707550845480337 508737462530663134110253)
                  ·
                    refine ⟨190776548448998675291345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 508737462530663134110253 190776548448998675291345)
                    ·
                      refine ⟨143082411336749006468509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 190776548448998675291345 143082411336749006468509)
                      ·
                        rfl

theorem cell23_278652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 2, 3, 2].length) (baseStart_278652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278652 prefixEnd_278652 := by exact prefixLift 278652
  have htrace : WordTrace (prefixWord ++ tailWord_278652) baseStart_278652 baseEnd_278652 := by
    simpa [prefixWord, tailWord_278652, baseEnd_278652] using wordTrace_append hprefix tailTrace_278652
  have hstable : (prefixWord ++ tailWord_278652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278652).length < 2 ^ (prefixWord ++ tailWord_278652).sum := by decide
  have hdescent : baseEnd_278652 < baseStart_278652 := by decide
  rcases family_descends (prefixWord ++ tailWord_278652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278685 : List Nat := [1, 4, 2, 1, 1, 3, 1, 2, 3, 2, 3]
def baseStart_278685 : Nat := 118140960795 + 278685 * 2 ^ 59
def prefixEnd_278685 : Nat := 4983230072969 + 3 ^ 40 * 278685 * 2
def baseEnd_278685 : Nat := 143099356198347377355857

theorem tailTrace_278685 : CollatzResearch.WordTrace tailWord_278685 prefixEnd_278685 143099356198347377355857 := by
  unfold tailWord_278685
  simp only [CollatzResearch.WordTrace]
  refine ⟨10164476995379315453829509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6776317996919543635886339 10164476995379315453829509)
  ·
    refine ⟨1905839436633621647593033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10164476995379315453829509 1905839436633621647593033)
    ·
      refine ⟨1429379577475216235694775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1905839436633621647593033 1429379577475216235694775)
      ·
        refine ⟨2144069366212824353542163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1429379577475216235694775 2144069366212824353542163)
        ·
          refine ⟨3216104049319236530313245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2144069366212824353542163 3216104049319236530313245)
          ·
            refine ⟨1206039018494713698867467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3216104049319236530313245 1206039018494713698867467)
            ·
              refine ⟨1809058527742070548301201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1206039018494713698867467 1809058527742070548301201)
              ·
                refine ⟨1356793895806552911225901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1809058527742070548301201 1356793895806552911225901)
                ·
                  refine ⟨508797710927457341709713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1356793895806552911225901 508797710927457341709713)
                  ·
                    refine ⟨381598283195593006282285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 508797710927457341709713 381598283195593006282285)
                    ·
                      refine ⟨143099356198347377355857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 381598283195593006282285 143099356198347377355857)
                      ·
                        rfl

theorem cell23_278685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_278685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278685 prefixEnd_278685 := by exact prefixLift 278685
  have htrace : WordTrace (prefixWord ++ tailWord_278685) baseStart_278685 baseEnd_278685 := by
    simpa [prefixWord, tailWord_278685, baseEnd_278685] using wordTrace_append hprefix tailTrace_278685
  have hstable : (prefixWord ++ tailWord_278685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278685).length < 2 ^ (prefixWord ++ tailWord_278685).sum := by decide
  have hdescent : baseEnd_278685 < baseStart_278685 := by decide
  rcases family_descends (prefixWord ++ tailWord_278685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278688 : List Nat := [2, 1, 1, 4, 2, 2, 3, 8]
def baseStart_278688 : Nat := 118140960795 + 278688 * 2 ^ 59
def prefixEnd_278688 : Nat := 4983230072969 + 3 ^ 40 * 278688 * 2
def baseEnd_278688 : Nat := 5300033208900402430309

theorem tailTrace_278688 : CollatzResearch.WordTrace tailWord_278688 prefixEnd_278688 5300033208900402430309 := by
  unfold tailWord_278688
  simp only [CollatzResearch.WordTrace]
  refine ⟨5082293207184223483094359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6776390942912297977459145 5082293207184223483094359)
  ·
    refine ⟨7623439810776335224641539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5082293207184223483094359 7623439810776335224641539)
    ·
      refine ⟨11435159716164502836962309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7623439810776335224641539 11435159716164502836962309)
      ·
        refine ⟨2144092446780844281930433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11435159716164502836962309 2144092446780844281930433)
        ·
          refine ⟨1608069335085633211447825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2144092446780844281930433 1608069335085633211447825)
          ·
            refine ⟨1206052001314224908585869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1608069335085633211447825 1206052001314224908585869)
            ·
              refine ⟨452269500492834340719701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1206052001314224908585869 452269500492834340719701)
              ·
                refine ⟨5300033208900402430309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 452269500492834340719701 5300033208900402430309)
                ·
                  rfl

theorem cell23_278688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 8].length) (baseStart_278688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278688 prefixEnd_278688 := by exact prefixLift 278688
  have htrace : WordTrace (prefixWord ++ tailWord_278688) baseStart_278688 baseEnd_278688 := by
    simpa [prefixWord, tailWord_278688, baseEnd_278688] using wordTrace_append hprefix tailTrace_278688
  have hstable : (prefixWord ++ tailWord_278688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278688).length < 2 ^ (prefixWord ++ tailWord_278688).sum := by decide
  have hdescent : baseEnd_278688 < baseStart_278688 := by decide
  rcases family_descends (prefixWord ++ tailWord_278688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278715 : List Nat := [1, 1, 1, 1, 1, 2, 6, 2, 4, 1, 3]
def baseStart_278715 : Nat := 118140960795 + 278715 * 2 ^ 59
def prefixEnd_278715 : Nat := 4983230072969 + 3 ^ 40 * 278715 * 2
def baseEnd_278715 : Nat := 143114760617982259980719

theorem tailTrace_278715 : CollatzResearch.WordTrace tailWord_278715 prefixEnd_278715 143114760617982259980719 := by
  unfold tailWord_278715
  simp only [CollatzResearch.WordTrace]
  refine ⟨10165571185270630577421599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6777047456847087051614399 10165571185270630577421599)
  ·
    refine ⟨15248356777905945866132399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10165571185270630577421599 15248356777905945866132399)
    ·
      refine ⟨22872535166858918799198599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15248356777905945866132399 22872535166858918799198599)
      ·
        refine ⟨34308802750288378198797899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22872535166858918799198599 34308802750288378198797899)
        ·
          refine ⟨51463204125432567298196849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34308802750288378198797899 51463204125432567298196849)
          ·
            refine ⟨38597403094074425473647637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51463204125432567298196849 38597403094074425473647637)
            ·
              refine ⟨1809253270034738694077233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38597403094074425473647637 1809253270034738694077233)
              ·
                refine ⟨1356939952526054020557925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1809253270034738694077233 1356939952526054020557925)
                ·
                  refine ⟨254426241098635128854611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1356939952526054020557925 254426241098635128854611)
                  ·
                    refine ⟨381639361647952693281917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 254426241098635128854611 381639361647952693281917)
                    ·
                      refine ⟨143114760617982259980719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 381639361647952693281917 143114760617982259980719)
                      ·
                        rfl

theorem cell23_278715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 4, 1, 3].length) (baseStart_278715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278715 prefixEnd_278715 := by exact prefixLift 278715
  have htrace : WordTrace (prefixWord ++ tailWord_278715) baseStart_278715 baseEnd_278715 := by
    simpa [prefixWord, tailWord_278715, baseEnd_278715] using wordTrace_append hprefix tailTrace_278715
  have hstable : (prefixWord ++ tailWord_278715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278715).length < 2 ^ (prefixWord ++ tailWord_278715).sum := by decide
  have hdescent : baseEnd_278715 < baseStart_278715 := by decide
  rcases family_descends (prefixWord ++ tailWord_278715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278716 : List Nat := [2, 2, 2, 3, 4, 1, 2, 1, 1, 1, 4]
def baseStart_278716 : Nat := 118140960795 + 278716 * 2 ^ 59
def prefixEnd_278716 : Nat := 4983230072969 + 3 ^ 40 * 278716 * 2
def baseEnd_278716 : Nat := 143115274098636756068215

theorem tailTrace_278716 : CollatzResearch.WordTrace tailWord_278716 prefixEnd_278716 143115274098636756068215 := by
  unfold tailWord_278716
  simp only [CollatzResearch.WordTrace]
  refine ⟨5082803829133503874104001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6777071772178005165472001 5082803829133503874104001)
  ·
    refine ⟨3812102871850127905578001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5082803829133503874104001 3812102871850127905578001)
    ·
      refine ⟨2859077153887595929183501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3812102871850127905578001 2859077153887595929183501)
      ·
        refine ⟨1072153932707848473443813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2859077153887595929183501 1072153932707848473443813)
        ·
          refine ⟨201028862382721588770715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1072153932707848473443813 201028862382721588770715)
          ·
            refine ⟨301543293574082383156073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201028862382721588770715 301543293574082383156073)
            ·
              refine ⟨226157470180561787367055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 301543293574082383156073 226157470180561787367055)
              ·
                refine ⟨339236205270842681050583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226157470180561787367055 339236205270842681050583)
                ·
                  refine ⟨508854307906264021575875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 339236205270842681050583 508854307906264021575875)
                  ·
                    refine ⟨763281461859396032363813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 508854307906264021575875 763281461859396032363813)
                    ·
                      refine ⟨143115274098636756068215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 763281461859396032363813 143115274098636756068215)
                      ·
                        rfl

theorem cell23_278716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_278716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278716 prefixEnd_278716 := by exact prefixLift 278716
  have htrace : WordTrace (prefixWord ++ tailWord_278716) baseStart_278716 baseEnd_278716 := by
    simpa [prefixWord, tailWord_278716, baseEnd_278716] using wordTrace_append hprefix tailTrace_278716
  have hstable : (prefixWord ++ tailWord_278716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278716).length < 2 ^ (prefixWord ++ tailWord_278716).sum := by decide
  have hdescent : baseEnd_278716 < baseStart_278716 := by decide
  rcases family_descends (prefixWord ++ tailWord_278716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278722 : List Nat := [3, 5, 1, 1, 1, 2, 10]
def baseStart_278722 : Nat := 118140960795 + 278722 * 2 ^ 59
def prefixEnd_278722 : Nat := 4983230072969 + 3 ^ 40 * 278722 * 2
def baseEnd_278722 : Nat := 1766893271389675711027

theorem tailTrace_278722 : CollatzResearch.WordTrace tailWord_278722 prefixEnd_278722 1766893271389675711027 := by
  unfold tailWord_278722
  simp only [CollatzResearch.WordTrace]
  refine ⟨2541456624061317693231605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6777217664163513848617613 2541456624061317693231605)
  ·
    refine ⟨238261558505748533740463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2541456624061317693231605 238261558505748533740463)
    ·
      refine ⟨357392337758622800610695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238261558505748533740463 357392337758622800610695)
      ·
        refine ⟨536088506637934200916043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357392337758622800610695 536088506637934200916043)
        ·
          refine ⟨804132759956901301374065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 536088506637934200916043 804132759956901301374065)
          ·
            refine ⟨603099569967675976030549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 804132759956901301374065 603099569967675976030549)
            ·
              refine ⟨1766893271389675711027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 603099569967675976030549 1766893271389675711027)
              ·
                rfl

theorem cell23_278722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 10].length) (baseStart_278722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278722 prefixEnd_278722 := by exact prefixLift 278722
  have htrace : WordTrace (prefixWord ++ tailWord_278722) baseStart_278722 baseEnd_278722 := by
    simpa [prefixWord, tailWord_278722, baseEnd_278722] using wordTrace_append hprefix tailTrace_278722
  have hstable : (prefixWord ++ tailWord_278722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278722).length < 2 ^ (prefixWord ++ tailWord_278722).sum := by decide
  have hdescent : baseEnd_278722 < baseStart_278722 := by decide
  rcases family_descends (prefixWord ++ tailWord_278722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278749 : List Nat := [1, 4, 3, 2, 1, 3, 1, 1, 1, 3, 3]
def baseStart_278749 : Nat := 118140960795 + 278749 * 2 ^ 59
def prefixEnd_278749 : Nat := 4983230072969 + 3 ^ 40 * 278749 * 2
def baseEnd_278749 : Nat := 143132218960235126955563

theorem tailTrace_278749 : CollatzResearch.WordTrace tailWord_278749 prefixEnd_278749 143132218960235126955563 := by
  unfold tailWord_278749
  simp only [CollatzResearch.WordTrace]
  refine ⟨10166811267147454384159301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6777874178098302922772867 10166811267147454384159301)
  ·
    refine ⟨1906277112590147697029869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10166811267147454384159301 1906277112590147697029869)
    ·
      refine ⟨714853917221305386386201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1906277112590147697029869 714853917221305386386201)
      ·
        refine ⟨536140437915979039789651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 714853917221305386386201 536140437915979039789651)
        ·
          refine ⟨804210656873968559684477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 536140437915979039789651 804210656873968559684477)
          ·
            refine ⟨301578996327738209881679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 804210656873968559684477 301578996327738209881679)
            ·
              refine ⟨452368494491607314822519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301578996327738209881679 452368494491607314822519)
              ·
                refine ⟨678552741737410972233779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 452368494491607314822519 678552741737410972233779)
                ·
                  refine ⟨1017829112606116458350669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 678552741737410972233779 1017829112606116458350669)
                  ·
                    refine ⟨381685917227293671881501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1017829112606116458350669 381685917227293671881501)
                    ·
                      refine ⟨143132218960235126955563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 381685917227293671881501 143132218960235126955563)
                      ·
                        rfl

theorem cell23_278749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_278749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278749 prefixEnd_278749 := by exact prefixLift 278749
  have htrace : WordTrace (prefixWord ++ tailWord_278749) baseStart_278749 baseEnd_278749 := by
    simpa [prefixWord, tailWord_278749, baseEnd_278749] using wordTrace_append hprefix tailTrace_278749
  have hstable : (prefixWord ++ tailWord_278749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278749).length < 2 ^ (prefixWord ++ tailWord_278749).sum := by decide
  have hdescent : baseEnd_278749 < baseStart_278749 := by decide
  rcases family_descends (prefixWord ++ tailWord_278749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278759 : List Nat := [1, 1, 5, 3, 1, 1, 1, 4, 1, 3, 2]
def baseStart_278759 : Nat := 118140960795 + 278759 * 2 ^ 59
def prefixEnd_278759 : Nat := 4983230072969 + 3 ^ 40 * 278759 * 2
def baseEnd_278759 : Nat := 143137353766780087830517

theorem tailTrace_278759 : CollatzResearch.WordTrace tailWord_278759 prefixEnd_278759 143137353766780087830517 := by
  unfold tailWord_278759
  simp only [CollatzResearch.WordTrace]
  refine ⟨10167175997111226092023331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6778117331407484061348887 10167175997111226092023331)
  ·
    refine ⟨15250763995666839138034997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10167175997111226092023331 15250763995666839138034997)
    ·
      refine ⟨1429759124593766169190781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15250763995666839138034997 1429759124593766169190781)
      ·
        refine ⟨536159671722662313446543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1429759124593766169190781 536159671722662313446543)
        ·
          refine ⟨804239507583993470169815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 536159671722662313446543 804239507583993470169815)
          ·
            refine ⟨1206359261375990205254723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 804239507583993470169815 1206359261375990205254723)
            ·
              refine ⟨1809538892063985307882085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1206359261375990205254723 1809538892063985307882085)
              ·
                refine ⟨339288542261997245227891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1809538892063985307882085 339288542261997245227891)
                ·
                  refine ⟨508932813392995867841837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 339288542261997245227891 508932813392995867841837)
                  ·
                    refine ⟨190849805022373450440689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 508932813392995867841837 190849805022373450440689)
                    ·
                      refine ⟨143137353766780087830517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 190849805022373450440689 143137353766780087830517)
                      ·
                        rfl

theorem cell23_278759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_278759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278759 prefixEnd_278759 := by exact prefixLift 278759
  have htrace : WordTrace (prefixWord ++ tailWord_278759) baseStart_278759 baseEnd_278759 := by
    simpa [prefixWord, tailWord_278759, baseEnd_278759] using wordTrace_append hprefix tailTrace_278759
  have hstable : (prefixWord ++ tailWord_278759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278759).length < 2 ^ (prefixWord ++ tailWord_278759).sum := by decide
  have hdescent : baseEnd_278759 < baseStart_278759 := by decide
  rcases family_descends (prefixWord ++ tailWord_278759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278768 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 4]
def baseStart_278768 : Nat := 118140960795 + 278768 * 2 ^ 59
def prefixEnd_278768 : Nat := 4983230072969 + 3 ^ 40 * 278768 * 2
def baseEnd_278768 : Nat := 143141975092670552617975

theorem tailTrace_278768 : CollatzResearch.WordTrace tailWord_278768 prefixEnd_278768 143141975092670552617975 := by
  unfold tailWord_278768
  simp only [CollatzResearch.WordTrace]
  refine ⟨5083752127039310314550479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6778336169385747086067305 5083752127039310314550479)
  ·
    refine ⟨7625628190558965471825719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5083752127039310314550479 7625628190558965471825719)
    ·
      refine ⟨11438442285838448207738579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7625628190558965471825719 11438442285838448207738579)
      ·
        refine ⟨17157663428757672311607869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11438442285838448207738579 17157663428757672311607869)
        ·
          refine ⟨6434123785784127116852951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17157663428757672311607869 6434123785784127116852951)
          ·
            refine ⟨9651185678676190675279427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6434123785784127116852951 9651185678676190675279427)
            ·
              refine ⟨14476778518014286012919141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9651185678676190675279427 14476778518014286012919141)
              ·
                refine ⟨2714395972127678627422339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14476778518014286012919141 2714395972127678627422339)
                ·
                  refine ⟨4071593958191517941133509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2714395972127678627422339 4071593958191517941133509)
                  ·
                    refine ⟨763423867160909613962533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4071593958191517941133509 763423867160909613962533)
                    ·
                      refine ⟨143141975092670552617975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 763423867160909613962533 143141975092670552617975)
                      ·
                        rfl

theorem cell23_278768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 4].length) (baseStart_278768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278768 prefixEnd_278768 := by exact prefixLift 278768
  have htrace : WordTrace (prefixWord ++ tailWord_278768) baseStart_278768 baseEnd_278768 := by
    simpa [prefixWord, tailWord_278768, baseEnd_278768] using wordTrace_append hprefix tailTrace_278768
  have hstable : (prefixWord ++ tailWord_278768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278768).length < 2 ^ (prefixWord ++ tailWord_278768).sum := by decide
  have hdescent : baseEnd_278768 < baseStart_278768 := by decide
  rcases family_descends (prefixWord ++ tailWord_278768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278805 : List Nat := [1, 3, 2, 1, 2, 1, 2, 3, 2, 3, 3]
def baseStart_278805 : Nat := 118140960795 + 278805 * 2 ^ 59
def prefixEnd_278805 : Nat := 4983230072969 + 3 ^ 40 * 278805 * 2
def baseEnd_278805 : Nat := 143160973876886907855305

theorem tailTrace_278805 : CollatzResearch.WordTrace tailWord_278805 prefixEnd_278805 143160973876886907855305 := by
  unfold tailWord_278805
  simp only [CollatzResearch.WordTrace]
  refine ⟨10168853754944575948197869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6779235836629717298798579 10168853754944575948197869)
  ·
    refine ⟨3813320158104215980574201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10168853754944575948197869 3813320158104215980574201)
    ·
      refine ⟨2859990118578161985430651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3813320158104215980574201 2859990118578161985430651)
      ·
        refine ⟨4289985177867242978145977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2859990118578161985430651 4289985177867242978145977)
        ·
          refine ⟨3217488883400432233609483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4289985177867242978145977 3217488883400432233609483)
          ·
            refine ⟨4826233325100648350414225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3217488883400432233609483 4826233325100648350414225)
            ·
              refine ⟨3619674993825486262810669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4826233325100648350414225 3619674993825486262810669)
              ·
                refine ⟨1357378122684557348554001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3619674993825486262810669 1357378122684557348554001)
                ·
                  refine ⟨1018033592013418011415501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1357378122684557348554001 1018033592013418011415501)
                  ·
                    refine ⟨381762597005031754280813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1018033592013418011415501 381762597005031754280813)
                    ·
                      refine ⟨143160973876886907855305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 381762597005031754280813 143160973876886907855305)
                      ·
                        rfl

theorem cell23_278805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_278805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278805 prefixEnd_278805 := by exact prefixLift 278805
  have htrace : WordTrace (prefixWord ++ tailWord_278805) baseStart_278805 baseEnd_278805 := by
    simpa [prefixWord, tailWord_278805, baseEnd_278805] using wordTrace_append hprefix tailTrace_278805
  have hstable : (prefixWord ++ tailWord_278805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278805).length < 2 ^ (prefixWord ++ tailWord_278805).sum := by decide
  have hdescent : baseEnd_278805 < baseStart_278805 := by decide
  rcases family_descends (prefixWord ++ tailWord_278805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278823 : List Nat := [1, 1, 8, 1, 1, 1, 1, 2, 1, 4, 2]
def baseStart_278823 : Nat := 118140960795 + 278823 * 2 ^ 59
def prefixEnd_278823 : Nat := 4983230072969 + 3 ^ 40 * 278823 * 2
def baseEnd_278823 : Nat := 143170216528667837430223

theorem tailTrace_278823 : CollatzResearch.WordTrace tailWord_278823 prefixEnd_278823 143170216528667837430223 := by
  unfold tailWord_278823
  simp only [CollatzResearch.WordTrace]
  refine ⟨10169510268879365022353123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6779673512586243348235415 10169510268879365022353123)
  ·
    refine ⟨15254265403319047533529685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10169510268879365022353123 15254265403319047533529685)
    ·
      refine ⟨178760922695145088283551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 15254265403319047533529685 178760922695145088283551)
      ·
        refine ⟨268141384042717632425327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178760922695145088283551 268141384042717632425327)
        ·
          refine ⟨402212076064076448637991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268141384042717632425327 402212076064076448637991)
          ·
            refine ⟨603318114096114672956987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402212076064076448637991 603318114096114672956987)
            ·
              refine ⟨904977171144172009435481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 603318114096114672956987 904977171144172009435481)
              ·
                refine ⟨678732878358129007076611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 904977171144172009435481 678732878358129007076611)
                ·
                  refine ⟨1018099317537193510614917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 678732878358129007076611 1018099317537193510614917)
                  ·
                    refine ⟨190893622038223783240297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1018099317537193510614917 190893622038223783240297)
                    ·
                      refine ⟨143170216528667837430223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 190893622038223783240297 143170216528667837430223)
                      ·
                        rfl

theorem cell23_278823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_278823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278823 prefixEnd_278823 := by exact prefixLift 278823
  have htrace : WordTrace (prefixWord ++ tailWord_278823) baseStart_278823 baseEnd_278823 := by
    simpa [prefixWord, tailWord_278823, baseEnd_278823] using wordTrace_append hprefix tailTrace_278823
  have hstable : (prefixWord ++ tailWord_278823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278823).length < 2 ^ (prefixWord ++ tailWord_278823).sum := by decide
  have hdescent : baseEnd_278823 < baseStart_278823 := by decide
  rcases family_descends (prefixWord ++ tailWord_278823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278846 : List Nat := [4, 2, 1, 2, 1, 4, 2, 2, 5]
def baseStart_278846 : Nat := 118140960795 + 278846 * 2 ^ 59
def prefixEnd_278846 : Nat := 4983230072969 + 3 ^ 40 * 278846 * 2
def baseEnd_278846 : Nat := 15909114064857916382513

theorem tailTrace_278846 : CollatzResearch.WordTrace tailWord_278846 prefixEnd_278846 15909114064857916382513 := by
  unfold tailWord_278846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1271293643474504993805049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6780232765197359966960261 1271293643474504993805049)
  ·
    refine ⟨953470232605878745353787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1271293643474504993805049 953470232605878745353787)
    ·
      refine ⟨1430205348908818118030681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 953470232605878745353787 1430205348908818118030681)
      ·
        refine ⟨1072654011681613588523011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1430205348908818118030681 1072654011681613588523011)
        ·
          refine ⟨1608981017522420382784517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1072654011681613588523011 1608981017522420382784517)
          ·
            refine ⟨301683940785453821772097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1608981017522420382784517 301683940785453821772097)
            ·
              refine ⟨226262955589090366329073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 301683940785453821772097 226262955589090366329073)
              ·
                refine ⟨169697216691817774746805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226262955589090366329073 169697216691817774746805)
                ·
                  refine ⟨15909114064857916382513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 169697216691817774746805 15909114064857916382513)
                  ·
                    rfl

theorem cell23_278846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_278846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278846 prefixEnd_278846 := by exact prefixLift 278846
  have htrace : WordTrace (prefixWord ++ tailWord_278846) baseStart_278846 baseEnd_278846 := by
    simpa [prefixWord, tailWord_278846, baseEnd_278846] using wordTrace_append hprefix tailTrace_278846
  have hstable : (prefixWord ++ tailWord_278846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278846).length < 2 ^ (prefixWord ++ tailWord_278846).sum := by decide
  have hdescent : baseEnd_278846 < baseStart_278846 := by decide
  rcases family_descends (prefixWord ++ tailWord_278846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278876 : List Nat := [2, 2, 4, 3, 1, 2, 1, 1, 2, 5]
def baseStart_278876 : Nat := 118140960795 + 278876 * 2 ^ 59
def prefixEnd_278876 : Nat := 4983230072969 + 3 ^ 40 * 278876 * 2
def baseEnd_278876 : Nat := 47732477001118710022493

theorem tailTrace_278876 : CollatzResearch.WordTrace tailWord_278876 prefixEnd_278876 47732477001118710022493 := by
  unfold tailWord_278876
  simp only [CollatzResearch.WordTrace]
  refine ⟨5085721668843677537016241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6780962225124903382688321 5085721668843677537016241)
  ·
    refine ⟨3814291251632758152762181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5085721668843677537016241 3814291251632758152762181)
    ·
      refine ⟨715179609681142153642909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3814291251632758152762181 715179609681142153642909)
      ·
        refine ⟨268192353630428307616091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 715179609681142153642909 268192353630428307616091)
        ·
          refine ⟨402288530445642461424137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268192353630428307616091 402288530445642461424137)
          ·
            refine ⟨301716397834231846068103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 402288530445642461424137 301716397834231846068103)
            ·
              refine ⟨452574596751347769102155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301716397834231846068103 452574596751347769102155)
              ·
                refine ⟨678861895127021653653233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 452574596751347769102155 678861895127021653653233)
                ·
                  refine ⟨509146421345266240239925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 678861895127021653653233 509146421345266240239925)
                  ·
                    refine ⟨47732477001118710022493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 509146421345266240239925 47732477001118710022493)
                    ·
                      rfl

theorem cell23_278876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_278876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278876 prefixEnd_278876 := by exact prefixLift 278876
  have htrace : WordTrace (prefixWord ++ tailWord_278876) baseStart_278876 baseEnd_278876 := by
    simpa [prefixWord, tailWord_278876, baseEnd_278876] using wordTrace_append hprefix tailTrace_278876
  have hstable : (prefixWord ++ tailWord_278876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278876).length < 2 ^ (prefixWord ++ tailWord_278876).sum := by decide
  have hdescent : baseEnd_278876 < baseStart_278876 := by decide
  rcases family_descends (prefixWord ++ tailWord_278876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278889 : List Nat := [1, 2, 1, 1, 1, 3, 6, 3, 1, 4]
def baseStart_278889 : Nat := 118140960795 + 278889 * 2 ^ 59
def prefixEnd_278889 : Nat := 4983230072969 + 3 ^ 40 * 278889 * 2
def baseEnd_278889 : Nat := 47734702083954859734973

theorem tailTrace_278889 : CollatzResearch.WordTrace tailWord_278889 prefixEnd_278889 47734702083954859734973 := by
  unfold tailWord_278889
  simp only [CollatzResearch.WordTrace]
  refine ⟨10171917486640258294255721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6781278324426838862837147 10171917486640258294255721)
  ·
    refine ⟨7628938114980193720691791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10171917486640258294255721 7628938114980193720691791)
    ·
      refine ⟨11443407172470290581037687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7628938114980193720691791 11443407172470290581037687)
      ·
        refine ⟨17165110758705435871556531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11443407172470290581037687 17165110758705435871556531)
        ·
          refine ⟨25747666138058153807334797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17165110758705435871556531 25747666138058153807334797)
          ·
            refine ⟨9655374801771807677750549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25747666138058153807334797 9655374801771807677750549)
            ·
              refine ⟨452595693833053484894557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9655374801771807677750549 452595693833053484894557)
              ·
                refine ⟨169723385187395056835459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 452595693833053484894557 169723385187395056835459)
                ·
                  refine ⟨254585077781092585253189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169723385187395056835459 254585077781092585253189)
                  ·
                    refine ⟨47734702083954859734973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 254585077781092585253189 47734702083954859734973)
                    ·
                      rfl

theorem cell23_278889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 3, 1, 4].length) (baseStart_278889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278889 prefixEnd_278889 := by exact prefixLift 278889
  have htrace : WordTrace (prefixWord ++ tailWord_278889) baseStart_278889 baseEnd_278889 := by
    simpa [prefixWord, tailWord_278889, baseEnd_278889] using wordTrace_append hprefix tailTrace_278889
  have hstable : (prefixWord ++ tailWord_278889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278889).length < 2 ^ (prefixWord ++ tailWord_278889).sum := by decide
  have hdescent : baseEnd_278889 < baseStart_278889 := by decide
  rcases family_descends (prefixWord ++ tailWord_278889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278962 : List Nat := [3, 2, 1, 1, 1, 1, 3, 3, 4, 4]
def baseStart_278962 : Nat := 118140960795 + 278962 * 2 ^ 59
def prefixEnd_278962 : Nat := 4983230072969 + 3 ^ 40 * 278962 * 2
def baseEnd_278962 : Nat := 47747196779880931197361

theorem tailTrace_278962 : CollatzResearch.WordTrace tailWord_278962 prefixEnd_278962 47747196779880931197361 := by
  unfold tailWord_278962
  simp only [CollatzResearch.WordTrace]
  refine ⟨2543645003843947940415785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6783053343583861174442093 2543645003843947940415785)
  ·
    refine ⟨1907733752882960955311839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2543645003843947940415785 1907733752882960955311839)
    ·
      refine ⟨2861600629324441432967759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1907733752882960955311839 2861600629324441432967759)
      ·
        refine ⟨4292400943986662149451639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2861600629324441432967759 4292400943986662149451639)
        ·
          refine ⟨6438601415979993224177459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4292400943986662149451639 6438601415979993224177459)
          ·
            refine ⟨9657902123969989836266189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6438601415979993224177459 9657902123969989836266189)
            ·
              refine ⟨3621713296488746188599821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9657902123969989836266189 3621713296488746188599821)
              ·
                refine ⟨1358142486183279820724933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3621713296488746188599821 1358142486183279820724933)
                ·
                  refine ⟨254651716159364966385925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1358142486183279820724933 254651716159364966385925)
                  ·
                    refine ⟨47747196779880931197361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 254651716159364966385925 47747196779880931197361)
                    ·
                      rfl

theorem cell23_278962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_278962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278962 prefixEnd_278962 := by exact prefixLift 278962
  have htrace : WordTrace (prefixWord ++ tailWord_278962) baseStart_278962 baseEnd_278962 := by
    simpa [prefixWord, tailWord_278962, baseEnd_278962] using wordTrace_append hprefix tailTrace_278962
  have hstable : (prefixWord ++ tailWord_278962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278962).length < 2 ^ (prefixWord ++ tailWord_278962).sum := by decide
  have hdescent : baseEnd_278962 < baseStart_278962 := by decide
  rcases family_descends (prefixWord ++ tailWord_278962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279022 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 2, 7]
def baseStart_279022 : Nat := 118140960795 + 279022 * 2 ^ 59
def prefixEnd_279022 : Nat := 4983230072969 + 3 ^ 40 * 279022 * 2
def baseEnd_279022 : Nat := 47757466392970852947269

theorem tailTrace_279022 : CollatzResearch.WordTrace tailWord_279022 prefixEnd_279022 47757466392970852947269 := by
  unfold tailWord_279022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1272096049394802751105915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6784512263438948005898213 1272096049394802751105915)
  ·
    refine ⟨1908144074092204126658873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1272096049394802751105915 1908144074092204126658873)
    ·
      refine ⟨1431108055569153094994155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1908144074092204126658873 1431108055569153094994155)
      ·
        refine ⟨2146662083353729642491233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1431108055569153094994155 2146662083353729642491233)
        ·
          refine ⟨1609996562515297231868425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2146662083353729642491233 1609996562515297231868425)
          ·
            refine ⟨1207497421886472923901319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1609996562515297231868425 1207497421886472923901319)
            ·
              refine ⟨1811246132829709385851979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1207497421886472923901319 1811246132829709385851979)
              ·
                refine ⟨2716869199244564078777969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1811246132829709385851979 2716869199244564078777969)
                ·
                  refine ⟨2037651899433423059083477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2716869199244564078777969 2037651899433423059083477)
                  ·
                    refine ⟨47757466392970852947269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2037651899433423059083477 47757466392970852947269)
                    ·
                      rfl

theorem cell23_279022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_279022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279022 prefixEnd_279022 := by exact prefixLift 279022
  have htrace : WordTrace (prefixWord ++ tailWord_279022) baseStart_279022 baseEnd_279022 := by
    simpa [prefixWord, tailWord_279022, baseEnd_279022] using wordTrace_append hprefix tailTrace_279022
  have hstable : (prefixWord ++ tailWord_279022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279022).length < 2 ^ (prefixWord ++ tailWord_279022).sum := by decide
  have hdescent : baseEnd_279022 < baseStart_279022 := by decide
  rcases family_descends (prefixWord ++ tailWord_279022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279026 : List Nat := [3, 2, 1, 4, 3, 1, 1, 8]
def baseStart_279026 : Nat := 118140960795 + 279026 * 2 ^ 59
def prefixEnd_279026 : Nat := 4983230072969 + 3 ^ 40 * 279026 * 2
def baseEnd_279026 : Nat := 5306461225982612710807

theorem tailTrace_279026 : CollatzResearch.WordTrace tailWord_279026 prefixEnd_279026 5306461225982612710807 := by
  unfold tailWord_279026
  simp only [CollatzResearch.WordTrace]
  refine ⟨2544228571785982672998233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6784609524762620461328621 2544228571785982672998233)
  ·
    refine ⟨1908171428839487004748675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2544228571785982672998233 1908171428839487004748675)
    ·
      refine ⟨2862257143259230507123013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1908171428839487004748675 2862257143259230507123013)
      ·
        refine ⟨536673214361105720085565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2862257143259230507123013 536673214361105720085565)
        ·
          refine ⟨201252455385414645032087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 536673214361105720085565 201252455385414645032087)
          ·
            refine ⟨301878683078121967548131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201252455385414645032087 301878683078121967548131)
            ·
              refine ⟨452818024617182951322197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301878683078121967548131 452818024617182951322197)
              ·
                refine ⟨5306461225982612710807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 452818024617182951322197 5306461225982612710807)
                ·
                  rfl

theorem cell23_279026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 8].length) (baseStart_279026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279026 prefixEnd_279026 := by exact prefixLift 279026
  have htrace : WordTrace (prefixWord ++ tailWord_279026) baseStart_279026 baseEnd_279026 := by
    simpa [prefixWord, tailWord_279026, baseEnd_279026] using wordTrace_append hprefix tailTrace_279026
  have hstable : (prefixWord ++ tailWord_279026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279026).length < 2 ^ (prefixWord ++ tailWord_279026).sum := by decide
  have hdescent : baseEnd_279026 < baseStart_279026 := by decide
  rcases family_descends (prefixWord ++ tailWord_279026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279053 : List Nat := [1, 7, 1, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_279053 : Nat := 118140960795 + 279053 * 2 ^ 59
def prefixEnd_279053 : Nat := 4983230072969 + 3 ^ 40 * 279053 * 2
def baseEnd_279053 : Nat := 143288317079201937554165

theorem tailTrace_279053 : CollatzResearch.WordTrace tailWord_279053 prefixEnd_279053 143288317079201937554165 := by
  unfold tailWord_279053
  simp only [CollatzResearch.WordTrace]
  refine ⟨10177899058046114303225813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6785266038697409535483875 10177899058046114303225813)
  ·
    refine ⟨238544509172955803981855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 10177899058046114303225813 238544509172955803981855)
    ·
      refine ⟨357816763759433705972783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238544509172955803981855 357816763759433705972783)
      ·
        refine ⟨536725145639150558959175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357816763759433705972783 536725145639150558959175)
        ·
          refine ⟨805087718458725838438763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 536725145639150558959175 805087718458725838438763)
          ·
            refine ⟨1207631577688088757658145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 805087718458725838438763 1207631577688088757658145)
            ·
              refine ⟨905723683266066568243609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1207631577688088757658145 905723683266066568243609)
              ·
                refine ⟨679292762449549926182707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 905723683266066568243609 679292762449549926182707)
                ·
                  refine ⟨1018939143674324889274061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 679292762449549926182707 1018939143674324889274061)
                  ·
                    refine ⟨382102178877871833477773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1018939143674324889274061 382102178877871833477773)
                    ·
                      refine ⟨143288317079201937554165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 382102178877871833477773 143288317079201937554165)
                      ·
                        rfl

theorem cell23_279053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_279053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279053 prefixEnd_279053 := by exact prefixLift 279053
  have htrace : WordTrace (prefixWord ++ tailWord_279053) baseStart_279053 baseEnd_279053 := by
    simpa [prefixWord, tailWord_279053, baseEnd_279053] using wordTrace_append hprefix tailTrace_279053
  have hstable : (prefixWord ++ tailWord_279053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279053).length < 2 ^ (prefixWord ++ tailWord_279053).sum := by decide
  have hdescent : baseEnd_279053 < baseStart_279053 := by decide
  rcases family_descends (prefixWord ++ tailWord_279053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279059 : List Nat := [1, 1, 1, 2, 1, 5, 1, 4, 1, 4, 2]
def baseStart_279059 : Nat := 118140960795 + 279059 * 2 ^ 59
def prefixEnd_279059 : Nat := 4983230072969 + 3 ^ 40 * 279059 * 2
def baseEnd_279059 : Nat := 143291397963128914079137

theorem tailTrace_279059 : CollatzResearch.WordTrace tailWord_279059 prefixEnd_279059 143291397963128914079137 := by
  unfold tailWord_279059
  simp only [CollatzResearch.WordTrace]
  refine ⟨10178117896024377327944231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6785411930682918218629487 10178117896024377327944231)
  ·
    refine ⟨15267176844036565991916347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10178117896024377327944231 15267176844036565991916347)
    ·
      refine ⟨22900765266054848987874521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15267176844036565991916347 22900765266054848987874521)
      ·
        refine ⟨17175573949541136740905891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22900765266054848987874521 17175573949541136740905891)
        ·
          refine ⟨25763360924311705111358837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17175573949541136740905891 25763360924311705111358837)
          ·
            refine ⟨2415315086654222354189891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25763360924311705111358837 2415315086654222354189891)
            ·
              refine ⟨3622972629981333531284837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2415315086654222354189891 3622972629981333531284837)
              ·
                refine ⟨679307368121500037115907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3622972629981333531284837 679307368121500037115907)
                ·
                  refine ⟨1018961052182250055673861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 679307368121500037115907 1018961052182250055673861)
                  ·
                    refine ⟨191055197284171885438849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1018961052182250055673861 191055197284171885438849)
                    ·
                      refine ⟨143291397963128914079137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 191055197284171885438849 143291397963128914079137)
                      ·
                        rfl

theorem cell23_279059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 4, 2].length) (baseStart_279059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279059 prefixEnd_279059 := by exact prefixLift 279059
  have htrace : WordTrace (prefixWord ++ tailWord_279059) baseStart_279059 baseEnd_279059 := by
    simpa [prefixWord, tailWord_279059, baseEnd_279059] using wordTrace_append hprefix tailTrace_279059
  have hstable : (prefixWord ++ tailWord_279059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279059).length < 2 ^ (prefixWord ++ tailWord_279059).sum := by decide
  have hdescent : baseEnd_279059 < baseStart_279059 := by decide
  rcases family_descends (prefixWord ++ tailWord_279059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279110 : List Nat := [6, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2]
def baseStart_279110 : Nat := 118140960795 + 279110 * 2 ^ 59
def prefixEnd_279110 : Nat := 4983230072969 + 3 ^ 40 * 279110 * 2
def baseEnd_279110 : Nat := 143317585476508214541403

theorem tailTrace_279110 : CollatzResearch.WordTrace tailWord_279110 prefixEnd_279110 143317585476508214541403 := by
  unfold tailWord_279110
  simp only [CollatzResearch.WordTrace]
  refine ⟨318124313088737907439087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6786652012559742025367189 318124313088737907439087)
  ·
    refine ⟨477186469633106861158631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 318124313088737907439087 477186469633106861158631)
    ·
      refine ⟨715779704449660291737947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 477186469633106861158631 715779704449660291737947)
      ·
        refine ⟨1073669556674490437606921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 715779704449660291737947 1073669556674490437606921)
        ·
          refine ⟨805252167505867828205191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1073669556674490437606921 805252167505867828205191)
          ·
            refine ⟨1207878251258801742307787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 805252167505867828205191 1207878251258801742307787)
            ·
              refine ⟨1811817376888202613461681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1207878251258801742307787 1811817376888202613461681)
              ·
                refine ⟨1358863032666151960096261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1811817376888202613461681 1358863032666151960096261)
                ·
                  refine ⟨254786818624903492518049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1358863032666151960096261 254786818624903492518049)
                  ·
                    refine ⟨191090113968677619388537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 254786818624903492518049 191090113968677619388537)
                    ·
                      refine ⟨143317585476508214541403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 191090113968677619388537 143317585476508214541403)
                      ·
                        rfl

theorem cell23_279110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_279110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279110 prefixEnd_279110 := by exact prefixLift 279110
  have htrace : WordTrace (prefixWord ++ tailWord_279110) baseStart_279110 baseEnd_279110 := by
    simpa [prefixWord, tailWord_279110, baseEnd_279110] using wordTrace_append hprefix tailTrace_279110
  have hstable : (prefixWord ++ tailWord_279110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279110).length < 2 ^ (prefixWord ++ tailWord_279110).sum := by decide
  have hdescent : baseEnd_279110 < baseStart_279110 := by decide
  rcases family_descends (prefixWord ++ tailWord_279110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279112 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 6, 5]
def baseStart_279112 : Nat := 118140960795 + 279112 * 2 ^ 59
def prefixEnd_279112 : Nat := 4983230072969 + 3 ^ 40 * 279112 * 2
def baseEnd_279112 : Nat := 47772870812605735572131

theorem tailTrace_279112 : CollatzResearch.WordTrace tailWord_279112 prefixEnd_279112 47772870812605735572131 := by
  unfold tailWord_279112
  simp only [CollatzResearch.WordTrace]
  refine ⟨5090025482416183689811795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6786700643221578253082393 5090025482416183689811795)
  ·
    refine ⟨7635038223624275534717693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5090025482416183689811795 7635038223624275534717693)
    ·
      refine ⟨2863139333859103325519135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7635038223624275534717693 2863139333859103325519135)
      ·
        refine ⟨4294709000788654988278703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2863139333859103325519135 4294709000788654988278703)
        ·
          refine ⟨6442063501182982482418055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4294709000788654988278703 6442063501182982482418055)
          ·
            refine ⟨9663095251774473723627083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6442063501182982482418055 9663095251774473723627083)
            ·
              refine ⟨14494642877661710585440625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9663095251774473723627083 14494642877661710585440625)
              ·
                refine ⟨10870982158246282939080469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14494642877661710585440625 10870982158246282939080469)
                ·
                  refine ⟨509577288667794512769397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10870982158246282939080469 509577288667794512769397)
                  ·
                    refine ⟨47772870812605735572131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 509577288667794512769397 47772870812605735572131)
                    ·
                      rfl

theorem cell23_279112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_279112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279112 prefixEnd_279112 := by exact prefixLift 279112
  have htrace : WordTrace (prefixWord ++ tailWord_279112) baseStart_279112 baseEnd_279112 := by
    simpa [prefixWord, tailWord_279112, baseEnd_279112] using wordTrace_append hprefix tailTrace_279112
  have hstable : (prefixWord ++ tailWord_279112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279112).length < 2 ^ (prefixWord ++ tailWord_279112).sum := by decide
  have hdescent : baseEnd_279112 < baseStart_279112 := by decide
  rcases family_descends (prefixWord ++ tailWord_279112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279144 : List Nat := [2, 1, 4, 3, 3, 1, 2, 1, 2, 2, 2]
def baseStart_279144 : Nat := 118140960795 + 279144 * 2 ^ 59
def prefixEnd_279144 : Nat := 4983230072969 + 3 ^ 40 * 279144 * 2
def baseEnd_279144 : Nat := 143335043818761081516247

theorem tailTrace_279144 : CollatzResearch.WordTrace tailWord_279144 prefixEnd_279144 143335043818761081516247 := by
  unfold tailWord_279144
  simp only [CollatzResearch.WordTrace]
  refine ⟨5090609050358218422394243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6787478733810957896525657 5090609050358218422394243)
  ·
    refine ⟨7635913575537327633591365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5090609050358218422394243 7635913575537327633591365)
    ·
      refine ⟨1431733795413248931298381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7635913575537327633591365 1431733795413248931298381)
      ·
        refine ⟨536900173279968349236893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1431733795413248931298381 536900173279968349236893)
        ·
          refine ⟨201337564979988130963835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 536900173279968349236893 201337564979988130963835)
          ·
            refine ⟨302006347469982196445753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201337564979988130963835 302006347469982196445753)
            ·
              refine ⟨226504760602486647334315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 302006347469982196445753 226504760602486647334315)
              ·
                refine ⟨339757140903729971001473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226504760602486647334315 339757140903729971001473)
                ·
                  refine ⟨254817855677797478251105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 339757140903729971001473 254817855677797478251105)
                  ·
                    refine ⟨191113391758348108688329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 254817855677797478251105 191113391758348108688329)
                    ·
                      refine ⟨143335043818761081516247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 191113391758348108688329 143335043818761081516247)
                      ·
                        rfl

theorem cell23_279144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_279144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279144 prefixEnd_279144 := by exact prefixLift 279144
  have htrace : WordTrace (prefixWord ++ tailWord_279144) baseStart_279144 baseEnd_279144 := by
    simpa [prefixWord, tailWord_279144, baseEnd_279144] using wordTrace_append hprefix tailTrace_279144
  have hstable : (prefixWord ++ tailWord_279144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279144).length < 2 ^ (prefixWord ++ tailWord_279144).sum := by decide
  have hdescent : baseEnd_279144 < baseStart_279144 := by decide
  rcases family_descends (prefixWord ++ tailWord_279144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279159 : List Nat := [1, 1, 3, 1, 1, 3, 2, 4, 3, 4]
def baseStart_279159 : Nat := 118140960795 + 279159 * 2 ^ 59
def prefixEnd_279159 : Nat := 4983230072969 + 3 ^ 40 * 279159 * 2
def baseEnd_279159 : Nat := 47780915342859507609559

theorem tailTrace_279159 : CollatzResearch.WordTrace tailWord_279159 prefixEnd_279159 47780915342859507609559 := by
  unfold tailWord_279159
  simp only [CollatzResearch.WordTrace]
  refine ⟨10181765195662094406584531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6787843463774729604389687 10181765195662094406584531)
  ·
    refine ⟨15272647793493141609876797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10181765195662094406584531 15272647793493141609876797)
    ·
      refine ⟨5727242922559928103703799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15272647793493141609876797 5727242922559928103703799)
      ·
        refine ⟨8590864383839892155555699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5727242922559928103703799 8590864383839892155555699)
        ·
          refine ⟨12886296575759838233333549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8590864383839892155555699 12886296575759838233333549)
          ·
            refine ⟨4832361215909939337500081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12886296575759838233333549 4832361215909939337500081)
            ·
              refine ⟨3624270911932454503125061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4832361215909939337500081 3624270911932454503125061)
              ·
                refine ⟨679550795987335219335949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3624270911932454503125061 679550795987335219335949)
                ·
                  refine ⟨254831548495250707250981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 679550795987335219335949 254831548495250707250981)
                  ·
                    refine ⟨47780915342859507609559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 254831548495250707250981 47780915342859507609559)
                    ·
                      rfl

theorem cell23_279159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 3, 4].length) (baseStart_279159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279159 prefixEnd_279159 := by exact prefixLift 279159
  have htrace : WordTrace (prefixWord ++ tailWord_279159) baseStart_279159 baseEnd_279159 := by
    simpa [prefixWord, tailWord_279159, baseEnd_279159] using wordTrace_append hprefix tailTrace_279159
  have hstable : (prefixWord ++ tailWord_279159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279159).length < 2 ^ (prefixWord ++ tailWord_279159).sum := by decide
  have hdescent : baseEnd_279159 < baseStart_279159 := by decide
  rcases family_descends (prefixWord ++ tailWord_279159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279210 : List Nat := [3, 1, 5, 2, 1, 1, 1, 2, 3, 4]
def baseStart_279210 : Nat := 118140960795 + 279210 * 2 ^ 59
def prefixEnd_279210 : Nat := 4983230072969 + 3 ^ 40 * 279210 * 2
def baseEnd_279210 : Nat := 47789644513985941096981

theorem tailTrace_279210 : CollatzResearch.WordTrace tailWord_279210 prefixEnd_279210 47789644513985941096981 := by
  unfold tailWord_279210
  simp only [CollatzResearch.WordTrace]
  refine ⟨2545906329619332529172771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6789083545651553411127389 2545906329619332529172771)
  ·
    refine ⟨3818859494428998793759157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2545906329619332529172771 3818859494428998793759157)
    ·
      refine ⟨358018077602718636914921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3818859494428998793759157 358018077602718636914921)
      ·
        refine ⟨268513558202038977686191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 358018077602718636914921 268513558202038977686191)
        ·
          refine ⟨402770337303058466529287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268513558202038977686191 402770337303058466529287)
          ·
            refine ⟨604155505954587699793931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402770337303058466529287 604155505954587699793931)
            ·
              refine ⟨906233258931881549690897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604155505954587699793931 906233258931881549690897)
              ·
                refine ⟨679674944198911162268173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 906233258931881549690897 679674944198911162268173)
                ·
                  refine ⟨254878104074591685850565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 679674944198911162268173 254878104074591685850565)
                  ·
                    refine ⟨47789644513985941096981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 254878104074591685850565 47789644513985941096981)
                    ·
                      rfl

theorem cell23_279210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_279210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279210 prefixEnd_279210 := by exact prefixLift 279210
  have htrace : WordTrace (prefixWord ++ tailWord_279210) baseStart_279210 baseEnd_279210 := by
    simpa [prefixWord, tailWord_279210, baseEnd_279210] using wordTrace_append hprefix tailTrace_279210
  have hstable : (prefixWord ++ tailWord_279210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279210).length < 2 ^ (prefixWord ++ tailWord_279210).sum := by decide
  have hdescent : baseEnd_279210 < baseStart_279210 := by decide
  rcases family_descends (prefixWord ++ tailWord_279210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279219 : List Nat := [1, 1, 1, 2, 3, 4, 2, 1, 3, 5]
def baseStart_279219 : Nat := 118140960795 + 279219 * 2 ^ 59
def prefixEnd_279219 : Nat := 4983230072969 + 3 ^ 40 * 279219 * 2
def baseEnd_279219 : Nat := 47791184955949429359467

theorem tailTrace_279219 : CollatzResearch.WordTrace tailWord_279219 prefixEnd_279219 47791184955949429359467 := by
  unfold tailWord_279219
  simp only [CollatzResearch.WordTrace]
  refine ⟨10183953575444724653768711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6789302383629816435845807 10183953575444724653768711)
  ·
    refine ⟨15275930363167086980653067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10183953575444724653768711 15275930363167086980653067)
    ·
      refine ⟨22913895544750630470979601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15275930363167086980653067 22913895544750630470979601)
      ·
        refine ⟨17185421658562972853234701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22913895544750630470979601 17185421658562972853234701)
        ·
          refine ⟨6444533121961114819963013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17185421658562972853234701 6444533121961114819963013)
          ·
            refine ⟨1208349960367709028743065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6444533121961114819963013 1208349960367709028743065)
            ·
              refine ⟨906262470275781771557299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1208349960367709028743065 906262470275781771557299)
              ·
                refine ⟨1359393705413672657335949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 906262470275781771557299 1359393705413672657335949)
                ·
                  refine ⟨509772639530127246500981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1359393705413672657335949 509772639530127246500981)
                  ·
                    refine ⟨47791184955949429359467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 509772639530127246500981 47791184955949429359467)
                    ·
                      rfl

theorem cell23_279219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 5].length) (baseStart_279219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279219 prefixEnd_279219 := by exact prefixLift 279219
  have htrace : WordTrace (prefixWord ++ tailWord_279219) baseStart_279219 baseEnd_279219 := by
    simpa [prefixWord, tailWord_279219, baseEnd_279219] using wordTrace_append hprefix tailTrace_279219
  have hstable : (prefixWord ++ tailWord_279219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279219).length < 2 ^ (prefixWord ++ tailWord_279219).sum := by decide
  have hdescent : baseEnd_279219 < baseStart_279219 := by decide
  rcases family_descends (prefixWord ++ tailWord_279219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279226 : List Nat := [3, 1, 1, 1, 2, 3, 3, 1, 1, 5, 2]
def baseStart_279226 : Nat := 118140960795 + 279226 * 2 ^ 59
def prefixEnd_279226 : Nat := 4983230072969 + 3 ^ 40 * 279226 * 2
def baseEnd_279226 : Nat := 143377149232429760690869

theorem tailTrace_279226 : CollatzResearch.WordTrace tailWord_279226 prefixEnd_279226 143377149232429760690869 := by
  unfold tailWord_279226
  simp only [CollatzResearch.WordTrace]
  refine ⟨2546052221604841212318383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6789472590946243232849021 2546052221604841212318383)
  ·
    refine ⟨3819078332407261818477575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2546052221604841212318383 3819078332407261818477575)
    ·
      refine ⟨5728617498610892727716363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3819078332407261818477575 5728617498610892727716363)
      ·
        refine ⟨8592926247916339091574545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5728617498610892727716363 8592926247916339091574545)
        ·
          refine ⟨6444694685937254318680909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8592926247916339091574545 6444694685937254318680909)
          ·
            refine ⟨2416760507226470369505341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6444694685937254318680909 2416760507226470369505341)
            ·
              refine ⟨906285190209926388564503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2416760507226470369505341 906285190209926388564503)
              ·
                refine ⟨1359427785314889582846755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 906285190209926388564503 1359427785314889582846755)
                ·
                  refine ⟨2039141677972334374270133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1359427785314889582846755 2039141677972334374270133)
                  ·
                    refine ⟨191169532309906347587825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2039141677972334374270133 191169532309906347587825)
                    ·
                      refine ⟨143377149232429760690869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 191169532309906347587825 143377149232429760690869)
                      ·
                        rfl

theorem cell23_279226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 1, 5, 2].length) (baseStart_279226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279226 prefixEnd_279226 := by exact prefixLift 279226
  have htrace : WordTrace (prefixWord ++ tailWord_279226) baseStart_279226 baseEnd_279226 := by
    simpa [prefixWord, tailWord_279226, baseEnd_279226] using wordTrace_append hprefix tailTrace_279226
  have hstable : (prefixWord ++ tailWord_279226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279226).length < 2 ^ (prefixWord ++ tailWord_279226).sum := by decide
  have hdescent : baseEnd_279226 < baseStart_279226 := by decide
  rcases family_descends (prefixWord ++ tailWord_279226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279239 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 4]
def baseStart_279239 : Nat := 118140960795 + 279239 * 2 ^ 59
def prefixEnd_279239 : Nat := 4983230072969 + 3 ^ 40 * 279239 * 2
def baseEnd_279239 : Nat := 143383824480938209828309

theorem tailTrace_279239 : CollatzResearch.WordTrace tailWord_279239 prefixEnd_279239 143383824480938209828309 := by
  unfold tailWord_279239
  simp only [CollatzResearch.WordTrace]
  refine ⟨10184683035372268069496771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6789788690248178712997847 10184683035372268069496771)
  ·
    refine ⟨15277024553058402104245157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10184683035372268069496771 15277024553058402104245157)
    ·
      refine ⟨2864442103698450394545967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15277024553058402104245157 2864442103698450394545967)
      ·
        refine ⟨4296663155547675591818951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2864442103698450394545967 4296663155547675591818951)
        ·
          refine ⟨6444994733321513387728427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4296663155547675591818951 6444994733321513387728427)
          ·
            refine ⟨9667492099982270081592641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6444994733321513387728427 9667492099982270081592641)
            ·
              refine ⟨7250619074986702561194481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9667492099982270081592641 7250619074986702561194481)
              ·
                refine ⟨5437964306240026920895861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7250619074986702561194481 5437964306240026920895861)
                ·
                  refine ⟨509809153710002523833987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5437964306240026920895861 509809153710002523833987)
                  ·
                    refine ⟨764713730565003785750981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 509809153710002523833987 764713730565003785750981)
                    ·
                      refine ⟨143383824480938209828309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 764713730565003785750981 143383824480938209828309)
                      ·
                        rfl

theorem cell23_279239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_279239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279239 prefixEnd_279239 := by exact prefixLift 279239
  have htrace : WordTrace (prefixWord ++ tailWord_279239) baseStart_279239 baseEnd_279239 := by
    simpa [prefixWord, tailWord_279239, baseEnd_279239] using wordTrace_append hprefix tailTrace_279239
  have hstable : (prefixWord ++ tailWord_279239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279239).length < 2 ^ (prefixWord ++ tailWord_279239).sum := by decide
  have hdescent : baseEnd_279239 < baseStart_279239 := by decide
  rcases family_descends (prefixWord ++ tailWord_279239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279250 : List Nat := [3, 2, 2, 2, 3, 1, 2, 1, 3, 1, 3]
def baseStart_279250 : Nat := 118140960795 + 279250 * 2 ^ 59
def prefixEnd_279250 : Nat := 4983230072969 + 3 ^ 40 * 279250 * 2
def baseEnd_279250 : Nat := 143389472768137666790759

theorem tailTrace_279250 : CollatzResearch.WordTrace tailWord_279250 prefixEnd_279250 143389472768137666790759 := by
  unfold tailWord_279250
  simp only [CollatzResearch.WordTrace]
  refine ⟨2546271059583104237036801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6790056158888277965431469 2546271059583104237036801)
  ·
    refine ⟨1909703294687328177777601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2546271059583104237036801 1909703294687328177777601)
    ·
      refine ⟨1432277471015496133333201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1909703294687328177777601 1432277471015496133333201)
      ·
        refine ⟨1074208103261622099999901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1432277471015496133333201 1074208103261622099999901)
        ·
          refine ⟨402828038723108287499963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1074208103261622099999901 402828038723108287499963)
          ·
            refine ⟨604242058084662431249945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402828038723108287499963 604242058084662431249945)
            ·
              refine ⟨453181543563496823437459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 604242058084662431249945 453181543563496823437459)
              ·
                refine ⟨679772315345245235156189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 453181543563496823437459 679772315345245235156189)
                ·
                  refine ⟨254914618254466963183571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 679772315345245235156189 254914618254466963183571)
                  ·
                    refine ⟨382371927381700444775357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 254914618254466963183571 382371927381700444775357)
                    ·
                      refine ⟨143389472768137666790759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 382371927381700444775357 143389472768137666790759)
                      ·
                        rfl

theorem cell23_279250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_279250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279250 prefixEnd_279250 := by exact prefixLift 279250
  have htrace : WordTrace (prefixWord ++ tailWord_279250) baseStart_279250 baseEnd_279250 := by
    simpa [prefixWord, tailWord_279250, baseEnd_279250] using wordTrace_append hprefix tailTrace_279250
  have hstable : (prefixWord ++ tailWord_279250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279250).length < 2 ^ (prefixWord ++ tailWord_279250).sum := by decide
  have hdescent : baseEnd_279250 < baseStart_279250 := by decide
  rcases family_descends (prefixWord ++ tailWord_279250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279273 : List Nat := [1, 2, 1, 1, 1, 2, 6, 2, 3, 2, 2]
def baseStart_279273 : Nat := 118140960795 + 279273 * 2 ^ 59
def prefixEnd_279273 : Nat := 4983230072969 + 3 ^ 40 * 279273 * 2
def baseEnd_279273 : Nat := 143401282823191076803153

theorem tailTrace_279273 : CollatzResearch.WordTrace tailWord_279273 prefixEnd_279273 143401282823191076803153 := by
  unfold tailWord_279273
  simp only [CollatzResearch.WordTrace]
  refine ⟨10185923117249091876234473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6790615411499394584156315 10185923117249091876234473)
  ·
    refine ⟨7639442337936818907175855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10185923117249091876234473 7639442337936818907175855)
    ·
      refine ⟨11459163506905228360763783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7639442337936818907175855 11459163506905228360763783)
      ·
        refine ⟨17188745260357842541145675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11459163506905228360763783 17188745260357842541145675)
        ·
          refine ⟨25783117890536763811718513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17188745260357842541145675 25783117890536763811718513)
          ·
            refine ⟨19337338417902572858788885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25783117890536763811718513 19337338417902572858788885)
            ·
              refine ⟨906437738339183102755729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19337338417902572858788885 906437738339183102755729)
              ·
                refine ⟨679828303754387327066797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 906437738339183102755729 679828303754387327066797)
                ·
                  refine ⟨254935613907895247650049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 679828303754387327066797 254935613907895247650049)
                  ·
                    refine ⟨191201710430921435737537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 254935613907895247650049 191201710430921435737537)
                    ·
                      refine ⟨143401282823191076803153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 191201710430921435737537 143401282823191076803153)
                      ·
                        rfl

theorem cell23_279273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 3, 2, 2].length) (baseStart_279273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279273 prefixEnd_279273 := by exact prefixLift 279273
  have htrace : WordTrace (prefixWord ++ tailWord_279273) baseStart_279273 baseEnd_279273 := by
    simpa [prefixWord, tailWord_279273, baseEnd_279273] using wordTrace_append hprefix tailTrace_279273
  have hstable : (prefixWord ++ tailWord_279273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279273).length < 2 ^ (prefixWord ++ tailWord_279273).sum := by decide
  have hdescent : baseEnd_279273 < baseStart_279273 := by decide
  rcases family_descends (prefixWord ++ tailWord_279273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279279 : List Nat := [1, 1, 2, 1, 5, 3, 1, 9]
def baseStart_279279 : Nat := 118140960795 + 279279 * 2 ^ 59
def prefixEnd_279279 : Nat := 4983230072969 + 3 ^ 40 * 279279 * 2
def baseEnd_279279 : Nat := 5311272729893261234375

theorem tailTrace_279279 : CollatzResearch.WordTrace tailWord_279279 prefixEnd_279279 5311272729893261234375 := by
  unfold tailWord_279279
  simp only [CollatzResearch.WordTrace]
  refine ⟨10186141955227354900952891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6790761303484903267301927 10186141955227354900952891)
  ·
    refine ⟨15279212932841032351429337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10186141955227354900952891 15279212932841032351429337)
    ·
      refine ⟨11459409699630774263572003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15279212932841032351429337 11459409699630774263572003)
      ·
        refine ⟨17189114549446161395358005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11459409699630774263572003 17189114549446161395358005)
        ·
          refine ⟨1611479489010577630814813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17189114549446161395358005 1611479489010577630814813)
          ·
            refine ⟨604304808378966611555555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1611479489010577630814813 604304808378966611555555)
            ·
              refine ⟨906457212568449917333333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604304808378966611555555 906457212568449917333333)
              ·
                refine ⟨5311272729893261234375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 906457212568449917333333 5311272729893261234375)
                ·
                  rfl

theorem cell23_279279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 9].length) (baseStart_279279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279279 prefixEnd_279279 := by exact prefixLift 279279
  have htrace : WordTrace (prefixWord ++ tailWord_279279) baseStart_279279 baseEnd_279279 := by
    simpa [prefixWord, tailWord_279279, baseEnd_279279] using wordTrace_append hprefix tailTrace_279279
  have hstable : (prefixWord ++ tailWord_279279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279279).length < 2 ^ (prefixWord ++ tailWord_279279).sum := by decide
  have hdescent : baseEnd_279279 < baseStart_279279 := by decide
  rcases family_descends (prefixWord ++ tailWord_279279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279286 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4]
def baseStart_279286 : Nat := 118140960795 + 279286 * 2 ^ 59
def prefixEnd_279286 : Nat := 4983230072969 + 3 ^ 40 * 279286 * 2
def baseEnd_279286 : Nat := 143407958071699525940593

theorem tailTrace_279286 : CollatzResearch.WordTrace tailWord_279286 prefixEnd_279286 143407958071699525940593 := by
  unfold tailWord_279286
  simp only [CollatzResearch.WordTrace]
  refine ⟨636649829137624693528607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6790931510801330064305141 636649829137624693528607)
  ·
    refine ⟨954974743706437040292911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 636649829137624693528607 954974743706437040292911)
    ·
      refine ⟨1432462115559655560439367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 954974743706437040292911 1432462115559655560439367)
      ·
        refine ⟨2148693173339483340659051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1432462115559655560439367 2148693173339483340659051)
        ·
          refine ⟨3223039760009225010988577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2148693173339483340659051 3223039760009225010988577)
          ·
            refine ⟨2417279820006918758241433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3223039760009225010988577 2417279820006918758241433)
            ·
              refine ⟨1812959865005189068681075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2417279820006918758241433 1812959865005189068681075)
              ·
                refine ⟨2719439797507783603021613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1812959865005189068681075 2719439797507783603021613)
                ·
                  refine ⟨1019789924065418851133105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2719439797507783603021613 1019789924065418851133105)
                  ·
                    refine ⟨764842443049064138349829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1019789924065418851133105 764842443049064138349829)
                    ·
                      refine ⟨143407958071699525940593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 764842443049064138349829 143407958071699525940593)
                      ·
                        rfl

theorem cell23_279286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_279286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279286 prefixEnd_279286 := by exact prefixLift 279286
  have htrace : WordTrace (prefixWord ++ tailWord_279286) baseStart_279286 baseEnd_279286 := by
    simpa [prefixWord, tailWord_279286, baseEnd_279286] using wordTrace_append hprefix tailTrace_279286
  have hstable : (prefixWord ++ tailWord_279286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279286).length < 2 ^ (prefixWord ++ tailWord_279286).sum := by decide
  have hdescent : baseEnd_279286 < baseStart_279286 := by decide
  rcases family_descends (prefixWord ++ tailWord_279286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279333 : List Nat := [1, 3, 1, 2, 3, 1, 3, 1, 3, 3, 2]
def baseStart_279333 : Nat := 118140960795 + 279333 * 2 ^ 59
def prefixEnd_279333 : Nat := 4983230072969 + 3 ^ 40 * 279333 * 2
def baseEnd_279333 : Nat := 143432091662460842052877

theorem tailTrace_279333 : CollatzResearch.WordTrace tailWord_279333 prefixEnd_279333 143432091662460842052877 := by
  unfold tailWord_279333
  simp only [CollatzResearch.WordTrace]
  refine ⟨10188111497031722123418653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6792074331354481415612435 10188111497031722123418653)
  ·
    refine ⟨3820541811386895796281995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10188111497031722123418653 3820541811386895796281995)
    ·
      refine ⟨5730812717080343694422993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3820541811386895796281995 5730812717080343694422993)
      ·
        refine ⟨4298109537810257770817245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5730812717080343694422993 4298109537810257770817245)
        ·
          refine ⟨1611791076678846664056467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4298109537810257770817245 1611791076678846664056467)
          ·
            refine ⟨2417686615018269996084701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1611791076678846664056467 2417686615018269996084701)
            ·
              refine ⟨906632480631851248531763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2417686615018269996084701 906632480631851248531763)
              ·
                refine ⟨1359948720947776872797645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 906632480631851248531763 1359948720947776872797645)
                ·
                  refine ⟨509980770355416327299117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1359948720947776872797645 509980770355416327299117)
                  ·
                    refine ⟨191242788883281122737169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 509980770355416327299117 191242788883281122737169)
                    ·
                      refine ⟨143432091662460842052877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 191242788883281122737169 143432091662460842052877)
                      ·
                        rfl

theorem cell23_279333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 3, 2].length) (baseStart_279333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279333 prefixEnd_279333 := by exact prefixLift 279333
  have htrace : WordTrace (prefixWord ++ tailWord_279333) baseStart_279333 baseEnd_279333 := by
    simpa [prefixWord, tailWord_279333, baseEnd_279333] using wordTrace_append hprefix tailTrace_279333
  have hstable : (prefixWord ++ tailWord_279333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279333).length < 2 ^ (prefixWord ++ tailWord_279333).sum := by decide
  have hdescent : baseEnd_279333 < baseStart_279333 := by decide
  rcases family_descends (prefixWord ++ tailWord_279333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279357 : List Nat := [1, 4, 1, 4, 2, 1, 2, 2, 2, 1, 3]
def baseStart_279357 : Nat := 118140960795 + 279357 * 2 ^ 59
def prefixEnd_279357 : Nat := 4983230072969 + 3 ^ 40 * 279357 * 2
def baseEnd_279357 : Nat := 143444415198168748152767

theorem tailTrace_279357 : CollatzResearch.WordTrace tailWord_279357 prefixEnd_279357 143444415198168748152767 := by
  unfold tailWord_279357
  simp only [CollatzResearch.WordTrace]
  refine ⟨10188986848944774222292325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6792657899296516148194883 10188986848944774222292325)
  ·
    refine ⟨1910435034177145166679811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10188986848944774222292325 1910435034177145166679811)
    ·
      refine ⟨2865652551265717750019717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1910435034177145166679811 2865652551265717750019717)
      ·
        refine ⟨537309853362322078128697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2865652551265717750019717 537309853362322078128697)
        ·
          refine ⟨402982390021741558596523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 537309853362322078128697 402982390021741558596523)
          ·
            refine ⟨604473585032612337894785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402982390021741558596523 604473585032612337894785)
            ·
              refine ⟨453355188774459253421089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 604473585032612337894785 453355188774459253421089)
              ·
                refine ⟨340016391580844440065817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 453355188774459253421089 340016391580844440065817)
                ·
                  refine ⟨255012293685633330049363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 340016391580844440065817 255012293685633330049363)
                  ·
                    refine ⟨382518440528449995074045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 255012293685633330049363 382518440528449995074045)
                    ·
                      refine ⟨143444415198168748152767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 382518440528449995074045 143444415198168748152767)
                      ·
                        rfl

theorem cell23_279357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_279357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279357 prefixEnd_279357 := by exact prefixLift 279357
  have htrace : WordTrace (prefixWord ++ tailWord_279357) baseStart_279357 baseEnd_279357 := by
    simpa [prefixWord, tailWord_279357, baseEnd_279357] using wordTrace_append hprefix tailTrace_279357
  have hstable : (prefixWord ++ tailWord_279357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279357).length < 2 ^ (prefixWord ++ tailWord_279357).sum := by decide
  have hdescent : baseEnd_279357 < baseStart_279357 := by decide
  rcases family_descends (prefixWord ++ tailWord_279357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279358 : List Nat := [4, 2, 1, 2, 4, 1, 2, 2, 1, 2, 2]
def baseStart_279358 : Nat := 118140960795 + 279358 * 2 ^ 59
def prefixEnd_279358 : Nat := 4983230072969 + 3 ^ 40 * 279358 * 2
def baseEnd_279358 : Nat := 143444928678823244240263

theorem tailTrace_279358 : CollatzResearch.WordTrace tailWord_279358 prefixEnd_279358 143444928678823244240263 := by
  unfold tailWord_279358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1273627915242643924134841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6792682214627434262052485 1273627915242643924134841)
  ·
    refine ⟨955220936431982943101131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1273627915242643924134841 955220936431982943101131)
    ·
      refine ⟨1432831404647974414651697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 955220936431982943101131 1432831404647974414651697)
      ·
        refine ⟨1074623553485980810988773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1432831404647974414651697 1074623553485980810988773)
        ·
          refine ⟨201491916278621402060395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1074623553485980810988773 201491916278621402060395)
          ·
            refine ⟨302237874417932103090593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201491916278621402060395 302237874417932103090593)
            ·
              refine ⟨226678405813449077317945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 302237874417932103090593 226678405813449077317945)
              ·
                refine ⟨170008804360086807988459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226678405813449077317945 170008804360086807988459)
                ·
                  refine ⟨255013206540130211982689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170008804360086807988459 255013206540130211982689)
                  ·
                    refine ⟨191259904905097658987017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 255013206540130211982689 191259904905097658987017)
                    ·
                      refine ⟨143444928678823244240263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 191259904905097658987017 143444928678823244240263)
                      ·
                        rfl

theorem cell23_279358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_279358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279358 prefixEnd_279358 := by exact prefixLift 279358
  have htrace : WordTrace (prefixWord ++ tailWord_279358) baseStart_279358 baseEnd_279358 := by
    simpa [prefixWord, tailWord_279358, baseEnd_279358] using wordTrace_append hprefix tailTrace_279358
  have hstable : (prefixWord ++ tailWord_279358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279358).length < 2 ^ (prefixWord ++ tailWord_279358).sum := by decide
  have hdescent : baseEnd_279358 < baseStart_279358 := by decide
  rcases family_descends (prefixWord ++ tailWord_279358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279386 : List Nat := [3, 1, 1, 2, 1, 5, 1, 2, 7]
def baseStart_279386 : Nat := 118140960795 + 279386 * 2 ^ 59
def prefixEnd_279386 : Nat := 4983230072969 + 3 ^ 40 * 279386 * 2
def baseEnd_279386 : Nat := 15939922904127681632237

theorem tailTrace_279386 : CollatzResearch.WordTrace tailWord_279386 prefixEnd_279386 15939922904127681632237 := by
  unfold tailWord_279386
  simp only [CollatzResearch.WordTrace]
  refine ⟨2547511141459928043774503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6793363043893141450065341 2547511141459928043774503)
  ·
    refine ⟨3821266712189892065661755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2547511141459928043774503 3821266712189892065661755)
    ·
      refine ⟨5731900068284838098492633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3821266712189892065661755 5731900068284838098492633)
      ·
        refine ⟨4298925051213628573869475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5731900068284838098492633 4298925051213628573869475)
        ·
          refine ⟨6448387576820442860804213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4298925051213628573869475 6448387576820442860804213)
          ·
            refine ⟨604536335326916518200395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6448387576820442860804213 604536335326916518200395)
            ·
              refine ⟨906804502990374777300593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604536335326916518200395 906804502990374777300593)
              ·
                refine ⟨680103377242781082975445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 906804502990374777300593 680103377242781082975445)
                ·
                  refine ⟨15939922904127681632237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 680103377242781082975445 15939922904127681632237)
                  ·
                    rfl

theorem cell23_279386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 7].length) (baseStart_279386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279386 prefixEnd_279386 := by exact prefixLift 279386
  have htrace : WordTrace (prefixWord ++ tailWord_279386) baseStart_279386 baseEnd_279386 := by
    simpa [prefixWord, tailWord_279386, baseEnd_279386] using wordTrace_append hprefix tailTrace_279386
  have hstable : (prefixWord ++ tailWord_279386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279386).length < 2 ^ (prefixWord ++ tailWord_279386).sum := by decide
  have hdescent : baseEnd_279386 < baseStart_279386 := by decide
  rcases family_descends (prefixWord ++ tailWord_279386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279413 : List Nat := [1, 3, 4, 1, 1, 2, 1, 2, 2, 3, 3]
def baseStart_279413 : Nat := 118140960795 + 279413 * 2 ^ 59
def prefixEnd_279413 : Nat := 4983230072969 + 3 ^ 40 * 279413 * 2
def baseEnd_279413 : Nat := 143473170114820529052509

theorem tailTrace_279413 : CollatzResearch.WordTrace tailWord_279413 prefixEnd_279413 143473170114820529052509 := by
  unfold tailWord_279413
  simp only [CollatzResearch.WordTrace]
  refine ⟨10191029336741895786330893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6794019557827930524220595 10191029336741895786330893)
  ·
    refine ⟨3821636001278210919874085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10191029336741895786330893 3821636001278210919874085)
    ·
      refine ⟨716556750239664547476391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3821636001278210919874085 716556750239664547476391)
      ·
        refine ⟨1074835125359496821214587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 716556750239664547476391 1074835125359496821214587)
        ·
          refine ⟨1612252688039245231821881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1074835125359496821214587 1612252688039245231821881)
          ·
            refine ⟨1209189516029433923866411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1612252688039245231821881 1209189516029433923866411)
            ·
              refine ⟨1813784274044150885799617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1209189516029433923866411 1813784274044150885799617)
              ·
                refine ⟨1360338205533113164349713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1813784274044150885799617 1360338205533113164349713)
                ·
                  refine ⟨1020253654149834873262285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1360338205533113164349713 1020253654149834873262285)
                  ·
                    refine ⟨382595120306188077473357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1020253654149834873262285 382595120306188077473357)
                    ·
                      refine ⟨143473170114820529052509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 382595120306188077473357 143473170114820529052509)
                      ·
                        rfl

theorem cell23_279413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_279413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279413 prefixEnd_279413 := by exact prefixLift 279413
  have htrace : WordTrace (prefixWord ++ tailWord_279413) baseStart_279413 baseEnd_279413 := by
    simpa [prefixWord, tailWord_279413, baseEnd_279413] using wordTrace_append hprefix tailTrace_279413
  have hstable : (prefixWord ++ tailWord_279413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279413).length < 2 ^ (prefixWord ++ tailWord_279413).sum := by decide
  have hdescent : baseEnd_279413 < baseStart_279413 := by decide
  rcases family_descends (prefixWord ++ tailWord_279413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279414 : List Nat := [5, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2]
def baseStart_279414 : Nat := 118140960795 + 279414 * 2 ^ 59
def prefixEnd_279414 : Nat := 4983230072969 + 3 ^ 40 * 279414 * 2
def baseEnd_279414 : Nat := 143473683595475025140005

theorem tailTrace_279414 : CollatzResearch.WordTrace tailWord_279414 prefixEnd_279414 143473683595475025140005 := by
  unfold tailWord_279414
  simp only [CollatzResearch.WordTrace]
  refine ⟨636941613108642059819831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6794043873158848638078197 636941613108642059819831)
  ·
    refine ⟨955412419662963089729747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 636941613108642059819831 955412419662963089729747)
    ·
      refine ⟨1433118629494444634594621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 955412419662963089729747 1433118629494444634594621)
      ·
        refine ⟨537419486060416737972983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1433118629494444634594621 537419486060416737972983)
        ·
          refine ⟨806129229090625106959475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537419486060416737972983 806129229090625106959475)
          ·
            refine ⟨1209193843635937660439213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 806129229090625106959475 1209193843635937660439213)
            ·
              refine ⟨453447691363476622664705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1209193843635937660439213 453447691363476622664705)
              ·
                refine ⟨340085768522607466998529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 453447691363476622664705 340085768522607466998529)
                ·
                  refine ⟨255064326391955600248897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 340085768522607466998529 255064326391955600248897)
                  ·
                    refine ⟨191298244793966700186673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 255064326391955600248897 191298244793966700186673)
                    ·
                      refine ⟨143473683595475025140005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 191298244793966700186673 143473683595475025140005)
                      ·
                        rfl

theorem cell23_279414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_279414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279414 prefixEnd_279414 := by exact prefixLift 279414
  have htrace : WordTrace (prefixWord ++ tailWord_279414) baseStart_279414 baseEnd_279414 := by
    simpa [prefixWord, tailWord_279414, baseEnd_279414] using wordTrace_append hprefix tailTrace_279414
  have hstable : (prefixWord ++ tailWord_279414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279414).length < 2 ^ (prefixWord ++ tailWord_279414).sum := by decide
  have hdescent : baseEnd_279414 < baseStart_279414 := by decide
  rcases family_descends (prefixWord ++ tailWord_279414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279436 : List Nat := [2, 2, 1, 2, 1, 2, 3, 2, 1, 3, 4]
def baseStart_279436 : Nat := 118140960795 + 279436 * 2 ^ 59
def prefixEnd_279436 : Nat := 4983230072969 + 3 ^ 40 * 279436 * 2
def baseEnd_279436 : Nat := 143484980169873939064903

theorem tailTrace_279436 : CollatzResearch.WordTrace tailWord_279436 prefixEnd_279436 143484980169873939064903 := by
  unfold tailWord_279436
  simp only [CollatzResearch.WordTrace]
  refine ⟨5095934107829285357209081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6794578810439047142945441 5095934107829285357209081)
  ·
    refine ⟨3821950580871964017906811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5095934107829285357209081 3821950580871964017906811)
    ·
      refine ⟨5732925871307946026860217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3821950580871964017906811 5732925871307946026860217)
      ·
        refine ⟨4299694403480959520145163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5732925871307946026860217 4299694403480959520145163)
        ·
          refine ⟨6449541605221439280217745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4299694403480959520145163 6449541605221439280217745)
          ·
            refine ⟨4837156203916079460163309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6449541605221439280217745 4837156203916079460163309)
            ·
              refine ⟨1813933576468529797561241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4837156203916079460163309 1813933576468529797561241)
              ·
                refine ⟨1360450182351397348170931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1813933576468529797561241 1360450182351397348170931)
                ·
                  refine ⟨2040675273527096022256397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1360450182351397348170931 2040675273527096022256397)
                  ·
                    refine ⟨765253227572661008346149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2040675273527096022256397 765253227572661008346149)
                    ·
                      refine ⟨143484980169873939064903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 765253227572661008346149 143484980169873939064903)
                      ·
                        rfl

theorem cell23_279436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_279436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279436 prefixEnd_279436 := by exact prefixLift 279436
  have htrace : WordTrace (prefixWord ++ tailWord_279436) baseStart_279436 baseEnd_279436 := by
    simpa [prefixWord, tailWord_279436, baseEnd_279436] using wordTrace_append hprefix tailTrace_279436
  have hstable : (prefixWord ++ tailWord_279436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279436).length < 2 ^ (prefixWord ++ tailWord_279436).sum := by decide
  have hdescent : baseEnd_279436 < baseStart_279436 := by decide
  rcases family_descends (prefixWord ++ tailWord_279436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279453 : List Nat := [1, 4, 2, 1, 2, 1, 2, 3, 2, 1, 4]
def baseStart_279453 : Nat := 118140960795 + 279453 * 2 ^ 59
def prefixEnd_279453 : Nat := 4983230072969 + 3 ^ 40 * 279453 * 2
def baseEnd_279453 : Nat := 143493709341000372552325

theorem tailTrace_279453 : CollatzResearch.WordTrace tailWord_279453 prefixEnd_279453 143493709341000372552325 := by
  unfold tailWord_279453
  simp only [CollatzResearch.WordTrace]
  refine ⟨10192488256596982617787013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6794992171064655078524675 10192488256596982617787013)
  ·
    refine ⟨1911091548111934240835065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10192488256596982617787013 1911091548111934240835065)
    ·
      refine ⟨1433318661083950680626299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1911091548111934240835065 1433318661083950680626299)
      ·
        refine ⟨2149977991625926020939449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1433318661083950680626299 2149977991625926020939449)
        ·
          refine ⟨1612483493719444515704587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2149977991625926020939449 1612483493719444515704587)
          ·
            refine ⟨2418725240579166773556881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1612483493719444515704587 2418725240579166773556881)
            ·
              refine ⟨1814043930434375080167661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2418725240579166773556881 1814043930434375080167661)
              ·
                refine ⟨680266473912890655062873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1814043930434375080167661 680266473912890655062873)
                ·
                  refine ⟨510199855434667991297155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 680266473912890655062873 510199855434667991297155)
                  ·
                    refine ⟨765299783152001986945733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 510199855434667991297155 765299783152001986945733)
                    ·
                      refine ⟨143493709341000372552325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 765299783152001986945733 143493709341000372552325)
                      ·
                        rfl

theorem cell23_279453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_279453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279453 prefixEnd_279453 := by exact prefixLift 279453
  have htrace : WordTrace (prefixWord ++ tailWord_279453) baseStart_279453 baseEnd_279453 := by
    simpa [prefixWord, tailWord_279453, baseEnd_279453] using wordTrace_append hprefix tailTrace_279453
  have hstable : (prefixWord ++ tailWord_279453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279453).length < 2 ^ (prefixWord ++ tailWord_279453).sum := by decide
  have hdescent : baseEnd_279453 < baseStart_279453 := by decide
  rcases family_descends (prefixWord ++ tailWord_279453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279480 : List Nat := [2, 1, 2, 1, 2, 6, 1, 1, 3, 4]
def baseStart_279480 : Nat := 118140960795 + 279480 * 2 ^ 59
def prefixEnd_279480 : Nat := 4983230072969 + 3 ^ 40 * 279480 * 2
def baseEnd_279480 : Nat := 47835857772890588971567

theorem tailTrace_279480 : CollatzResearch.WordTrace tailWord_279480 prefixEnd_279480 47835857772890588971567 := by
  unfold tailWord_279480
  simp only [CollatzResearch.WordTrace]
  refine ⟨5096736513749583114509947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6795648684999444152679929 5096736513749583114509947)
  ·
    refine ⟨7645104770624374671764921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5096736513749583114509947 7645104770624374671764921)
    ·
      refine ⟨5733828577968281003823691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7645104770624374671764921 5733828577968281003823691)
      ·
        refine ⟨8600742866952421505735537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5733828577968281003823691 8600742866952421505735537)
        ·
          refine ⟨6450557150214316129301653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8600742866952421505735537 6450557150214316129301653)
          ·
            refine ⟨302369866416296068561015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6450557150214316129301653 302369866416296068561015)
            ·
              refine ⟨453554799624444102841523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302369866416296068561015 453554799624444102841523)
              ·
                refine ⟨680332199436666154262285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 453554799624444102841523 680332199436666154262285)
                ·
                  refine ⟨255124574788749807848357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 680332199436666154262285 255124574788749807848357)
                  ·
                    refine ⟨47835857772890588971567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 255124574788749807848357 47835857772890588971567)
                    ·
                      rfl

theorem cell23_279480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 3, 4].length) (baseStart_279480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279480 prefixEnd_279480 := by exact prefixLift 279480
  have htrace : WordTrace (prefixWord ++ tailWord_279480) baseStart_279480 baseEnd_279480 := by
    simpa [prefixWord, tailWord_279480, baseEnd_279480] using wordTrace_append hprefix tailTrace_279480
  have hstable : (prefixWord ++ tailWord_279480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279480).length < 2 ^ (prefixWord ++ tailWord_279480).sum := by decide
  have hdescent : baseEnd_279480 < baseStart_279480 := by decide
  rcases family_descends (prefixWord ++ tailWord_279480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279536 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 5, 6]
def baseStart_279536 : Nat := 118140960795 + 279536 * 2 ^ 59
def prefixEnd_279536 : Nat := 4983230072969 + 3 ^ 40 * 279536 * 2
def baseEnd_279536 : Nat := 47845442745107849271481

theorem tailTrace_279536 : CollatzResearch.WordTrace tailWord_279536 prefixEnd_279536 47845442745107849271481 := by
  unfold tailWord_279536
  simp only [CollatzResearch.WordTrace]
  refine ⟨5097757757648143896529231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6797010343530858528705641 5097757757648143896529231)
  ·
    refine ⟨7646636636472215844793847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5097757757648143896529231 7646636636472215844793847)
    ·
      refine ⟨11469954954708323767190771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7646636636472215844793847 11469954954708323767190771)
      ·
        refine ⟨17204932432062485650786157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11469954954708323767190771 17204932432062485650786157)
        ·
          refine ⟨6451849662023432119044809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17204932432062485650786157 6451849662023432119044809)
          ·
            refine ⟨4838887246517574089283607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6451849662023432119044809 4838887246517574089283607)
            ·
              refine ⟨7258330869776361133925411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4838887246517574089283607 7258330869776361133925411)
              ·
                refine ⟨10887496304664541700888117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7258330869776361133925411 10887496304664541700888117)
                ·
                  refine ⟨1020702778562300784458261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10887496304664541700888117 1020702778562300784458261)
                  ·
                    refine ⟨47845442745107849271481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1020702778562300784458261 47845442745107849271481)
                    ·
                      rfl

theorem cell23_279536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 5, 6].length) (baseStart_279536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279536 prefixEnd_279536 := by exact prefixLift 279536
  have htrace : WordTrace (prefixWord ++ tailWord_279536) baseStart_279536 baseEnd_279536 := by
    simpa [prefixWord, tailWord_279536, baseEnd_279536] using wordTrace_append hprefix tailTrace_279536
  have hstable : (prefixWord ++ tailWord_279536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279536).length < 2 ^ (prefixWord ++ tailWord_279536).sum := by decide
  have hdescent : baseEnd_279536 < baseStart_279536 := by decide
  rcases family_descends (prefixWord ++ tailWord_279536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279553 : List Nat := [1, 2, 4, 1, 2, 2, 1, 3, 1, 6]
def baseStart_279553 : Nat := 118140960795 + 279553 * 2 ^ 59
def prefixEnd_279553 : Nat := 4983230072969 + 3 ^ 40 * 279553 * 2
def baseEnd_279553 : Nat := 47848352468816660433955

theorem tailTrace_279553 : CollatzResearch.WordTrace tailWord_279553 prefixEnd_279553 47848352468816660433955 := by
  unfold tailWord_279553
  simp only [CollatzResearch.WordTrace]
  refine ⟨10196135556234699696427313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6797423704156466464284875 10196135556234699696427313)
  ·
    refine ⟨7647101667176024772320485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10196135556234699696427313 7647101667176024772320485)
    ·
      refine ⟨1433831562595504644810091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7647101667176024772320485 1433831562595504644810091)
      ·
        refine ⟨2150747343893256967215137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1433831562595504644810091 2150747343893256967215137)
        ·
          refine ⟨1613060507919942725411353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2150747343893256967215137 1613060507919942725411353)
          ·
            refine ⟨1209795380939957044058515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1613060507919942725411353 1209795380939957044058515)
            ·
              refine ⟨1814693071409935566087773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1209795380939957044058515 1814693071409935566087773)
              ·
                refine ⟨680509901778725837282915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1814693071409935566087773 680509901778725837282915)
                ·
                  refine ⟨1020764852668088755924373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 680509901778725837282915 1020764852668088755924373)
                  ·
                    refine ⟨47848352468816660433955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1020764852668088755924373 47848352468816660433955)
                    ·
                      rfl

theorem cell23_279553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_279553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279553 prefixEnd_279553 := by exact prefixLift 279553
  have htrace : WordTrace (prefixWord ++ tailWord_279553) baseStart_279553 baseEnd_279553 := by
    simpa [prefixWord, tailWord_279553, baseEnd_279553] using wordTrace_append hprefix tailTrace_279553
  have hstable : (prefixWord ++ tailWord_279553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279553).length < 2 ^ (prefixWord ++ tailWord_279553).sum := by decide
  have hdescent : baseEnd_279553 < baseStart_279553 := by decide
  rcases family_descends (prefixWord ++ tailWord_279553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279587 : List Nat := [1, 1, 1, 4, 3, 4, 1, 2, 2, 4]
def baseStart_279587 : Nat := 118140960795 + 279587 * 2 ^ 59
def prefixEnd_279587 : Nat := 4983230072969 + 3 ^ 40 * 279587 * 2
def baseEnd_279587 : Nat := 47854171916234282758903

theorem tailTrace_279587 : CollatzResearch.WordTrace tailWord_279587 prefixEnd_279587 47854171916234282758903 := by
  unfold tailWord_279587
  simp only [CollatzResearch.WordTrace]
  refine ⟨10197375638111523503165015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6798250425407682335443343 10197375638111523503165015)
  ·
    refine ⟨15296063457167285254747523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10197375638111523503165015 15296063457167285254747523)
    ·
      refine ⟨22944095185750927882121285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15296063457167285254747523 22944095185750927882121285)
      ·
        refine ⟨4302017847328298977897741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22944095185750927882121285 4302017847328298977897741)
        ·
          refine ⟨1613256692748112116711653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4302017847328298977897741 1613256692748112116711653)
          ·
            refine ⟨302485629890271021883435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1613256692748112116711653 302485629890271021883435)
            ·
              refine ⟨453728444835406532825153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302485629890271021883435 453728444835406532825153)
              ·
                refine ⟨340296333626554899618865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 453728444835406532825153 340296333626554899618865)
                ·
                  refine ⟨255222250219916174714149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 340296333626554899618865 255222250219916174714149)
                  ·
                    refine ⟨47854171916234282758903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 255222250219916174714149 47854171916234282758903)
                    ·
                      rfl

theorem cell23_279587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 2, 4].length) (baseStart_279587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279587 prefixEnd_279587 := by exact prefixLift 279587
  have htrace : WordTrace (prefixWord ++ tailWord_279587) baseStart_279587 baseEnd_279587 := by
    simpa [prefixWord, tailWord_279587, baseEnd_279587] using wordTrace_append hprefix tailTrace_279587
  have hstable : (prefixWord ++ tailWord_279587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279587).length < 2 ^ (prefixWord ++ tailWord_279587).sum := by decide
  have hdescent : baseEnd_279587 < baseStart_279587 := by decide
  rcases family_descends (prefixWord ++ tailWord_279587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279610 : List Nat := [3, 1, 1, 1, 3, 1, 5, 1, 1, 3, 3]
def baseStart_279610 : Nat := 118140960795 + 279610 * 2 ^ 59
def prefixEnd_279610 : Nat := 4983230072969 + 3 ^ 40 * 279610 * 2
def baseEnd_279610 : Nat := 143574325803756258289103

theorem tailTrace_279610 : CollatzResearch.WordTrace tailWord_279610 prefixEnd_279610 143574325803756258289103 := by
  unfold tailWord_279610
  simp only [CollatzResearch.WordTrace]
  refine ⟨2549553629257049607813071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6798809678018798954168189 2549553629257049607813071)
  ·
    refine ⟨3824330443885574411719607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2549553629257049607813071 3824330443885574411719607)
    ·
      refine ⟨5736495665828361617579411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3824330443885574411719607 5736495665828361617579411)
      ·
        refine ⟨8604743498742542426369117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5736495665828361617579411 8604743498742542426369117)
        ·
          refine ⟨3226778812028453409888419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8604743498742542426369117 3226778812028453409888419)
          ·
            refine ⟨4840168218042680114832629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3226778812028453409888419 4840168218042680114832629)
            ·
              refine ⟨453765770441501260765559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4840168218042680114832629 453765770441501260765559)
              ·
                refine ⟨680648655662251891148339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 453765770441501260765559 680648655662251891148339)
                ·
                  refine ⟨1020972983493377836722509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 680648655662251891148339 1020972983493377836722509)
                  ·
                    refine ⟨382864868810016688770941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1020972983493377836722509 382864868810016688770941)
                    ·
                      refine ⟨143574325803756258289103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 382864868810016688770941 143574325803756258289103)
                      ·
                        rfl

theorem cell23_279610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 1, 3, 3].length) (baseStart_279610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279610 prefixEnd_279610 := by exact prefixLift 279610
  have htrace : WordTrace (prefixWord ++ tailWord_279610) baseStart_279610 baseEnd_279610 := by
    simpa [prefixWord, tailWord_279610, baseEnd_279610] using wordTrace_append hprefix tailTrace_279610
  have hstable : (prefixWord ++ tailWord_279610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279610).length < 2 ^ (prefixWord ++ tailWord_279610).sum := by decide
  have hdescent : baseEnd_279610 < baseStart_279610 := by decide
  rcases family_descends (prefixWord ++ tailWord_279610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279614 : List Nat := [4, 2, 1, 3, 1, 2, 2, 2, 1, 2, 3]
def baseStart_279614 : Nat := 118140960795 + 279614 * 2 ^ 59
def prefixEnd_279614 : Nat := 4983230072969 + 3 ^ 40 * 279614 * 2
def baseEnd_279614 : Nat := 143576379726374242639085

theorem tailTrace_279614 : CollatzResearch.WordTrace tailWord_279614 prefixEnd_279614 143576379726374242639085 := by
  unfold tailWord_279614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1274795051126713389299737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6798906939342471409598597 1274795051126713389299737)
  ·
    refine ⟨956096288345035041974803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1274795051126713389299737 956096288345035041974803)
    ·
      refine ⟨1434144432517552562962205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 956096288345035041974803 1434144432517552562962205)
      ·
        refine ⟨537804162194082211110827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1434144432517552562962205 537804162194082211110827)
        ·
          refine ⟨806706243291123316666241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537804162194082211110827 806706243291123316666241)
          ·
            refine ⟨605029682468342487499681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 806706243291123316666241 605029682468342487499681)
            ·
              refine ⟨453772261851256865624761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 605029682468342487499681 453772261851256865624761)
              ·
                refine ⟨340329196388442649218571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 453772261851256865624761 340329196388442649218571)
                ·
                  refine ⟨510493794582663973827857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 340329196388442649218571 510493794582663973827857)
                  ·
                    refine ⟨382870345936997980370893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 510493794582663973827857 382870345936997980370893)
                    ·
                      refine ⟨143576379726374242639085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 382870345936997980370893 143576379726374242639085)
                      ·
                        rfl

theorem cell23_279614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_279614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279614 prefixEnd_279614 := by exact prefixLift 279614
  have htrace : WordTrace (prefixWord ++ tailWord_279614) baseStart_279614 baseEnd_279614 := by
    simpa [prefixWord, tailWord_279614, baseEnd_279614] using wordTrace_append hprefix tailTrace_279614
  have hstable : (prefixWord ++ tailWord_279614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279614).length < 2 ^ (prefixWord ++ tailWord_279614).sum := by decide
  have hdescent : baseEnd_279614 < baseStart_279614 := by decide
  rcases family_descends (prefixWord ++ tailWord_279614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279617 : List Nat := [1, 2, 5, 1, 3, 2, 2, 7]
def baseStart_279617 : Nat := 118140960795 + 279617 * 2 ^ 59
def prefixEnd_279617 : Nat := 4983230072969 + 3 ^ 40 * 279617 * 2
def baseEnd_279617 : Nat := 5317700746975471514873

theorem tailTrace_279617 : CollatzResearch.WordTrace tailWord_279617 prefixEnd_279617 5317700746975471514873 := by
  unfold tailWord_279617
  simp only [CollatzResearch.WordTrace]
  refine ⟨10198469828002838626757105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6798979885335225751171403 10198469828002838626757105)
  ·
    refine ⟨7648852371002128970067829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10198469828002838626757105 7648852371002128970067829)
    ·
      refine ⟨717079909781449590943859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7648852371002128970067829 717079909781449590943859)
      ·
        refine ⟨1075619864672174386415789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 717079909781449590943859 1075619864672174386415789)
        ·
          refine ⟨403357449252065394905921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1075619864672174386415789 403357449252065394905921)
          ·
            refine ⟨302518086939049046179441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 403357449252065394905921 302518086939049046179441)
            ·
              refine ⟨226888565204286784634581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 302518086939049046179441 226888565204286784634581)
              ·
                refine ⟨5317700746975471514873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 226888565204286784634581 5317700746975471514873)
                ·
                  rfl

theorem cell23_279617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 7].length) (baseStart_279617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279617 prefixEnd_279617 := by exact prefixLift 279617
  have htrace : WordTrace (prefixWord ++ tailWord_279617) baseStart_279617 baseEnd_279617 := by
    simpa [prefixWord, tailWord_279617, baseEnd_279617] using wordTrace_append hprefix tailTrace_279617
  have hstable : (prefixWord ++ tailWord_279617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279617).length < 2 ^ (prefixWord ++ tailWord_279617).sum := by decide
  have hdescent : baseEnd_279617 < baseStart_279617 := by decide
  rcases family_descends (prefixWord ++ tailWord_279617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279623 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 5]
def baseStart_279623 : Nat := 118140960795 + 279623 * 2 ^ 59
def prefixEnd_279623 : Nat := 4983230072969 + 3 ^ 40 * 279623 * 2
def baseEnd_279623 : Nat := 143581001052264707426543

theorem tailTrace_279623 : CollatzResearch.WordTrace tailWord_279623 prefixEnd_279623 143581001052264707426543 := by
  unfold tailWord_279623
  simp only [CollatzResearch.WordTrace]
  refine ⟨10198688665981101651475523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6799125777320734434317015 10198688665981101651475523)
  ·
    refine ⟨15298032998971652477213285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10198688665981101651475523 15298032998971652477213285)
    ·
      refine ⟨2868381187307184839477491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15298032998971652477213285 2868381187307184839477491)
      ·
        refine ⟨4302571780960777259216237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2868381187307184839477491 4302571780960777259216237)
        ·
          refine ⟨1613464417860291472206089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4302571780960777259216237 1613464417860291472206089)
          ·
            refine ⟨1210098313395218604154567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1613464417860291472206089 1210098313395218604154567)
            ·
              refine ⟨1815147470092827906231851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1210098313395218604154567 1815147470092827906231851)
              ·
                refine ⟨2722721205139241859347777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1815147470092827906231851 2722721205139241859347777)
                ·
                  refine ⟨2042040903854431394510833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2722721205139241859347777 2042040903854431394510833)
                  ·
                    refine ⟨1531530677890823545883125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2042040903854431394510833 1531530677890823545883125)
                    ·
                      refine ⟨143581001052264707426543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1531530677890823545883125 143581001052264707426543)
                      ·
                        rfl

theorem cell23_279623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_279623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279623 prefixEnd_279623 := by exact prefixLift 279623
  have htrace : WordTrace (prefixWord ++ tailWord_279623) baseStart_279623 baseEnd_279623 := by
    simpa [prefixWord, tailWord_279623, baseEnd_279623] using wordTrace_append hprefix tailTrace_279623
  have hstable : (prefixWord ++ tailWord_279623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279623).length < 2 ^ (prefixWord ++ tailWord_279623).sum := by decide
  have hdescent : baseEnd_279623 < baseStart_279623 := by decide
  rcases family_descends (prefixWord ++ tailWord_279623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279637 : List Nat := [1, 3, 2, 2, 1, 2, 1, 5, 1, 3, 2]
def baseStart_279637 : Nat := 118140960795 + 279637 * 2 ^ 59
def prefixEnd_279637 : Nat := 4983230072969 + 3 ^ 40 * 279637 * 2
def baseEnd_279637 : Nat := 143588189781427652651479

theorem tailTrace_279637 : CollatzResearch.WordTrace tailWord_279637 prefixEnd_279637 143588189781427652651479 := by
  unfold tailWord_279637
  simp only [CollatzResearch.WordTrace]
  refine ⟨10199199287930382042485165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6799466191953588028323443 10199199287930382042485165)
  ·
    refine ⟨3824699732973893265931937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10199199287930382042485165 3824699732973893265931937)
    ·
      refine ⟨2868524799730419949448953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3824699732973893265931937 2868524799730419949448953)
      ·
        refine ⟨2151393599797814962086715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2868524799730419949448953 2151393599797814962086715)
        ·
          refine ⟨3227090399696722443130073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2151393599797814962086715 3227090399696722443130073)
          ·
            refine ⟨2420317799772541832347555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3227090399696722443130073 2420317799772541832347555)
            ·
              refine ⟨3630476699658812748521333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2420317799772541832347555 3630476699658812748521333)
              ·
                refine ⟨340357190593013695173875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3630476699658812748521333 340357190593013695173875)
                ·
                  refine ⟨510535785889520542760813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 340357190593013695173875 510535785889520542760813)
                  ·
                    refine ⟨191450919708570203535305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 510535785889520542760813 191450919708570203535305)
                    ·
                      refine ⟨143588189781427652651479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 191450919708570203535305 143588189781427652651479)
                      ·
                        rfl

theorem cell23_279637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_279637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279637 prefixEnd_279637 := by exact prefixLift 279637
  have htrace : WordTrace (prefixWord ++ tailWord_279637) baseStart_279637 baseEnd_279637 := by
    simpa [prefixWord, tailWord_279637, baseEnd_279637] using wordTrace_append hprefix tailTrace_279637
  have hstable : (prefixWord ++ tailWord_279637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279637).length < 2 ^ (prefixWord ++ tailWord_279637).sum := by decide
  have hdescent : baseEnd_279637 < baseStart_279637 := by decide
  rcases family_descends (prefixWord ++ tailWord_279637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279645 : List Nat := [1, 4, 4, 1, 2, 1, 3, 2, 1, 2, 2]
def baseStart_279645 : Nat := 118140960795 + 279645 * 2 ^ 59
def prefixEnd_279645 : Nat := 4983230072969 + 3 ^ 40 * 279645 * 2
def baseEnd_279645 : Nat := 143592297626663621351443

theorem tailTrace_279645 : CollatzResearch.WordTrace tailWord_279645 prefixEnd_279645 143592297626663621351443 := by
  unfold tailWord_279645
  simp only [CollatzResearch.WordTrace]
  refine ⟨10199491071901399408776389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6799660714600932939184259 10199491071901399408776389)
  ·
    refine ⟨1912404575981512389145573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10199491071901399408776389 1912404575981512389145573)
    ·
      refine ⟨358575857996533572964795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1912404575981512389145573 358575857996533572964795)
      ·
        refine ⟨537863786994800359447193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358575857996533572964795 537863786994800359447193)
        ·
          refine ⟨403397840246100269585395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 537863786994800359447193 403397840246100269585395)
          ·
            refine ⟨605096760369150404378093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403397840246100269585395 605096760369150404378093)
            ·
              refine ⟨226911285138431401641785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 605096760369150404378093 226911285138431401641785)
              ·
                refine ⟨170183463853823551231339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226911285138431401641785 170183463853823551231339)
                ·
                  refine ⟨255275195780735326847009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170183463853823551231339 255275195780735326847009)
                  ·
                    refine ⟨191456396835551495135257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 255275195780735326847009 191456396835551495135257)
                    ·
                      refine ⟨143592297626663621351443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 191456396835551495135257 143592297626663621351443)
                      ·
                        rfl

theorem cell23_279645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_279645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279645 prefixEnd_279645 := by exact prefixLift 279645
  have htrace : WordTrace (prefixWord ++ tailWord_279645) baseStart_279645 baseEnd_279645 := by
    simpa [prefixWord, tailWord_279645, baseEnd_279645] using wordTrace_append hprefix tailTrace_279645
  have hstable : (prefixWord ++ tailWord_279645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279645).length < 2 ^ (prefixWord ++ tailWord_279645).sum := by decide
  have hdescent : baseEnd_279645 < baseStart_279645 := by decide
  rcases family_descends (prefixWord ++ tailWord_279645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279653 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 1, 3, 5]
def baseStart_279653 : Nat := 118140960795 + 279653 * 2 ^ 59
def prefixEnd_279653 : Nat := 4983230072969 + 3 ^ 40 * 279653 * 2
def baseEnd_279653 : Nat := 143596405471899590051405

theorem tailTrace_279653 : CollatzResearch.WordTrace tailWord_279653 prefixEnd_279653 143596405471899590051405 := by
  unfold tailWord_279653
  simp only [CollatzResearch.WordTrace]
  refine ⟨10199782855872416775067613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6799855237248277850045075 10199782855872416775067613)
  ·
    refine ⟨3824918570952156290650355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10199782855872416775067613 3824918570952156290650355)
    ·
      refine ⟨5737377856428234435975533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3824918570952156290650355 5737377856428234435975533)
      ·
        refine ⟨2151516696160587913490825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5737377856428234435975533 2151516696160587913490825)
        ·
          refine ⟨1613637522120440935118119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2151516696160587913490825 1613637522120440935118119)
          ·
            refine ⟨2420456283180661402677179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1613637522120440935118119 2420456283180661402677179)
            ·
              refine ⟨3630684424770992104015769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2420456283180661402677179 3630684424770992104015769)
              ·
                refine ⟨2723013318578244078011827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3630684424770992104015769 2723013318578244078011827)
                ·
                  refine ⟨4084519977867366117017741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2723013318578244078011827 4084519977867366117017741)
                  ·
                    refine ⟨1531694991700262293881653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4084519977867366117017741 1531694991700262293881653)
                    ·
                      refine ⟨143596405471899590051405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1531694991700262293881653 143596405471899590051405)
                      ·
                        rfl

theorem cell23_279653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_279653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279653 prefixEnd_279653 := by exact prefixLift 279653
  have htrace : WordTrace (prefixWord ++ tailWord_279653) baseStart_279653 baseEnd_279653 := by
    simpa [prefixWord, tailWord_279653, baseEnd_279653] using wordTrace_append hprefix tailTrace_279653
  have hstable : (prefixWord ++ tailWord_279653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279653).length < 2 ^ (prefixWord ++ tailWord_279653).sum := by decide
  have hdescent : baseEnd_279653 < baseStart_279653 := by decide
  rcases family_descends (prefixWord ++ tailWord_279653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279661 : List Nat := [1, 5, 1, 1, 2, 4, 2, 1, 2, 1, 3]
def baseStart_279661 : Nat := 118140960795 + 279661 * 2 ^ 59
def prefixEnd_279661 : Nat := 4983230072969 + 3 ^ 40 * 279661 * 2
def baseEnd_279661 : Nat := 143600513317135558751369

theorem tailTrace_279661 : CollatzResearch.WordTrace tailWord_279661 prefixEnd_279661 143600513317135558751369 := by
  unfold tailWord_279661
  simp only [CollatzResearch.WordTrace]
  refine ⟨10200074639843434141358837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6800049759895622760905891 10200074639843434141358837)
  ·
    refine ⟨956256997485321950752391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10200074639843434141358837 956256997485321950752391)
    ·
      refine ⟨1434385496227982926128587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 956256997485321950752391 1434385496227982926128587)
      ·
        refine ⟨2151578244341974389192881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1434385496227982926128587 2151578244341974389192881)
        ·
          refine ⟨1613683683256480791894661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2151578244341974389192881 1613683683256480791894661)
          ·
            refine ⟨302565690610590148480249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1613683683256480791894661 302565690610590148480249)
            ·
              refine ⟨226924267957942611360187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 302565690610590148480249 226924267957942611360187)
              ·
                refine ⟨340386401936913917040281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226924267957942611360187 340386401936913917040281)
                ·
                  refine ⟨255289801452685437780211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 340386401936913917040281 255289801452685437780211)
                  ·
                    refine ⟨382934702179028156670317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 255289801452685437780211 382934702179028156670317)
                    ·
                      refine ⟨143600513317135558751369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 382934702179028156670317 143600513317135558751369)
                      ·
                        rfl

theorem cell23_279661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_279661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279661 prefixEnd_279661 := by exact prefixLift 279661
  have htrace : WordTrace (prefixWord ++ tailWord_279661) baseStart_279661 baseEnd_279661 := by
    simpa [prefixWord, tailWord_279661, baseEnd_279661] using wordTrace_append hprefix tailTrace_279661
  have hstable : (prefixWord ++ tailWord_279661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279661).length < 2 ^ (prefixWord ++ tailWord_279661).sum := by decide
  have hdescent : baseEnd_279661 < baseStart_279661 := by decide
  rcases family_descends (prefixWord ++ tailWord_279661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279663 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 4]
def baseStart_279663 : Nat := 118140960795 + 279663 * 2 ^ 59
def prefixEnd_279663 : Nat := 4983230072969 + 3 ^ 40 * 279663 * 2
def baseEnd_279663 : Nat := 143601540278444550926359

theorem tailTrace_279663 : CollatzResearch.WordTrace tailWord_279663 prefixEnd_279663 143601540278444550926359 := by
  unfold tailWord_279663
  simp only [CollatzResearch.WordTrace]
  refine ⟨10200147585836188482931643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6800098390557458988621095 10200147585836188482931643)
  ·
    refine ⟨15300221378754282724397465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10200147585836188482931643 15300221378754282724397465)
    ·
      refine ⟨11475166034065712043298099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15300221378754282724397465 11475166034065712043298099)
      ·
        refine ⟨17212749051098568064947149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11475166034065712043298099 17212749051098568064947149)
        ·
          refine ⟨6454780894161963024355181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17212749051098568064947149 6454780894161963024355181)
          ·
            refine ⟨2420542835310736134133193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6454780894161963024355181 2420542835310736134133193)
            ·
              refine ⟨1815407126483052100599895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2420542835310736134133193 1815407126483052100599895)
              ·
                refine ⟨2723110689724578150899843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1815407126483052100599895 2723110689724578150899843)
                ·
                  refine ⟨4084666034586867226349765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2723110689724578150899843 4084666034586867226349765)
                  ·
                    refine ⟨765874881485037604940581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4084666034586867226349765 765874881485037604940581)
                    ·
                      refine ⟨143601540278444550926359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 765874881485037604940581 143601540278444550926359)
                      ·
                        rfl

theorem cell23_279663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 4].length) (baseStart_279663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279663 prefixEnd_279663 := by exact prefixLift 279663
  have htrace : WordTrace (prefixWord ++ tailWord_279663) baseStart_279663 baseEnd_279663 := by
    simpa [prefixWord, tailWord_279663, baseEnd_279663] using wordTrace_append hprefix tailTrace_279663
  have hstable : (prefixWord ++ tailWord_279663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279663).length < 2 ^ (prefixWord ++ tailWord_279663).sum := by decide
  have hdescent : baseEnd_279663 < baseStart_279663 := by decide
  rcases family_descends (prefixWord ++ tailWord_279663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279670 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5]
def baseStart_279670 : Nat := 118140960795 + 279670 * 2 ^ 59
def prefixEnd_279670 : Nat := 4983230072969 + 3 ^ 40 * 279670 * 2
def baseEnd_279670 : Nat := 143605134643026023538827

theorem tailTrace_279670 : CollatzResearch.WordTrace tailWord_279670 prefixEnd_279670 143605134643026023538827 := by
  unfold tailWord_279670
  simp only [CollatzResearch.WordTrace]
  refine ⟨637525181050676792402279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6800268597873885785624309 637525181050676792402279)
  ·
    refine ⟨956287771576015188603419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 637525181050676792402279 956287771576015188603419)
    ·
      refine ⟨1434431657364022782905129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 956287771576015188603419 1434431657364022782905129)
      ·
        refine ⟨1075823743023017087178847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1434431657364022782905129 1075823743023017087178847)
        ·
          refine ⟨1613735614534525630768271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1075823743023017087178847 1613735614534525630768271)
          ·
            refine ⟨2420603421801788446152407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1613735614534525630768271 2420603421801788446152407)
            ·
              refine ⟨3630905132702682669228611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2420603421801788446152407 3630905132702682669228611)
              ·
                refine ⟨5446357699054024003842917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3630905132702682669228611 5446357699054024003842917)
                ·
                  refine ⟨1021192068572629500720547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5446357699054024003842917 1021192068572629500720547)
                  ·
                    refine ⟨1531788102858944251080821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1021192068572629500720547 1531788102858944251080821)
                    ·
                      refine ⟨143605134643026023538827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1531788102858944251080821 143605134643026023538827)
                      ·
                        rfl

theorem cell23_279670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_279670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279670 prefixEnd_279670 := by exact prefixLift 279670
  have htrace : WordTrace (prefixWord ++ tailWord_279670) baseStart_279670 baseEnd_279670 := by
    simpa [prefixWord, tailWord_279670, baseEnd_279670] using wordTrace_append hprefix tailTrace_279670
  have hstable : (prefixWord ++ tailWord_279670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279670).length < 2 ^ (prefixWord ++ tailWord_279670).sum := by decide
  have hdescent : baseEnd_279670 < baseStart_279670 := by decide
  rcases family_descends (prefixWord ++ tailWord_279670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279737 : List Nat := [1, 2, 1, 4, 1, 5, 1, 1, 2, 5]
def baseStart_279737 : Nat := 118140960795 + 279737 * 2 ^ 59
def prefixEnd_279737 : Nat := 4983230072969 + 3 ^ 40 * 279737 * 2
def baseEnd_279737 : Nat := 47879845948959087133673

theorem tailTrace_279737 : CollatzResearch.WordTrace tailWord_279737 prefixEnd_279737 47879845948959087133673 := by
  unfold tailWord_279737
  simp only [CollatzResearch.WordTrace]
  refine ⟨10202846587568099121125465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6801897725045399414083643 10202846587568099121125465)
  ·
    refine ⟨7652134940676074340844099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10202846587568099121125465 7652134940676074340844099)
    ·
      refine ⟨11478202411014111511266149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7652134940676074340844099 11478202411014111511266149)
      ·
        refine ⟨2152162952065145908362403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11478202411014111511266149 2152162952065145908362403)
        ·
          refine ⟨3228244428097718862543605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2152162952065145908362403 3228244428097718862543605)
          ·
            refine ⟨302647915134161143363463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3228244428097718862543605 302647915134161143363463)
            ·
              refine ⟨453971872701241715045195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302647915134161143363463 453971872701241715045195)
              ·
                refine ⟨680957809051862572567793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 453971872701241715045195 680957809051862572567793)
                ·
                  refine ⟨510718356788896929425845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 680957809051862572567793 510718356788896929425845)
                  ·
                    refine ⟨47879845948959087133673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 510718356788896929425845 47879845948959087133673)
                    ·
                      rfl

theorem cell23_279737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 5].length) (baseStart_279737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279737 prefixEnd_279737 := by exact prefixLift 279737
  have htrace : WordTrace (prefixWord ++ tailWord_279737) baseStart_279737 baseEnd_279737 := by
    simpa [prefixWord, tailWord_279737, baseEnd_279737] using wordTrace_append hprefix tailTrace_279737
  have hstable : (prefixWord ++ tailWord_279737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279737).length < 2 ^ (prefixWord ++ tailWord_279737).sum := by decide
  have hdescent : baseEnd_279737 < baseStart_279737 := by decide
  rcases family_descends (prefixWord ++ tailWord_279737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279763 : List Nat := [1, 1, 1, 2, 1, 1, 1, 7, 8]
def baseStart_279763 : Nat := 118140960795 + 279763 * 2 ^ 59
def prefixEnd_279763 : Nat := 4983230072969 + 3 ^ 40 * 279763 * 2
def baseEnd_279763 : Nat := 15961432038210462186211

theorem tailTrace_279763 : CollatzResearch.WordTrace tailWord_279763 prefixEnd_279763 15961432038210462186211 := by
  unfold tailWord_279763
  simp only [CollatzResearch.WordTrace]
  refine ⟨10203794885473905561571943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6802529923649270374381295 10203794885473905561571943)
  ·
    refine ⟨15305692328210858342357915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10203794885473905561571943 15305692328210858342357915)
    ·
      refine ⟨22958538492316287513536873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15305692328210858342357915 22958538492316287513536873)
      ·
        refine ⟨17218903869237215635152655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22958538492316287513536873 17218903869237215635152655)
        ·
          refine ⟨25828355803855823452728983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17218903869237215635152655 25828355803855823452728983)
          ·
            refine ⟨38742533705783735179093475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25828355803855823452728983 38742533705783735179093475)
            ·
              refine ⟨58113800558675602768640213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38742533705783735179093475 58113800558675602768640213)
              ·
                refine ⟨1362042200593959439890005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 58113800558675602768640213 1362042200593959439890005)
                ·
                  refine ⟨15961432038210462186211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1362042200593959439890005 15961432038210462186211)
                  ·
                    rfl

theorem cell23_279763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 8].length) (baseStart_279763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279763 prefixEnd_279763 := by exact prefixLift 279763
  have htrace : WordTrace (prefixWord ++ tailWord_279763) baseStart_279763 baseEnd_279763 := by
    simpa [prefixWord, tailWord_279763, baseEnd_279763] using wordTrace_append hprefix tailTrace_279763
  have hstable : (prefixWord ++ tailWord_279763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279763).length < 2 ^ (prefixWord ++ tailWord_279763).sum := by decide
  have hdescent : baseEnd_279763 < baseStart_279763 := by decide
  rcases family_descends (prefixWord ++ tailWord_279763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279780 : List Nat := [2, 3, 1, 1, 1, 2, 2, 5, 6]
def baseStart_279780 : Nat := 118140960795 + 279780 * 2 ^ 59
def prefixEnd_279780 : Nat := 4983230072969 + 3 ^ 40 * 279780 * 2
def baseEnd_279780 : Nat := 15962401946113399240369

theorem tailTrace_279780 : CollatzResearch.WordTrace tailWord_279780 prefixEnd_279780 15962401946113399240369 := by
  unfold tailWord_279780
  simp only [CollatzResearch.WordTrace]
  refine ⟨5102207463206158732470397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6802943284274878309960529 5102207463206158732470397)
  ·
    refine ⟨1913327798702309524676399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5102207463206158732470397 1913327798702309524676399)
    ·
      refine ⟨2869991698053464287014599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1913327798702309524676399 2869991698053464287014599)
      ·
        refine ⟨4304987547080196430521899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2869991698053464287014599 4304987547080196430521899)
        ·
          refine ⟨6457481320620294645782849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4304987547080196430521899 6457481320620294645782849)
          ·
            refine ⟨4843110990465220984337137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6457481320620294645782849 4843110990465220984337137)
            ·
              refine ⟨3632333242848915738252853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4843110990465220984337137 3632333242848915738252853)
              ·
                refine ⟨340531241517085850461205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3632333242848915738252853 340531241517085850461205)
                ·
                  refine ⟨15962401946113399240369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 340531241517085850461205 15962401946113399240369)
                  ·
                    rfl

theorem cell23_279780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 6].length) (baseStart_279780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279780 prefixEnd_279780 := by exact prefixLift 279780
  have htrace : WordTrace (prefixWord ++ tailWord_279780) baseStart_279780 baseEnd_279780 := by
    simpa [prefixWord, tailWord_279780, baseEnd_279780] using wordTrace_append hprefix tailTrace_279780
  have hstable : (prefixWord ++ tailWord_279780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279780).length < 2 ^ (prefixWord ++ tailWord_279780).sum := by decide
  have hdescent : baseEnd_279780 < baseStart_279780 := by decide
  rcases family_descends (prefixWord ++ tailWord_279780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279857 : List Nat := [1, 2, 2, 3, 3, 2, 1, 2, 1, 6]
def baseStart_279857 : Nat := 118140960795 + 279857 * 2 ^ 59
def prefixEnd_279857 : Nat := 4983230072969 + 3 ^ 40 * 279857 * 2
def baseEnd_279857 : Nat := 47900385175138930633489

theorem tailTrace_279857 : CollatzResearch.WordTrace tailWord_279857 prefixEnd_279857 47900385175138930633489 := by
  unfold tailWord_279857
  simp only [CollatzResearch.WordTrace]
  refine ⟨10207223347133359615493825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6804815564755573076995883 10207223347133359615493825)
  ·
    refine ⟨7655417510350019711620369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10207223347133359615493825 7655417510350019711620369)
    ·
      refine ⟨5741563132762514783715277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7655417510350019711620369 5741563132762514783715277)
      ·
        refine ⟨2153086174785943043893229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5741563132762514783715277 2153086174785943043893229)
        ·
          refine ⟨807407315544728641459961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2153086174785943043893229 807407315544728641459961)
          ·
            refine ⟨605555486658546481094971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 807407315544728641459961 605555486658546481094971)
            ·
              refine ⟨908333229987819721642457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 605555486658546481094971 908333229987819721642457)
              ·
                refine ⟨681249922490864791231843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 908333229987819721642457 681249922490864791231843)
                ·
                  refine ⟨1021874883736297186847765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 681249922490864791231843 1021874883736297186847765)
                  ·
                    refine ⟨47900385175138930633489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1021874883736297186847765 47900385175138930633489)
                    ·
                      rfl

theorem cell23_279857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 6].length) (baseStart_279857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279857 prefixEnd_279857 := by exact prefixLift 279857
  have htrace : WordTrace (prefixWord ++ tailWord_279857) baseStart_279857 baseEnd_279857 := by
    simpa [prefixWord, tailWord_279857, baseEnd_279857] using wordTrace_append hprefix tailTrace_279857
  have hstable : (prefixWord ++ tailWord_279857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279857).length < 2 ^ (prefixWord ++ tailWord_279857).sum := by decide
  have hdescent : baseEnd_279857 < baseStart_279857 := by decide
  rcases family_descends (prefixWord ++ tailWord_279857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279897 : List Nat := [1, 2, 1, 2, 2, 2, 3, 3, 1, 3, 3]
def baseStart_279897 : Nat := 118140960795 + 279897 * 2 ^ 59
def prefixEnd_279897 : Nat := 4983230072969 + 3 ^ 40 * 279897 * 2
def baseEnd_279897 : Nat := 143721694751596635400283

theorem tailTrace_279897 : CollatzResearch.WordTrace tailWord_279897 prefixEnd_279897 143721694751596635400283 := by
  unfold tailWord_279897
  simp only [CollatzResearch.WordTrace]
  refine ⟨10208682266988446446949945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6805788177992297631299963 10208682266988446446949945)
  ·
    refine ⟨7656511700241334835212459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10208682266988446446949945 7656511700241334835212459)
    ·
      refine ⟨11484767550362002252818689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7656511700241334835212459 11484767550362002252818689)
      ·
        refine ⟨8613575662771501689614017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11484767550362002252818689 8613575662771501689614017)
        ·
          refine ⟨6460181747078626267210513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8613575662771501689614017 6460181747078626267210513)
          ·
            refine ⟨4845136310308969700407885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6460181747078626267210513 4845136310308969700407885)
            ·
              refine ⟨1816926116365863637652957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4845136310308969700407885 1816926116365863637652957)
              ·
                refine ⟨681347293637198864119859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1816926116365863637652957 681347293637198864119859)
                ·
                  refine ⟨1022020940455798296179789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 681347293637198864119859 1022020940455798296179789)
                  ·
                    refine ⟨383257852670924361067421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1022020940455798296179789 383257852670924361067421)
                    ·
                      refine ⟨143721694751596635400283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 383257852670924361067421 143721694751596635400283)
                      ·
                        rfl

theorem cell23_279897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 3, 3].length) (baseStart_279897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279897 prefixEnd_279897 := by exact prefixLift 279897
  have htrace : WordTrace (prefixWord ++ tailWord_279897) baseStart_279897 baseEnd_279897 := by
    simpa [prefixWord, tailWord_279897, baseEnd_279897] using wordTrace_append hprefix tailTrace_279897
  have hstable : (prefixWord ++ tailWord_279897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279897).length < 2 ^ (prefixWord ++ tailWord_279897).sum := by decide
  have hdescent : baseEnd_279897 < baseStart_279897 := by decide
  rcases family_descends (prefixWord ++ tailWord_279897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279918 : List Nat := [4, 1, 2, 4, 1, 1, 1, 3, 1, 2, 3]
def baseStart_279918 : Nat := 118140960795 + 279918 * 2 ^ 59
def prefixEnd_279918 : Nat := 4983230072969 + 3 ^ 40 * 279918 * 2
def baseEnd_279918 : Nat := 143732477845341053237687

theorem tailTrace_279918 : CollatzResearch.WordTrace tailWord_279918 prefixEnd_279918 143732477845341053237687 := by
  unfold tailWord_279918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1276181024989045879183051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6806298799941578022309605 1276181024989045879183051)
  ·
    refine ⟨1914271537483568818774577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1276181024989045879183051 1914271537483568818774577)
    ·
      refine ⟨1435703653112676614080933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1914271537483568818774577 1435703653112676614080933)
      ·
        refine ⟨269194434958626865140175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1435703653112676614080933 269194434958626865140175)
        ·
          refine ⟨403791652437940297710263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269194434958626865140175 403791652437940297710263)
          ·
            refine ⟨605687478656910446565395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403791652437940297710263 605687478656910446565395)
            ·
              refine ⟨908531217985365669848093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 605687478656910446565395 908531217985365669848093)
              ·
                refine ⟨340699206744512126193035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 908531217985365669848093 340699206744512126193035)
                ·
                  refine ⟨511048810116768189289553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 340699206744512126193035 511048810116768189289553)
                  ·
                    refine ⟨383286607587576141967165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 511048810116768189289553 383286607587576141967165)
                    ·
                      refine ⟨143732477845341053237687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 383286607587576141967165 143732477845341053237687)
                      ·
                        rfl

theorem cell23_279918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_279918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279918 prefixEnd_279918 := by exact prefixLift 279918
  have htrace : WordTrace (prefixWord ++ tailWord_279918) baseStart_279918 baseEnd_279918 := by
    simpa [prefixWord, tailWord_279918, baseEnd_279918] using wordTrace_append hprefix tailTrace_279918
  have hstable : (prefixWord ++ tailWord_279918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279918).length < 2 ^ (prefixWord ++ tailWord_279918).sum := by decide
  have hdescent : baseEnd_279918 < baseStart_279918 := by decide
  rcases family_descends (prefixWord ++ tailWord_279918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279930 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 3, 8]
def baseStart_279930 : Nat := 118140960795 + 279930 * 2 ^ 59
def prefixEnd_279930 : Nat := 4983230072969 + 3 ^ 40 * 279930 * 2
def baseEnd_279930 : Nat := 47912879871065002095877

theorem tailTrace_279930 : CollatzResearch.WordTrace tailWord_279930 prefixEnd_279930 47912879871065002095877 := by
  unfold tailWord_279930
  simp only [CollatzResearch.WordTrace]
  refine ⟨2552471468967223270725311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6806590583912595388600829 2552471468967223270725311)
  ·
    refine ⟨3828707203450834906087967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2552471468967223270725311 3828707203450834906087967)
    ·
      refine ⟨5743060805176252359131951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3828707203450834906087967 5743060805176252359131951)
      ·
        refine ⟨8614591207764378538697927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5743060805176252359131951 8614591207764378538697927)
        ·
          refine ⟨12921886811646567808046891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8614591207764378538697927 12921886811646567808046891)
          ·
            refine ⟨19382830217469851712070337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12921886811646567808046891 19382830217469851712070337)
            ·
              refine ⟨14537122663102388784052753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19382830217469851712070337 14537122663102388784052753)
              ·
                refine ⟨10902841997326791588039565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14537122663102388784052753 10902841997326791588039565)
                ·
                  refine ⟨4088565748997546845514837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10902841997326791588039565 4088565748997546845514837)
                  ·
                    refine ⟨47912879871065002095877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4088565748997546845514837 47912879871065002095877)
                    ·
                      rfl

theorem cell23_279930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 3, 8].length) (baseStart_279930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279930 prefixEnd_279930 := by exact prefixLift 279930
  have htrace : WordTrace (prefixWord ++ tailWord_279930) baseStart_279930 baseEnd_279930 := by
    simpa [prefixWord, tailWord_279930, baseEnd_279930] using wordTrace_append hprefix tailTrace_279930
  have hstable : (prefixWord ++ tailWord_279930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279930).length < 2 ^ (prefixWord ++ tailWord_279930).sum := by decide
  have hdescent : baseEnd_279930 < baseStart_279930 := by decide
  rcases family_descends (prefixWord ++ tailWord_279930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279957 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 2, 4, 3]
def baseStart_279957 : Nat := 118140960795 + 279957 * 2 ^ 59
def prefixEnd_279957 : Nat := 4983230072969 + 3 ^ 40 * 279957 * 2
def baseEnd_279957 : Nat := 143752503590866400650007

theorem tailTrace_279957 : CollatzResearch.WordTrace tailWord_279957 prefixEnd_279957 143752503590866400650007 := by
  unfold tailWord_279957
  simp only [CollatzResearch.WordTrace]
  refine ⟨10210870646771076694134125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6807247097847384462756083 10210870646771076694134125)
  ·
    refine ⟨3829076492539153760300297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10210870646771076694134125 3829076492539153760300297)
    ·
      refine ⟨2871807369404365320225223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3829076492539153760300297 2871807369404365320225223)
      ·
        refine ⟨4307711054106547980337835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2871807369404365320225223 4307711054106547980337835)
        ·
          refine ⟨6461566581159821970506753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4307711054106547980337835 6461566581159821970506753)
          ·
            refine ⟨4846174935869866477880065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6461566581159821970506753 4846174935869866477880065)
            ·
              refine ⟨3634631201902399858410049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4846174935869866477880065 3634631201902399858410049)
              ·
                refine ⟨2725973401426799893807537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3634631201902399858410049 2725973401426799893807537)
                ·
                  refine ⟨2044480051070099920355653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2725973401426799893807537 2044480051070099920355653)
                  ·
                    refine ⟨383340009575643735066685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2044480051070099920355653 383340009575643735066685)
                    ·
                      refine ⟨143752503590866400650007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 383340009575643735066685 143752503590866400650007)
                      ·
                        rfl

theorem cell23_279957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_279957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279957 prefixEnd_279957 := by exact prefixLift 279957
  have htrace : WordTrace (prefixWord ++ tailWord_279957) baseStart_279957 baseEnd_279957 := by
    simpa [prefixWord, tailWord_279957, baseEnd_279957] using wordTrace_append hprefix tailTrace_279957
  have hstable : (prefixWord ++ tailWord_279957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279957).length < 2 ^ (prefixWord ++ tailWord_279957).sum := by decide
  have hdescent : baseEnd_279957 < baseStart_279957 := by decide
  rcases family_descends (prefixWord ++ tailWord_279957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_279987 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 4, 3, 3]
def baseStart_279987 : Nat := 118140960795 + 279987 * 2 ^ 59
def prefixEnd_279987 : Nat := 4983230072969 + 3 ^ 40 * 279987 * 2
def baseEnd_279987 : Nat := 143767908010501283274869

theorem tailTrace_279987 : CollatzResearch.WordTrace tailWord_279987 prefixEnd_279987 143767908010501283274869 := by
  unfold tailWord_279987
  simp only [CollatzResearch.WordTrace]
  refine ⟨10211964836662391817726215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6807976557774927878484143 10211964836662391817726215)
  ·
    refine ⟨15317947254993587726589323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10211964836662391817726215 15317947254993587726589323)
    ·
      refine ⟨22976920882490381589883985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15317947254993587726589323 22976920882490381589883985)
      ·
        refine ⟨17232690661867786192412989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22976920882490381589883985 17232690661867786192412989)
        ·
          refine ⟨6462258998200419822154871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17232690661867786192412989 6462258998200419822154871)
          ·
            refine ⟨9693388497300629733232307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6462258998200419822154871 9693388497300629733232307)
            ·
              refine ⟨14540082745950944599848461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9693388497300629733232307 14540082745950944599848461)
              ·
                refine ⟨5452531029731604224943173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14540082745950944599848461 5452531029731604224943173)
                ·
                  refine ⟨1022349568074675792176845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5452531029731604224943173 1022349568074675792176845)
                  ·
                    refine ⟨383381088028003422066317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1022349568074675792176845 383381088028003422066317)
                    ·
                      refine ⟨143767908010501283274869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 383381088028003422066317 143767908010501283274869)
                      ·
                        rfl

theorem cell23_279987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 3, 3].length) (baseStart_279987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_279987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_279987 prefixEnd_279987 := by exact prefixLift 279987
  have htrace : WordTrace (prefixWord ++ tailWord_279987) baseStart_279987 baseEnd_279987 := by
    simpa [prefixWord, tailWord_279987, baseEnd_279987] using wordTrace_append hprefix tailTrace_279987
  have hstable : (prefixWord ++ tailWord_279987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279987).length < 2 ^ (prefixWord ++ tailWord_279987).sum := by decide
  have hdescent : baseEnd_279987 < baseStart_279987 := by decide
  rcases family_descends (prefixWord ++ tailWord_279987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280007 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 4, 5]
def baseStart_280007 : Nat := 118140960795 + 280007 * 2 ^ 59
def prefixEnd_280007 : Nat := 4983230072969 + 3 ^ 40 * 280007 * 2
def baseEnd_280007 : Nat := 47926059207863735008259

theorem tailTrace_280007 : CollatzResearch.WordTrace tailWord_280007 prefixEnd_280007 47926059207863735008259 := by
  unfold tailWord_280007
  simp only [CollatzResearch.WordTrace]
  refine ⟨10212694296589935233454275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6808462864393290155636183 10212694296589935233454275)
  ·
    refine ⟨15319041444884902850181413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10212694296589935233454275 15319041444884902850181413)
    ·
      refine ⟨2872320270915919284409015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15319041444884902850181413 2872320270915919284409015)
      ·
        refine ⟨4308480406373878926613523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2872320270915919284409015 4308480406373878926613523)
        ·
          refine ⟨6462720609560818389920285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4308480406373878926613523 6462720609560818389920285)
          ·
            refine ⟨2423520228585306896220107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6462720609560818389920285 2423520228585306896220107)
            ·
              refine ⟨3635280342877960344330161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2423520228585306896220107 3635280342877960344330161)
              ·
                refine ⟨2726460257158470258247621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3635280342877960344330161 2726460257158470258247621)
                ·
                  refine ⟨511211298217213173421429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2726460257158470258247621 511211298217213173421429)
                  ·
                    refine ⟨47926059207863735008259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 511211298217213173421429 47926059207863735008259)
                    ·
                      rfl

theorem cell23_280007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_280007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280007 prefixEnd_280007 := by exact prefixLift 280007
  have htrace : WordTrace (prefixWord ++ tailWord_280007) baseStart_280007 baseEnd_280007 := by
    simpa [prefixWord, tailWord_280007, baseEnd_280007] using wordTrace_append hprefix tailTrace_280007
  have hstable : (prefixWord ++ tailWord_280007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280007).length < 2 ^ (prefixWord ++ tailWord_280007).sum := by decide
  have hdescent : baseEnd_280007 < baseStart_280007 := by decide
  rcases family_descends (prefixWord ++ tailWord_280007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280045 : List Nat := [1, 5, 1, 3, 2, 2, 2, 2, 5]
def baseStart_280045 : Nat := 118140960795 + 280045 * 2 ^ 59
def prefixEnd_280045 : Nat := 4983230072969 + 3 ^ 40 * 280045 * 2
def baseEnd_280045 : Nat := 15977521098718006261067

theorem tailTrace_280045 : CollatzResearch.WordTrace tailWord_280045 prefixEnd_280045 15977521098718006261067 := by
  unfold tailWord_280045
  simp only [CollatzResearch.WordTrace]
  refine ⟨10214080270452267723337589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6809386846968178482225059 10214080270452267723337589)
  ·
    refine ⟨957570025354900099062899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10214080270452267723337589 957570025354900099062899)
    ·
      refine ⟨1436355038032350148594349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 957570025354900099062899 1436355038032350148594349)
      ·
        refine ⟨538633139262131305722881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1436355038032350148594349 538633139262131305722881)
        ·
          refine ⟨403974854446598479292161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 538633139262131305722881 403974854446598479292161)
          ·
            refine ⟨302981140834948859469121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 403974854446598479292161 302981140834948859469121)
            ·
              refine ⟨227235855626211644601841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 302981140834948859469121 227235855626211644601841)
              ·
                refine ⟨170426891719658733451381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227235855626211644601841 170426891719658733451381)
                ·
                  refine ⟨15977521098718006261067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 170426891719658733451381 15977521098718006261067)
                  ·
                    rfl

theorem cell23_280045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_280045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280045 prefixEnd_280045 := by exact prefixLift 280045
  have htrace : WordTrace (prefixWord ++ tailWord_280045) baseStart_280045 baseEnd_280045 := by
    simpa [prefixWord, tailWord_280045, baseEnd_280045] using wordTrace_append hprefix tailTrace_280045
  have hstable : (prefixWord ++ tailWord_280045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280045).length < 2 ^ (prefixWord ++ tailWord_280045).sum := by decide
  have hdescent : baseEnd_280045 < baseStart_280045 := by decide
  rcases family_descends (prefixWord ++ tailWord_280045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280057 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 2, 4, 4]
def baseStart_280057 : Nat := 118140960795 + 280057 * 2 ^ 59
def prefixEnd_280057 : Nat := 4983230072969 + 3 ^ 40 * 280057 * 2
def baseEnd_280057 : Nat := 143803851656316009399547

theorem tailTrace_280057 : CollatzResearch.WordTrace tailWord_280057 prefixEnd_280057 143803851656316009399547 := by
  unfold tailWord_280057
  simp only [CollatzResearch.WordTrace]
  refine ⟨10214517946408793772774425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6809678630939195848516283 10214517946408793772774425)
  ·
    refine ⟨7660888459806595329580819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10214517946408793772774425 7660888459806595329580819)
    ·
      refine ⟨11491332689709892994371229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7660888459806595329580819 11491332689709892994371229)
      ·
        refine ⟨4309249758641209872889211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11491332689709892994371229 4309249758641209872889211)
        ·
          refine ⟨6463874637961814809333817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4309249758641209872889211 6463874637961814809333817)
          ·
            refine ⟨4847905978471361107000363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6463874637961814809333817 4847905978471361107000363)
            ·
              refine ⟨7271858967707041660500545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4847905978471361107000363 7271858967707041660500545)
              ·
                refine ⟨5453894225780281245375409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7271858967707041660500545 5453894225780281245375409)
                ·
                  refine ⟨4090420669335210934031557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5453894225780281245375409 4090420669335210934031557)
                  ·
                    refine ⟨766953875500352050130917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4090420669335210934031557 766953875500352050130917)
                    ·
                      refine ⟨143803851656316009399547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 766953875500352050130917 143803851656316009399547)
                      ·
                        rfl

theorem cell23_280057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_280057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280057 prefixEnd_280057 := by exact prefixLift 280057
  have htrace : WordTrace (prefixWord ++ tailWord_280057) baseStart_280057 baseEnd_280057 := by
    simpa [prefixWord, tailWord_280057, baseEnd_280057] using wordTrace_append hprefix tailTrace_280057
  have hstable : (prefixWord ++ tailWord_280057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280057).length < 2 ^ (prefixWord ++ tailWord_280057).sum := by decide
  have hdescent : baseEnd_280057 < baseStart_280057 := by decide
  rcases family_descends (prefixWord ++ tailWord_280057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280061 : List Nat := [1, 4, 1, 1, 1, 5, 1, 1, 2, 4, 2]
def baseStart_280061 : Nat := 118140960795 + 280061 * 2 ^ 59
def prefixEnd_280061 : Nat := 4983230072969 + 3 ^ 40 * 280061 * 2
def baseEnd_280061 : Nat := 143805905578933993749529

theorem tailTrace_280061 : CollatzResearch.WordTrace tailWord_280061 prefixEnd_280061 143805905578933993749529 := by
  unfold tailWord_280061
  simp only [CollatzResearch.WordTrace]
  refine ⟨10214663838394302455920037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6809775892262868303946691 10214663838394302455920037)
  ·
    refine ⟨1915249469698931710485007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10214663838394302455920037 1915249469698931710485007)
    ·
      refine ⟨2872874204548397565727511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1915249469698931710485007 2872874204548397565727511)
      ·
        refine ⟨4309311306822596348591267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2872874204548397565727511 4309311306822596348591267)
        ·
          refine ⟨6463966960233894522886901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4309311306822596348591267 6463966960233894522886901)
          ·
            refine ⟨605996902521927611520647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6463966960233894522886901 605996902521927611520647)
            ·
              refine ⟨908995353782891417280971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 605996902521927611520647 908995353782891417280971)
              ·
                refine ⟨1363493030674337125921457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 908995353782891417280971 1363493030674337125921457)
                ·
                  refine ⟨1022619773005752844441093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1363493030674337125921457 1022619773005752844441093)
                  ·
                    refine ⟨191741207438578658332705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1022619773005752844441093 191741207438578658332705)
                    ·
                      refine ⟨143805905578933993749529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 191741207438578658332705 143805905578933993749529)
                      ·
                        rfl

theorem cell23_280061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 4, 2].length) (baseStart_280061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280061 prefixEnd_280061 := by exact prefixLift 280061
  have htrace : WordTrace (prefixWord ++ tailWord_280061) baseStart_280061 baseEnd_280061 := by
    simpa [prefixWord, tailWord_280061, baseEnd_280061] using wordTrace_append hprefix tailTrace_280061
  have hstable : (prefixWord ++ tailWord_280061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280061).length < 2 ^ (prefixWord ++ tailWord_280061).sum := by decide
  have hdescent : baseEnd_280061 < baseStart_280061 := by decide
  rcases family_descends (prefixWord ++ tailWord_280061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280071 : List Nat := [1, 1, 4, 3, 2, 2, 1, 2, 3, 4]
def baseStart_280071 : Nat := 118140960795 + 280071 * 2 ^ 59
def prefixEnd_280071 : Nat := 4983230072969 + 3 ^ 40 * 280071 * 2
def baseEnd_280071 : Nat := 47937013461826318208161

theorem tailTrace_280071 : CollatzResearch.WordTrace tailWord_280071 prefixEnd_280071 47937013461826318208161 := by
  unfold tailWord_280071
  simp only [CollatzResearch.WordTrace]
  refine ⟨10215028568358074163784067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6810019045572049442522711 10215028568358074163784067)
  ·
    refine ⟨15322542852537111245676101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10215028568358074163784067 15322542852537111245676101)
    ·
      refine ⟨2872976784850708358564269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15322542852537111245676101 2872976784850708358564269)
      ·
        refine ⟨1077366294319015634461601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2872976784850708358564269 1077366294319015634461601)
        ·
          refine ⟨808024720739261725846201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1077366294319015634461601 808024720739261725846201)
          ·
            refine ⟨606018540554446294384651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 808024720739261725846201 606018540554446294384651)
            ·
              refine ⟨909027810831669441576977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606018540554446294384651 909027810831669441576977)
              ·
                refine ⟨681770858123752081182733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 909027810831669441576977 681770858123752081182733)
                ·
                  refine ⟨255664071796407030443525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 681770858123752081182733 255664071796407030443525)
                  ·
                    refine ⟨47937013461826318208161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 255664071796407030443525 47937013461826318208161)
                    ·
                      rfl

theorem cell23_280071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_280071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280071 prefixEnd_280071 := by exact prefixLift 280071
  have htrace : WordTrace (prefixWord ++ tailWord_280071) baseStart_280071 baseEnd_280071 := by
    simpa [prefixWord, tailWord_280071, baseEnd_280071] using wordTrace_append hprefix tailTrace_280071
  have hstable : (prefixWord ++ tailWord_280071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280071).length < 2 ^ (prefixWord ++ tailWord_280071).sum := by decide
  have hdescent : baseEnd_280071 < baseStart_280071 := by decide
  rcases family_descends (prefixWord ++ tailWord_280071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280078 : List Nat := [4, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4]
def baseStart_280078 : Nat := 118140960795 + 280078 * 2 ^ 59
def prefixEnd_280078 : Nat := 4983230072969 + 3 ^ 40 * 280078 * 2
def baseEnd_280078 : Nat := 143814634750060427236951

theorem tailTrace_280078 : CollatzResearch.WordTrace tailWord_280078 prefixEnd_280078 143814634750060427236951 := by
  unfold tailWord_280078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1276910484916589294911111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6810189252888476239525925 1276910484916589294911111)
  ·
    refine ⟨1915365727374883942366667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1276910484916589294911111 1915365727374883942366667)
    ·
      refine ⟨2873048591062325913550001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1915365727374883942366667 2873048591062325913550001)
      ·
        refine ⟨2154786443296744435162501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2873048591062325913550001 2154786443296744435162501)
        ·
          refine ⟨404022458118139581592969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2154786443296744435162501 404022458118139581592969)
          ·
            refine ⟨303016843588604686194727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 404022458118139581592969 303016843588604686194727)
            ·
              refine ⟨454525265382907029292091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303016843588604686194727 454525265382907029292091)
              ·
                refine ⟨681787898074360543938137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 454525265382907029292091 681787898074360543938137)
                ·
                  refine ⟨511340923555770407953603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 681787898074360543938137 511340923555770407953603)
                  ·
                    refine ⟨767011385333655611930405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 511340923555770407953603 767011385333655611930405)
                    ·
                      refine ⟨143814634750060427236951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 767011385333655611930405 143814634750060427236951)
                      ·
                        rfl

theorem cell23_280078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_280078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280078 prefixEnd_280078 := by exact prefixLift 280078
  have htrace : WordTrace (prefixWord ++ tailWord_280078) baseStart_280078 baseEnd_280078 := by
    simpa [prefixWord, tailWord_280078, baseEnd_280078] using wordTrace_append hprefix tailTrace_280078
  have hstable : (prefixWord ++ tailWord_280078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280078).length < 2 ^ (prefixWord ++ tailWord_280078).sum := by decide
  have hdescent : baseEnd_280078 < baseStart_280078 := by decide
  rcases family_descends (prefixWord ++ tailWord_280078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280121 : List Nat := [1, 2, 1, 5, 1, 2, 1, 2, 1, 5, 2]
def baseStart_280121 : Nat := 118140960795 + 280121 * 2 ^ 59
def prefixEnd_280121 : Nat := 4983230072969 + 3 ^ 40 * 280121 * 2
def baseEnd_280121 : Nat := 143836714418203758999253

theorem tailTrace_280121 : CollatzResearch.WordTrace tailWord_280121 prefixEnd_280121 143836714418203758999253 := by
  unfold tailWord_280121
  simp only [CollatzResearch.WordTrace]
  refine ⟨10216852218176932703104217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6811234812117955135402811 10216852218176932703104217)
  ·
    refine ⟨7662639163632699527328163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10216852218176932703104217 7662639163632699527328163)
    ·
      refine ⟨11493958745449049290992245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7662639163632699527328163 11493958745449049290992245)
      ·
        refine ⟨1077558632385848371030523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11493958745449049290992245 1077558632385848371030523)
        ·
          refine ⟨1616337948578772556545785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1077558632385848371030523 1616337948578772556545785)
          ·
            refine ⟨1212253461434079417409339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1616337948578772556545785 1212253461434079417409339)
            ·
              refine ⟨1818380192151119126114009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1212253461434079417409339 1818380192151119126114009)
              ·
                refine ⟨1363785144113339344585507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1818380192151119126114009 1363785144113339344585507)
                ·
                  refine ⟨2045677716170009016878261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1363785144113339344585507 2045677716170009016878261)
                  ·
                    refine ⟨191782285890938345332337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2045677716170009016878261 191782285890938345332337)
                    ·
                      refine ⟨143836714418203758999253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 191782285890938345332337 143836714418203758999253)
                      ·
                        rfl

theorem cell23_280121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_280121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280121 prefixEnd_280121 := by exact prefixLift 280121
  have htrace : WordTrace (prefixWord ++ tailWord_280121) baseStart_280121 baseEnd_280121 := by
    simpa [prefixWord, tailWord_280121, baseEnd_280121] using wordTrace_append hprefix tailTrace_280121
  have hstable : (prefixWord ++ tailWord_280121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280121).length < 2 ^ (prefixWord ++ tailWord_280121).sum := by decide
  have hdescent : baseEnd_280121 < baseStart_280121 := by decide
  rcases family_descends (prefixWord ++ tailWord_280121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280144 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 6, 4]
def baseStart_280144 : Nat := 118140960795 + 280144 * 2 ^ 59
def prefixEnd_280144 : Nat := 4983230072969 + 3 ^ 40 * 280144 * 2
def baseEnd_280144 : Nat := 47949508157752389670549

theorem tailTrace_280144 : CollatzResearch.WordTrace tailWord_280144 prefixEnd_280144 47949508157752389670549 := by
  unfold tailWord_280144
  simp only [CollatzResearch.WordTrace]
  refine ⟨5108845548546803815595743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6811794064729071754127657 5108845548546803815595743)
  ·
    refine ⟨7663268322820205723393615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5108845548546803815595743 7663268322820205723393615)
    ·
      refine ⟨11494902484230308585090423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7663268322820205723393615 11494902484230308585090423)
      ·
        refine ⟨17242353726345462877635635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11494902484230308585090423 17242353726345462877635635)
        ·
          refine ⟨25863530589518194316453453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17242353726345462877635635 25863530589518194316453453)
          ·
            refine ⟨9698823971069322868670045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25863530589518194316453453 9698823971069322868670045)
            ·
              refine ⟨3637058989150996075751267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9698823971069322868670045 3637058989150996075751267)
              ·
                refine ⟨5455588483726494113626901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3637058989150996075751267 5455588483726494113626901)
                ·
                  refine ⟨255730710174679411576261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5455588483726494113626901 255730710174679411576261)
                  ·
                    refine ⟨47949508157752389670549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 255730710174679411576261 47949508157752389670549)
                    ·
                      rfl

theorem cell23_280144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 6, 4].length) (baseStart_280144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280144 prefixEnd_280144 := by exact prefixLift 280144
  have htrace : WordTrace (prefixWord ++ tailWord_280144) baseStart_280144 baseEnd_280144 := by
    simpa [prefixWord, tailWord_280144, baseEnd_280144] using wordTrace_append hprefix tailTrace_280144
  have hstable : (prefixWord ++ tailWord_280144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280144).length < 2 ^ (prefixWord ++ tailWord_280144).sum := by decide
  have hdescent : baseEnd_280144 < baseStart_280144 := by decide
  rcases family_descends (prefixWord ++ tailWord_280144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280147 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 6]
def baseStart_280147 : Nat := 118140960795 + 280147 * 2 ^ 59
def prefixEnd_280147 : Nat := 4983230072969 + 3 ^ 40 * 280147 * 2
def baseEnd_280147 : Nat := 143850064915220657274133

theorem tailTrace_280147 : CollatzResearch.WordTrace tailWord_280147 prefixEnd_280147 143850064915220657274133 := by
  unfold tailWord_280147
  simp only [CollatzResearch.WordTrace]
  refine ⟨10217800516082739143550695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6811867010721826095700463 10217800516082739143550695)
  ·
    refine ⟨15326700774124108715326043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10217800516082739143550695 15326700774124108715326043)
    ·
      refine ⟨22990051161186163072989065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15326700774124108715326043 22990051161186163072989065)
      ·
        refine ⟨17242538370889622304741799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22990051161186163072989065 17242538370889622304741799)
        ·
          refine ⟨25863807556334433457112699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17242538370889622304741799 25863807556334433457112699)
          ·
            refine ⟨38795711334501650185669049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25863807556334433457112699 38795711334501650185669049)
            ·
              refine ⟨29096783500876237639251787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38795711334501650185669049 29096783500876237639251787)
              ·
                refine ⟨43645175251314356458877681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29096783500876237639251787 43645175251314356458877681)
                ·
                  refine ⟨32733881438485767344158261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43645175251314356458877681 32733881438485767344158261)
                  ·
                    refine ⟨3068801384858040688514837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32733881438485767344158261 3068801384858040688514837)
                    ·
                      refine ⟨143850064915220657274133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3068801384858040688514837 143850064915220657274133)
                      ·
                        rfl

theorem cell23_280147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 6].length) (baseStart_280147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280147 prefixEnd_280147 := by exact prefixLift 280147
  have htrace : WordTrace (prefixWord ++ tailWord_280147) baseStart_280147 baseEnd_280147 := by
    simpa [prefixWord, tailWord_280147, baseEnd_280147] using wordTrace_append hprefix tailTrace_280147
  have hstable : (prefixWord ++ tailWord_280147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280147).length < 2 ^ (prefixWord ++ tailWord_280147).sum := by decide
  have hdescent : baseEnd_280147 < baseStart_280147 := by decide
  rcases family_descends (prefixWord ++ tailWord_280147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280151 : List Nat := [1, 1, 3, 2, 2, 3, 2, 3, 1, 1, 4]
def baseStart_280151 : Nat := 118140960795 + 280151 * 2 ^ 59
def prefixEnd_280151 : Nat := 4983230072969 + 3 ^ 40 * 280151 * 2
def baseEnd_280151 : Nat := 143852118837838641624115

theorem tailTrace_280151 : CollatzResearch.WordTrace tailWord_280151 prefixEnd_280151 143852118837838641624115 := by
  unfold tailWord_280151
  simp only [CollatzResearch.WordTrace]
  refine ⟨10217946408068247826696307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6811964272045498551130871 10217946408068247826696307)
  ·
    refine ⟨15326919612102371740044461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10217946408068247826696307 15326919612102371740044461)
    ·
      refine ⟨5747594854538389402516673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15326919612102371740044461 5747594854538389402516673)
      ·
        refine ⟨4310696140903792051887505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5747594854538389402516673 4310696140903792051887505)
        ·
          refine ⟨3233022105677844038915629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4310696140903792051887505 3233022105677844038915629)
          ·
            refine ⟨1212383289629191514593361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3233022105677844038915629 1212383289629191514593361)
            ·
              refine ⟨909287467221893635945021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1212383289629191514593361 909287467221893635945021)
              ·
                refine ⟨340982800208210113479383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 909287467221893635945021 340982800208210113479383)
                ·
                  refine ⟨511474200312315170219075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 340982800208210113479383 511474200312315170219075)
                  ·
                    refine ⟨767211300468472755328613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 511474200312315170219075 767211300468472755328613)
                    ·
                      refine ⟨143852118837838641624115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 767211300468472755328613 143852118837838641624115)
                      ·
                        rfl

theorem cell23_280151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_280151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280151 prefixEnd_280151 := by exact prefixLift 280151
  have htrace : WordTrace (prefixWord ++ tailWord_280151) baseStart_280151 baseEnd_280151 := by
    simpa [prefixWord, tailWord_280151, baseEnd_280151] using wordTrace_append hprefix tailTrace_280151
  have hstable : (prefixWord ++ tailWord_280151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280151).length < 2 ^ (prefixWord ++ tailWord_280151).sum := by decide
  have hdescent : baseEnd_280151 < baseStart_280151 := by decide
  rcases family_descends (prefixWord ++ tailWord_280151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280161 : List Nat := [1, 2, 3, 1, 1, 3, 2, 4, 2, 4]
def baseStart_280161 : Nat := 118140960795 + 280161 * 2 ^ 59
def prefixEnd_280161 : Nat := 4983230072969 + 3 ^ 40 * 280161 * 2
def baseEnd_280161 : Nat := 47952417881461200833023

theorem tailTrace_280161 : CollatzResearch.WordTrace tailWord_280161 prefixEnd_280161 47952417881461200833023 := by
  unfold tailWord_280161
  simp only [CollatzResearch.WordTrace]
  refine ⟨10218311138032019534560337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6812207425354679689706891 10218311138032019534560337)
  ·
    refine ⟨7663733353524014650920253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10218311138032019534560337 7663733353524014650920253)
    ·
      refine ⟨2873900007571505494095095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7663733353524014650920253 2873900007571505494095095)
      ·
        refine ⟨4310850011357258241142643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2873900007571505494095095 4310850011357258241142643)
        ·
          refine ⟨6466275017035887361713965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4310850011357258241142643 6466275017035887361713965)
          ·
            refine ⟨2424853131388457760642737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6466275017035887361713965 2424853131388457760642737)
            ·
              refine ⟨1818639848541343320482053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2424853131388457760642737 1818639848541343320482053)
              ·
                refine ⟨340994971601501872590385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1818639848541343320482053 340994971601501872590385)
                ·
                  refine ⟨255746228701126404442789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 340994971601501872590385 255746228701126404442789)
                  ·
                    refine ⟨47952417881461200833023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 255746228701126404442789 47952417881461200833023)
                    ·
                      rfl

theorem cell23_280161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_280161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280161 prefixEnd_280161 := by exact prefixLift 280161
  have htrace : WordTrace (prefixWord ++ tailWord_280161) baseStart_280161 baseEnd_280161 := by
    simpa [prefixWord, tailWord_280161, baseEnd_280161] using wordTrace_append hprefix tailTrace_280161
  have hstable : (prefixWord ++ tailWord_280161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280161).length < 2 ^ (prefixWord ++ tailWord_280161).sum := by decide
  have hdescent : baseEnd_280161 < baseStart_280161 := by decide
  rcases family_descends (prefixWord ++ tailWord_280161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280164 : List Nat := [2, 3, 1, 1, 2, 3, 1, 2, 1, 1, 6]
def baseStart_280164 : Nat := 118140960795 + 280164 * 2 ^ 59
def prefixEnd_280164 : Nat := 4983230072969 + 3 ^ 40 * 280164 * 2
def baseEnd_280164 : Nat := 143858794086347090761555

theorem tailTrace_280164 : CollatzResearch.WordTrace tailWord_280164 prefixEnd_280164 143858794086347090761555 := by
  unfold tailWord_280164
  simp only [CollatzResearch.WordTrace]
  refine ⟨5109210278510575523459773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6812280371347434031279697 5109210278510575523459773)
  ·
    refine ⟨1915953854441465821297415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5109210278510575523459773 1915953854441465821297415)
    ·
      refine ⟨2873930781662198731946123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1915953854441465821297415 2873930781662198731946123)
      ·
        refine ⟨4310896172493298097919185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2873930781662198731946123 4310896172493298097919185)
        ·
          refine ⟨3233172129369973573439389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4310896172493298097919185 3233172129369973573439389)
          ·
            refine ⟨1212439548513740090039771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3233172129369973573439389 1212439548513740090039771)
            ·
              refine ⟨1818659322770610135059657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1212439548513740090039771 1818659322770610135059657)
              ·
                refine ⟨1363994492077957601294743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1818659322770610135059657 1363994492077957601294743)
                ·
                  refine ⟨2045991738116936401942115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1363994492077957601294743 2045991738116936401942115)
                  ·
                    refine ⟨3068987607175404602913173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2045991738116936401942115 3068987607175404602913173)
                    ·
                      refine ⟨143858794086347090761555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3068987607175404602913173 143858794086347090761555)
                      ·
                        rfl

theorem cell23_280164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_280164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280164 prefixEnd_280164 := by exact prefixLift 280164
  have htrace : WordTrace (prefixWord ++ tailWord_280164) baseStart_280164 baseEnd_280164 := by
    simpa [prefixWord, tailWord_280164, baseEnd_280164] using wordTrace_append hprefix tailTrace_280164
  have hstable : (prefixWord ++ tailWord_280164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280164).length < 2 ^ (prefixWord ++ tailWord_280164).sum := by decide
  have hdescent : baseEnd_280164 < baseStart_280164 := by decide
  rcases family_descends (prefixWord ++ tailWord_280164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280178 : List Nat := [3, 2, 1, 2, 3, 2, 1, 3, 2, 4]
def baseStart_280178 : Nat := 118140960795 + 280178 * 2 ^ 59
def prefixEnd_280178 : Nat := 4983230072969 + 3 ^ 40 * 280178 * 2
def baseEnd_280178 : Nat := 47955327605170011995497

theorem tailTrace_280178 : CollatzResearch.WordTrace tailWord_280178 prefixEnd_280178 47955327605170011995497 := by
  unfold tailWord_280178
  simp only [CollatzResearch.WordTrace]
  refine ⟨2554732794742607859482297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6812620785980287625286125 2554732794742607859482297)
  ·
    refine ⟨1916049596056955894611723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2554732794742607859482297 1916049596056955894611723)
    ·
      refine ⟨2874074394085433841917585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1916049596056955894611723 2874074394085433841917585)
      ·
        refine ⟨2155555795564075381438189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2874074394085433841917585 2155555795564075381438189)
        ·
          refine ⟨808333423336528268039321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2155555795564075381438189 808333423336528268039321)
          ·
            refine ⟨606250067502396201029491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 808333423336528268039321 606250067502396201029491)
            ·
              refine ⟨909375101253594301544237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606250067502396201029491 909375101253594301544237)
              ·
                refine ⟨341015662970097863079089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 909375101253594301544237 341015662970097863079089)
                ·
                  refine ⟨255761747227573397309317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 341015662970097863079089 255761747227573397309317)
                  ·
                    refine ⟨47955327605170011995497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 255761747227573397309317 47955327605170011995497)
                    ·
                      rfl

theorem cell23_280178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_280178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280178 prefixEnd_280178 := by exact prefixLift 280178
  have htrace : WordTrace (prefixWord ++ tailWord_280178) baseStart_280178 baseEnd_280178 := by
    simpa [prefixWord, tailWord_280178, baseEnd_280178] using wordTrace_append hprefix tailTrace_280178
  have hstable : (prefixWord ++ tailWord_280178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280178).length < 2 ^ (prefixWord ++ tailWord_280178).sum := by decide
  have hdescent : baseEnd_280178 < baseStart_280178 := by decide
  rcases family_descends (prefixWord ++ tailWord_280178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280181 : List Nat := [1, 3, 4, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_280181 : Nat := 118140960795 + 280181 * 2 ^ 59
def prefixEnd_280181 : Nat := 4983230072969 + 3 ^ 40 * 280181 * 2
def baseEnd_280181 : Nat := 143867523257473524248977

theorem tailTrace_280181 : CollatzResearch.WordTrace tailWord_280181 prefixEnd_280181 143867523257473524248977 := by
  unfold tailWord_280181
  simp only [CollatzResearch.WordTrace]
  refine ⟨10219040597959562950288397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6812693731973041966858931 10219040597959562950288397)
  ·
    refine ⟨3832140224234836106358149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10219040597959562950288397 3832140224234836106358149)
    ·
      refine ⟨718526292044031769942153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3832140224234836106358149 718526292044031769942153)
      ·
        refine ⟨538894719033023827456615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 718526292044031769942153 538894719033023827456615)
        ·
          refine ⟨808342078549535741184923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 538894719033023827456615 808342078549535741184923)
          ·
            refine ⟨1212513117824303611777385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 808342078549535741184923 1212513117824303611777385)
            ·
              refine ⟨909384838368227708833039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1212513117824303611777385 909384838368227708833039)
              ·
                refine ⟨1364077257552341563249559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 909384838368227708833039 1364077257552341563249559)
                ·
                  refine ⟨2046115886328512344874339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1364077257552341563249559 2046115886328512344874339)
                  ·
                    refine ⟨3069173829492768517311509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2046115886328512344874339 3069173829492768517311509)
                    ·
                      refine ⟨143867523257473524248977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3069173829492768517311509 143867523257473524248977)
                      ·
                        rfl

theorem cell23_280181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_280181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280181 prefixEnd_280181 := by exact prefixLift 280181
  have htrace : WordTrace (prefixWord ++ tailWord_280181) baseStart_280181 baseEnd_280181 := by
    simpa [prefixWord, tailWord_280181, baseEnd_280181] using wordTrace_append hprefix tailTrace_280181
  have hstable : (prefixWord ++ tailWord_280181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280181).length < 2 ^ (prefixWord ++ tailWord_280181).sum := by decide
  have hdescent : baseEnd_280181 < baseStart_280181 := by decide
  rcases family_descends (prefixWord ++ tailWord_280181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280201 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 6, 1, 3]
def baseStart_280201 : Nat := 118140960795 + 280201 * 2 ^ 59
def prefixEnd_280201 : Nat := 4983230072969 + 3 ^ 40 * 280201 * 2
def baseEnd_280201 : Nat := 143877792870563445998885

theorem tailTrace_280201 : CollatzResearch.WordTrace tailWord_280201 prefixEnd_280201 143877792870563445998885 := by
  unfold tailWord_280201
  simp only [CollatzResearch.WordTrace]
  refine ⟨10219770057887106366016457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6813180038591404244010971 10219770057887106366016457)
  ·
    refine ⟨7664827543415329774512343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10219770057887106366016457 7664827543415329774512343)
    ·
      refine ⟨11497241315122994661768515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7664827543415329774512343 11497241315122994661768515)
      ·
        refine ⟨17245861972684491992652773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11497241315122994661768515 17245861972684491992652773)
        ·
          refine ⟨3233599119878342248622395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17245861972684491992652773 3233599119878342248622395)
          ·
            refine ⟨4850398679817513372933593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3233599119878342248622395 4850398679817513372933593)
            ·
              refine ⟨3637799009863135029700195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4850398679817513372933593 3637799009863135029700195)
              ·
                refine ⟨5456698514794702544550293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3637799009863135029700195 5456698514794702544550293)
                ·
                  refine ⟨255782742881001681775795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5456698514794702544550293 255782742881001681775795)
                  ·
                    refine ⟨383674114321502522663693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 255782742881001681775795 383674114321502522663693)
                    ·
                      refine ⟨143877792870563445998885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 383674114321502522663693 143877792870563445998885)
                      ·
                        rfl

theorem cell23_280201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 6, 1, 3].length) (baseStart_280201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280201 prefixEnd_280201 := by exact prefixLift 280201
  have htrace : WordTrace (prefixWord ++ tailWord_280201) baseStart_280201 baseEnd_280201 := by
    simpa [prefixWord, tailWord_280201, baseEnd_280201] using wordTrace_append hprefix tailTrace_280201
  have hstable : (prefixWord ++ tailWord_280201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280201).length < 2 ^ (prefixWord ++ tailWord_280201).sum := by decide
  have hdescent : baseEnd_280201 < baseStart_280201 := by decide
  rcases family_descends (prefixWord ++ tailWord_280201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280211 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 7, 3, 2]
def baseStart_280211 : Nat := 118140960795 + 280211 * 2 ^ 59
def prefixEnd_280211 : Nat := 4983230072969 + 3 ^ 40 * 280211 * 2
def baseEnd_280211 : Nat := 143882927677108406873839

theorem tailTrace_280211 : CollatzResearch.WordTrace tailWord_280211 prefixEnd_280211 143882927677108406873839 := by
  unfold tailWord_280211
  simp only [CollatzResearch.WordTrace]
  refine ⟨10220134787850878073880487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6813423191900585382586991 10220134787850878073880487)
  ·
    refine ⟨15330202181776317110820731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10220134787850878073880487 15330202181776317110820731)
    ·
      refine ⟨22995303272664475666231097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15330202181776317110820731 22995303272664475666231097)
      ·
        refine ⟨17246477454498356749673323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22995303272664475666231097 17246477454498356749673323)
        ·
          refine ⟨25869716181747535124509985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17246477454498356749673323 25869716181747535124509985)
          ·
            refine ⟨19402287136310651343382489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25869716181747535124509985 19402287136310651343382489)
            ·
              refine ⟨14551715352232988507536867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19402287136310651343382489 14551715352232988507536867)
              ·
                refine ⟨21827573028349482761305301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14551715352232988507536867 21827573028349482761305301)
                ·
                  refine ⟨511583742851941002218093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 21827573028349482761305301 511583742851941002218093)
                  ·
                    refine ⟨191843903569477875831785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 511583742851941002218093 191843903569477875831785)
                    ·
                      refine ⟨143882927677108406873839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 191843903569477875831785 143882927677108406873839)
                      ·
                        rfl

theorem cell23_280211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 3, 2].length) (baseStart_280211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280211 prefixEnd_280211 := by exact prefixLift 280211
  have htrace : WordTrace (prefixWord ++ tailWord_280211) baseStart_280211 baseEnd_280211 := by
    simpa [prefixWord, tailWord_280211, baseEnd_280211] using wordTrace_append hprefix tailTrace_280211
  have hstable : (prefixWord ++ tailWord_280211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280211).length < 2 ^ (prefixWord ++ tailWord_280211).sum := by decide
  have hdescent : baseEnd_280211 < baseStart_280211 := by decide
  rcases family_descends (prefixWord ++ tailWord_280211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280228 : List Nat := [2, 3, 1, 2, 2, 2, 1, 2, 3, 3, 2]
def baseStart_280228 : Nat := 118140960795 + 280228 * 2 ^ 59
def prefixEnd_280228 : Nat := 4983230072969 + 3 ^ 40 * 280228 * 2
def baseEnd_280228 : Nat := 143891656848234840361261

theorem tailTrace_280228 : CollatzResearch.WordTrace tailWord_280228 prefixEnd_280228 143891656848234840361261 := by
  unfold tailWord_280228
  simp only [CollatzResearch.WordTrace]
  refine ⟨5110377414394644988624669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6813836552526193318166225 5110377414394644988624669)
  ·
    refine ⟨1916391530397991870734251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5110377414394644988624669 1916391530397991870734251)
    ·
      refine ⟨2874587295596987806101377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1916391530397991870734251 2874587295596987806101377)
      ·
        refine ⟨2155940471697740854576033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2874587295596987806101377 2155940471697740854576033)
        ·
          refine ⟨1616955353773305640932025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2155940471697740854576033 1616955353773305640932025)
          ·
            refine ⟨1212716515329979230699019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1616955353773305640932025 1212716515329979230699019)
            ·
              refine ⟨1819074772994968846048529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1212716515329979230699019 1819074772994968846048529)
              ·
                refine ⟨1364306079746226634536397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1819074772994968846048529 1364306079746226634536397)
                ·
                  refine ⟨511614779904834987951149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1364306079746226634536397 511614779904834987951149)
                  ·
                    refine ⟨191855542464313120481681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 511614779904834987951149 191855542464313120481681)
                    ·
                      refine ⟨143891656848234840361261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 191855542464313120481681 143891656848234840361261)
                      ·
                        rfl

theorem cell23_280228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_280228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280228 prefixEnd_280228 := by exact prefixLift 280228
  have htrace : WordTrace (prefixWord ++ tailWord_280228) baseStart_280228 baseEnd_280228 := by
    simpa [prefixWord, tailWord_280228, baseEnd_280228] using wordTrace_append hprefix tailTrace_280228
  have hstable : (prefixWord ++ tailWord_280228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280228).length < 2 ^ (prefixWord ++ tailWord_280228).sum := by decide
  have hdescent : baseEnd_280228 < baseStart_280228 := by decide
  rcases family_descends (prefixWord ++ tailWord_280228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280232 : List Nat := [2, 1, 7, 1, 1, 1, 2, 1, 1, 2, 4]
def baseStart_280232 : Nat := 118140960795 + 280232 * 2 ^ 59
def prefixEnd_280232 : Nat := 4983230072969 + 3 ^ 40 * 280232 * 2
def baseEnd_280232 : Nat := 143893710770852824711243

theorem tailTrace_280232 : CollatzResearch.WordTrace tailWord_280232 prefixEnd_280232 143893710770852824711243 := by
  unfold tailWord_280232
  simp only [CollatzResearch.WordTrace]
  refine ⟨5110450360387399330197475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6813933813849865773596633 5110450360387399330197475)
  ·
    refine ⟨7665675540581098995296213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5110450360387399330197475 7665675540581098995296213)
    ·
      refine ⟨179664270482369507702255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 7665675540581098995296213 179664270482369507702255)
      ·
        refine ⟨269496405723554261553383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179664270482369507702255 269496405723554261553383)
        ·
          refine ⟨404244608585331392330075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269496405723554261553383 404244608585331392330075)
          ·
            refine ⟨606366912877997088495113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404244608585331392330075 606366912877997088495113)
            ·
              refine ⟨454775184658497816371335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 606366912877997088495113 454775184658497816371335)
              ·
                refine ⟨682162776987746724557003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 454775184658497816371335 682162776987746724557003)
                ·
                  refine ⟨1023244165481620086835505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 682162776987746724557003 1023244165481620086835505)
                  ·
                    refine ⟨767433124111215065126629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1023244165481620086835505 767433124111215065126629)
                    ·
                      refine ⟨143893710770852824711243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 767433124111215065126629 143893710770852824711243)
                      ·
                        rfl

theorem cell23_280232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_280232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280232 prefixEnd_280232 := by exact prefixLift 280232
  have htrace : WordTrace (prefixWord ++ tailWord_280232) baseStart_280232 baseEnd_280232 := by
    simpa [prefixWord, tailWord_280232, baseEnd_280232] using wordTrace_append hprefix tailTrace_280232
  have hstable : (prefixWord ++ tailWord_280232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280232).length < 2 ^ (prefixWord ++ tailWord_280232).sum := by decide
  have hdescent : baseEnd_280232 < baseStart_280232 := by decide
  rcases family_descends (prefixWord ++ tailWord_280232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280264 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 9]
def baseStart_280264 : Nat := 118140960795 + 280264 * 2 ^ 59
def prefixEnd_280264 : Nat := 4983230072969 + 3 ^ 40 * 280264 * 2
def baseEnd_280264 : Nat := 15990015794644077723455

theorem tailTrace_280264 : CollatzResearch.WordTrace tailWord_280264 prefixEnd_280264 15990015794644077723455 := by
  unfold tailWord_280264
  simp only [CollatzResearch.WordTrace]
  refine ⟨5111033928329434062779923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6814711904439245417039897 5111033928329434062779923)
  ·
    refine ⟨7666550892494151094169885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5111033928329434062779923 7666550892494151094169885)
    ·
      refine ⟨2874956584685306660313707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7666550892494151094169885 2874956584685306660313707)
      ·
        refine ⟨4312434877027959990470561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2874956584685306660313707 4312434877027959990470561)
        ·
          refine ⟨3234326157770969992852921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4312434877027959990470561 3234326157770969992852921)
          ·
            refine ⟨2425744618328227494639691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3234326157770969992852921 2425744618328227494639691)
            ·
              refine ⟨3638616927492341241959537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2425744618328227494639691 3638616927492341241959537)
              ·
                refine ⟨2728962695619255931469653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3638616927492341241959537 2728962695619255931469653)
                ·
                  refine ⟨15990015794644077723455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2728962695619255931469653 15990015794644077723455)
                  ·
                    rfl

theorem cell23_280264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 9].length) (baseStart_280264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280264 prefixEnd_280264 := by exact prefixLift 280264
  have htrace : WordTrace (prefixWord ++ tailWord_280264) baseStart_280264 baseEnd_280264 := by
    simpa [prefixWord, tailWord_280264, baseEnd_280264] using wordTrace_append hprefix tailTrace_280264
  have hstable : (prefixWord ++ tailWord_280264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280264).length < 2 ^ (prefixWord ++ tailWord_280264).sum := by decide
  have hdescent : baseEnd_280264 < baseStart_280264 := by decide
  rcases family_descends (prefixWord ++ tailWord_280264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280269 : List Nat := [1, 6, 2, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_280269 : Nat := 118140960795 + 280269 * 2 ^ 59
def prefixEnd_280269 : Nat := 4983230072969 + 3 ^ 40 * 280269 * 2
def baseEnd_280269 : Nat := 143912709555069179948573

theorem tailTrace_280269 : CollatzResearch.WordTrace tailWord_280269 prefixEnd_280269 143912709555069179948573 := by
  unfold tailWord_280269
  simp only [CollatzResearch.WordTrace]
  refine ⟨10222250221640753979491861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6814833481093835986327907 10222250221640753979491861)
  ·
    refine ⟨479167979139410342788681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10222250221640753979491861 479167979139410342788681)
    ·
      refine ⟨359375984354557757091511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 479167979139410342788681 359375984354557757091511)
      ·
        refine ⟨539063976531836635637267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359375984354557757091511 539063976531836635637267)
        ·
          refine ⟨808595964797754953455901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 539063976531836635637267 808595964797754953455901)
          ·
            refine ⟨303223486799158107545963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 808595964797754953455901 303223486799158107545963)
            ·
              refine ⟨454835230198737161318945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303223486799158107545963 454835230198737161318945)
              ·
                refine ⟨341126422649052870989209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 454835230198737161318945 341126422649052870989209)
                ·
                  refine ⟨255844816986789653241907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 341126422649052870989209 255844816986789653241907)
                  ·
                    refine ⟨383767225480184479862861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 255844816986789653241907 383767225480184479862861)
                    ·
                      refine ⟨143912709555069179948573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 383767225480184479862861 143912709555069179948573)
                      ·
                        rfl

theorem cell23_280269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_280269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280269 prefixEnd_280269 := by exact prefixLift 280269
  have htrace : WordTrace (prefixWord ++ tailWord_280269) baseStart_280269 baseEnd_280269 := by
    simpa [prefixWord, tailWord_280269, baseEnd_280269] using wordTrace_append hprefix tailTrace_280269
  have hstable : (prefixWord ++ tailWord_280269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280269).length < 2 ^ (prefixWord ++ tailWord_280269).sum := by decide
  have hdescent : baseEnd_280269 < baseStart_280269 := by decide
  rcases family_descends (prefixWord ++ tailWord_280269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280281 : List Nat := [1, 2, 1, 2, 3, 4, 2, 1, 7]
def baseStart_280281 : Nat := 118140960795 + 280281 * 2 ^ 59
def prefixEnd_280281 : Nat := 4983230072969 + 3 ^ 40 * 280281 * 2
def baseEnd_280281 : Nat := 15990985702547014777613

theorem tailTrace_280281 : CollatzResearch.WordTrace tailWord_280281 prefixEnd_280281 15990985702547014777613 := by
  unfold tailWord_280281
  simp only [CollatzResearch.WordTrace]
  refine ⟨10222687897597280028928697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6815125265064853352619131 10222687897597280028928697)
  ·
    refine ⟨7667015923197960021696523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10222687897597280028928697 7667015923197960021696523)
    ·
      refine ⟨11500523884796940032544785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7667015923197960021696523 11500523884796940032544785)
      ·
        refine ⟨8625392913597705024408589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11500523884796940032544785 8625392913597705024408589)
        ·
          refine ⟨3234522342599139384153221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8625392913597705024408589 3234522342599139384153221)
          ·
            refine ⟨606472939237338634528729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3234522342599139384153221 606472939237338634528729)
            ·
              refine ⟨454854704428003975896547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 606472939237338634528729 454854704428003975896547)
              ·
                refine ⟨682282056642005963844821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 454854704428003975896547 682282056642005963844821)
                ·
                  refine ⟨15990985702547014777613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 682282056642005963844821 15990985702547014777613)
                  ·
                    rfl

theorem cell23_280281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 7].length) (baseStart_280281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280281 prefixEnd_280281 := by exact prefixLift 280281
  have htrace : WordTrace (prefixWord ++ tailWord_280281) baseStart_280281 baseEnd_280281 := by
    simpa [prefixWord, tailWord_280281, baseEnd_280281] using wordTrace_append hprefix tailTrace_280281
  have hstable : (prefixWord ++ tailWord_280281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280281).length < 2 ^ (prefixWord ++ tailWord_280281).sum := by decide
  have hdescent : baseEnd_280281 < baseStart_280281 := by decide
  rcases family_descends (prefixWord ++ tailWord_280281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280292 : List Nat := [2, 3, 1, 1, 1, 3, 5, 1, 2, 2, 2]
def baseStart_280292 : Nat := 118140960795 + 280292 * 2 ^ 59
def prefixEnd_280292 : Nat := 4983230072969 + 3 ^ 40 * 280292 * 2
def baseEnd_280292 : Nat := 143924519610122589960967

theorem tailTrace_280292 : CollatzResearch.WordTrace tailWord_280292 prefixEnd_280292 143924519610122589960967 := by
  unfold tailWord_280292
  simp only [CollatzResearch.WordTrace]
  refine ⟨5111544550278714453789565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6815392733704952605052753 5111544550278714453789565)
  ·
    refine ⟨1916829206354517920171087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5111544550278714453789565 1916829206354517920171087)
    ·
      refine ⟨2875243809531776880256631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1916829206354517920171087 2875243809531776880256631)
      ·
        refine ⟨4312865714297665320384947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2875243809531776880256631 4312865714297665320384947)
        ·
          refine ⟨6469298571446497980577421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4312865714297665320384947 6469298571446497980577421)
          ·
            refine ⟨2425986964292436742716533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6469298571446497980577421 2425986964292436742716533)
            ·
              refine ⟨227436277902415944629675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2425986964292436742716533 227436277902415944629675)
              ·
                refine ⟨341154416853623916944513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 227436277902415944629675 341154416853623916944513)
                ·
                  refine ⟨255865812640217937708385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 341154416853623916944513 255865812640217937708385)
                  ·
                    refine ⟨191899359480163453281289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 255865812640217937708385 191899359480163453281289)
                    ·
                      refine ⟨143924519610122589960967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 191899359480163453281289 143924519610122589960967)
                      ·
                        rfl

theorem cell23_280292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 2, 2, 2].length) (baseStart_280292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280292 prefixEnd_280292 := by exact prefixLift 280292
  have htrace : WordTrace (prefixWord ++ tailWord_280292) baseStart_280292 baseEnd_280292 := by
    simpa [prefixWord, tailWord_280292, baseEnd_280292] using wordTrace_append hprefix tailTrace_280292
  have hstable : (prefixWord ++ tailWord_280292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280292).length < 2 ^ (prefixWord ++ tailWord_280292).sum := by decide
  have hdescent : baseEnd_280292 < baseStart_280292 := by decide
  rcases family_descends (prefixWord ++ tailWord_280292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280304 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 7]
def baseStart_280304 : Nat := 118140960795 + 280304 * 2 ^ 59
def prefixEnd_280304 : Nat := 4983230072969 + 3 ^ 40 * 280304 * 2
def baseEnd_280304 : Nat := 143930681377976543010911

theorem tailTrace_280304 : CollatzResearch.WordTrace tailWord_280304 prefixEnd_280304 143930681377976543010911 := by
  unfold tailWord_280304
  simp only [CollatzResearch.WordTrace]
  refine ⟨5111763388256977478507983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6815684517675969971343977 5111763388256977478507983)
  ·
    refine ⟨7667645082385466217761975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5111763388256977478507983 7667645082385466217761975)
    ·
      refine ⟨11501467623578199326642963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7667645082385466217761975 11501467623578199326642963)
      ·
        refine ⟨17252201435367298989964445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11501467623578199326642963 17252201435367298989964445)
        ·
          refine ⟨6469575538262737121236667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17252201435367298989964445 6469575538262737121236667)
          ·
            refine ⟨9704363307394105681855001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6469575538262737121236667 9704363307394105681855001)
            ·
              refine ⟨7278272480545579261391251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9704363307394105681855001 7278272480545579261391251)
              ·
                refine ⟨10917408720818368892086877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7278272480545579261391251 10917408720818368892086877)
                ·
                  refine ⟨4094028270306888334532579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10917408720818368892086877 4094028270306888334532579)
                  ·
                    refine ⟨6141042405460332501798869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4094028270306888334532579 6141042405460332501798869)
                    ·
                      refine ⟨143930681377976543010911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6141042405460332501798869 143930681377976543010911)
                      ·
                        rfl

theorem cell23_280304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 7].length) (baseStart_280304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280304 prefixEnd_280304 := by exact prefixLift 280304
  have htrace : WordTrace (prefixWord ++ tailWord_280304) baseStart_280304 baseEnd_280304 := by
    simpa [prefixWord, tailWord_280304, baseEnd_280304] using wordTrace_append hprefix tailTrace_280304
  have hstable : (prefixWord ++ tailWord_280304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280304).length < 2 ^ (prefixWord ++ tailWord_280304).sum := by decide
  have hdescent : baseEnd_280304 < baseStart_280304 := by decide
  rcases family_descends (prefixWord ++ tailWord_280304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280331 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 4]
def baseStart_280331 : Nat := 118140960795 + 280331 * 2 ^ 59
def prefixEnd_280331 : Nat := 4983230072969 + 3 ^ 40 * 280331 * 2
def baseEnd_280331 : Nat := 143944545355647937373287

theorem tailTrace_280331 : CollatzResearch.WordTrace tailWord_280331 prefixEnd_280331 143944545355647937373287 := by
  unfold tailWord_280331
  simp only [CollatzResearch.WordTrace]
  refine ⟨10224511547416138568248847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6816341031610759045499231 10224511547416138568248847)
  ·
    refine ⟨15336767321124207852373271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10224511547416138568248847 15336767321124207852373271)
    ·
      refine ⟨23005150981686311778559907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15336767321124207852373271 23005150981686311778559907)
      ·
        refine ⟨34507726472529467667839861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23005150981686311778559907 34507726472529467667839861)
        ·
          refine ⟨3235099356799637593859987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34507726472529467667839861 3235099356799637593859987)
          ·
            refine ⟨4852649035199456390789981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3235099356799637593859987 4852649035199456390789981)
            ·
              refine ⟨1819743388199796146546243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4852649035199456390789981 1819743388199796146546243)
              ·
                refine ⟨2729615082299694219819365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1819743388199796146546243 2729615082299694219819365)
                ·
                  refine ⟨511802827931192666216131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2729615082299694219819365 511802827931192666216131)
                  ·
                    refine ⟨767704241896788999324197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 511802827931192666216131 767704241896788999324197)
                    ·
                      refine ⟨143944545355647937373287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 767704241896788999324197 143944545355647937373287)
                      ·
                        rfl

theorem cell23_280331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 4].length) (baseStart_280331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280331 prefixEnd_280331 := by exact prefixLift 280331
  have htrace : WordTrace (prefixWord ++ tailWord_280331) baseStart_280331 baseEnd_280331 := by
    simpa [prefixWord, tailWord_280331, baseEnd_280331] using wordTrace_append hprefix tailTrace_280331
  have hstable : (prefixWord ++ tailWord_280331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280331).length < 2 ^ (prefixWord ++ tailWord_280331).sum := by decide
  have hdescent : baseEnd_280331 < baseStart_280331 := by decide
  rcases family_descends (prefixWord ++ tailWord_280331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280338 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_280338 : Nat := 118140960795 + 280338 * 2 ^ 59
def prefixEnd_280338 : Nat := 4983230072969 + 3 ^ 40 * 280338 * 2
def baseEnd_280338 : Nat := 143948139720229409985755

theorem tailTrace_280338 : CollatzResearch.WordTrace tailWord_280338 prefixEnd_280338 143948139720229409985755 := by
  unfold tailWord_280338
  simp only [CollatzResearch.WordTrace]
  refine ⟨2556191714597694690938417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6816511238927185842502445 2556191714597694690938417)
  ·
    refine ⟨1917143785948271018203813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2556191714597694690938417 1917143785948271018203813)
    ·
      refine ⟨359464459865300815913215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1917143785948271018203813 359464459865300815913215)
      ·
        refine ⟨539196689797951223869823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359464459865300815913215 539196689797951223869823)
        ·
          refine ⟨808795034696926835804735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 539196689797951223869823 808795034696926835804735)
          ·
            refine ⟨1213192552045390253707103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 808795034696926835804735 1213192552045390253707103)
            ·
              refine ⟨1819788828068085380560655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1213192552045390253707103 1819788828068085380560655)
              ·
                refine ⟨2729683242102128070840983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1819788828068085380560655 2729683242102128070840983)
                ·
                  refine ⟨4094524863153192106261475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2729683242102128070840983 4094524863153192106261475)
                  ·
                    refine ⟨6141787294729788159392213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4094524863153192106261475 6141787294729788159392213)
                    ·
                      refine ⟨143948139720229409985755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6141787294729788159392213 143948139720229409985755)
                      ·
                        rfl

theorem cell23_280338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_280338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280338 prefixEnd_280338 := by exact prefixLift 280338
  have htrace : WordTrace (prefixWord ++ tailWord_280338) baseStart_280338 baseEnd_280338 := by
    simpa [prefixWord, tailWord_280338, baseEnd_280338] using wordTrace_append hprefix tailTrace_280338
  have hstable : (prefixWord ++ tailWord_280338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280338).length < 2 ^ (prefixWord ++ tailWord_280338).sum := by decide
  have hdescent : baseEnd_280338 < baseStart_280338 := by decide
  rcases family_descends (prefixWord ++ tailWord_280338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280348 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 1, 6, 2]
def baseStart_280348 : Nat := 118140960795 + 280348 * 2 ^ 59
def prefixEnd_280348 : Nat := 4983230072969 + 3 ^ 40 * 280348 * 2
def baseEnd_280348 : Nat := 143953274526774370860709

theorem tailTrace_280348 : CollatzResearch.WordTrace tailWord_280348 prefixEnd_280348 143953274526774370860709 := by
  unfold tailWord_280348
  simp only [CollatzResearch.WordTrace]
  refine ⟨5112565794177275235808849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6816754392236366981078465 5112565794177275235808849)
  ·
    refine ⟨3834424345632956426856637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5112565794177275235808849 3834424345632956426856637)
    ·
      refine ⟨1437909129612358660071239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3834424345632956426856637 1437909129612358660071239)
      ·
        refine ⟨2156863694418537990106859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1437909129612358660071239 2156863694418537990106859)
        ·
          refine ⟨3235295541627806985160289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2156863694418537990106859 3235295541627806985160289)
          ·
            refine ⟨2426471656220855238870217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3235295541627806985160289 2426471656220855238870217)
            ·
              refine ⟨1819853742165641429152663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2426471656220855238870217 1819853742165641429152663)
              ·
                refine ⟨2729780613248462143728995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1819853742165641429152663 2729780613248462143728995)
                ·
                  refine ⟨4094670919872693215593493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2729780613248462143728995 4094670919872693215593493)
                  ·
                    refine ⟨191937699369032494480945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4094670919872693215593493 191937699369032494480945)
                    ·
                      refine ⟨143953274526774370860709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 191937699369032494480945 143953274526774370860709)
                      ·
                        rfl

theorem cell23_280348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_280348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280348 prefixEnd_280348 := by exact prefixLift 280348
  have htrace : WordTrace (prefixWord ++ tailWord_280348) baseStart_280348 baseEnd_280348 := by
    simpa [prefixWord, tailWord_280348, baseEnd_280348] using wordTrace_append hprefix tailTrace_280348
  have hstable : (prefixWord ++ tailWord_280348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280348).length < 2 ^ (prefixWord ++ tailWord_280348).sum := by decide
  have hdescent : baseEnd_280348 < baseStart_280348 := by decide
  rcases family_descends (prefixWord ++ tailWord_280348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280392 : List Nat := [2, 1, 3, 1, 1, 4, 4, 2, 1, 4]
def baseStart_280392 : Nat := 118140960795 + 280392 * 2 ^ 59
def prefixEnd_280392 : Nat := 4983230072969 + 3 ^ 40 * 280392 * 2
def baseEnd_280392 : Nat := 47991955891857399570169

theorem tailTrace_280392 : CollatzResearch.WordTrace tailWord_280392 prefixEnd_280392 47991955891857399570169 := by
  unfold tailWord_280392
  simp only [CollatzResearch.WordTrace]
  refine ⟨5113368200097572993109715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6817824266796763990812953 5113368200097572993109715)
  ·
    refine ⟨7670052300146359489664573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5113368200097572993109715 7670052300146359489664573)
    ·
      refine ⟨2876269612554884808624215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7670052300146359489664573 2876269612554884808624215)
      ·
        refine ⟨4314404418832327212936323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2876269612554884808624215 4314404418832327212936323)
        ·
          refine ⟨6471606628248490819404485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4314404418832327212936323 6471606628248490819404485)
          ·
            refine ⟨1213426242796592028638341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6471606628248490819404485 1213426242796592028638341)
            ·
              refine ⟨227517420524361005369689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1213426242796592028638341 227517420524361005369689)
              ·
                refine ⟨170638065393270754027267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227517420524361005369689 170638065393270754027267)
                ·
                  refine ⟨255957098089906131040901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170638065393270754027267 255957098089906131040901)
                  ·
                    refine ⟨47991955891857399570169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 255957098089906131040901 47991955891857399570169)
                    ·
                      rfl

theorem cell23_280392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_280392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280392 prefixEnd_280392 := by exact prefixLift 280392
  have htrace : WordTrace (prefixWord ++ tailWord_280392) baseStart_280392 baseEnd_280392 := by
    simpa [prefixWord, tailWord_280392, baseEnd_280392] using wordTrace_append hprefix tailTrace_280392
  have hstable : (prefixWord ++ tailWord_280392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280392).length < 2 ^ (prefixWord ++ tailWord_280392).sum := by decide
  have hdescent : baseEnd_280392 < baseStart_280392 := by decide
  rcases family_descends (prefixWord ++ tailWord_280392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280415 : List Nat := [1, 1, 2, 3, 1, 5, 1, 2, 3, 1, 3]
def baseStart_280415 : Nat := 118140960795 + 280415 * 2 ^ 59
def prefixEnd_280415 : Nat := 4983230072969 + 3 ^ 40 * 280415 * 2
def baseEnd_280415 : Nat := 143987677730625608722901

theorem tailTrace_280415 : CollatzResearch.WordTrace tailWord_280415 prefixEnd_280415 143987677730625608722901 := by
  unfold tailWord_280415
  simp only [CollatzResearch.WordTrace]
  refine ⟨10227575279111820914306699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6818383519407880609537799 10227575279111820914306699)
  ·
    refine ⟨15341362918667731371460049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10227575279111820914306699 15341362918667731371460049)
    ·
      refine ⟨11506022189000798528595037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15341362918667731371460049 11506022189000798528595037)
      ·
        refine ⟨4314758320875299448223139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11506022189000798528595037 4314758320875299448223139)
        ·
          refine ⟨6472137481312949172334709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4314758320875299448223139 6472137481312949172334709)
          ·
            refine ⟨606762888873088984906379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6472137481312949172334709 606762888873088984906379)
            ·
              refine ⟨910144333309633477359569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606762888873088984906379 910144333309633477359569)
              ·
                refine ⟨682608249982225108019677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 910144333309633477359569 682608249982225108019677)
                ·
                  refine ⟨255978093743334415507379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 682608249982225108019677 255978093743334415507379)
                  ·
                    refine ⟨383967140615001623261069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 255978093743334415507379 383967140615001623261069)
                    ·
                      refine ⟨143987677730625608722901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 383967140615001623261069 143987677730625608722901)
                      ·
                        rfl

theorem cell23_280415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_280415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280415 prefixEnd_280415 := by exact prefixLift 280415
  have htrace : WordTrace (prefixWord ++ tailWord_280415) baseStart_280415 baseEnd_280415 := by
    simpa [prefixWord, tailWord_280415, baseEnd_280415] using wordTrace_append hprefix tailTrace_280415
  have hstable : (prefixWord ++ tailWord_280415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280415).length < 2 ^ (prefixWord ++ tailWord_280415).sum := by decide
  have hdescent : baseEnd_280415 < baseStart_280415 := by decide
  rcases family_descends (prefixWord ++ tailWord_280415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280448 : List Nat := [2, 1, 1, 2, 1, 2, 5, 1, 4, 4]
def baseStart_280448 : Nat := 118140960795 + 280448 * 2 ^ 59
def prefixEnd_280448 : Nat := 4983230072969 + 3 ^ 40 * 280448 * 2
def baseEnd_280448 : Nat := 48001540864074659870083

theorem tailTrace_280448 : CollatzResearch.WordTrace tailWord_280448 prefixEnd_280448 48001540864074659870083 := by
  unfold tailWord_280448
  simp only [CollatzResearch.WordTrace]
  refine ⟨5114389443996133775128999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6819185925328178366838665 5114389443996133775128999)
  ·
    refine ⟨7671584165994200662693499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5114389443996133775128999 7671584165994200662693499)
    ·
      refine ⟨11507376248991300994040249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7671584165994200662693499 11507376248991300994040249)
      ·
        refine ⟨8630532186743475745530187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11507376248991300994040249 8630532186743475745530187)
        ·
          refine ⟨12945798280115213618295281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8630532186743475745530187 12945798280115213618295281)
          ·
            refine ⟨9709348710086410213721461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12945798280115213618295281 9709348710086410213721461)
            ·
              refine ⟨910251441570600957536387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9709348710086410213721461 910251441570600957536387)
              ·
                refine ⟨1365377162355901436304581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 910251441570600957536387 1365377162355901436304581)
                ·
                  refine ⟨256008217941731519307109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1365377162355901436304581 256008217941731519307109)
                  ·
                    refine ⟨48001540864074659870083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 256008217941731519307109 48001540864074659870083)
                    ·
                      rfl

theorem cell23_280448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 4, 4].length) (baseStart_280448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280448 prefixEnd_280448 := by exact prefixLift 280448
  have htrace : WordTrace (prefixWord ++ tailWord_280448) baseStart_280448 baseEnd_280448 := by
    simpa [prefixWord, tailWord_280448, baseEnd_280448] using wordTrace_append hprefix tailTrace_280448
  have hstable : (prefixWord ++ tailWord_280448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280448).length < 2 ^ (prefixWord ++ tailWord_280448).sum := by decide
  have hdescent : baseEnd_280448 < baseStart_280448 := by decide
  rcases family_descends (prefixWord ++ tailWord_280448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280449 : List Nat := [1, 2, 4, 4, 1, 1, 2, 1, 3, 1, 3]
def baseStart_280449 : Nat := 118140960795 + 280449 * 2 ^ 59
def prefixEnd_280449 : Nat := 4983230072969 + 3 ^ 40 * 280449 * 2
def baseEnd_280449 : Nat := 144005136072878475697745

theorem tailTrace_280449 : CollatzResearch.WordTrace tailWord_280449 prefixEnd_280449 144005136072878475697745 := by
  unfold tailWord_280449
  simp only [CollatzResearch.WordTrace]
  refine ⟨10228815360988644721044401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6819210240659096480696267 10228815360988644721044401)
  ·
    refine ⟨7671611520741483540783301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10228815360988644721044401 7671611520741483540783301)
    ·
      refine ⟨1438427160139028163896869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7671611520741483540783301 1438427160139028163896869)
      ·
        refine ⟨269705092526067780730663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1438427160139028163896869 269705092526067780730663)
        ·
          refine ⟨404557638789101671095995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269705092526067780730663 404557638789101671095995)
          ·
            refine ⟨606836458183652506643993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404557638789101671095995 606836458183652506643993)
            ·
              refine ⟨455127343637739379982995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 606836458183652506643993 455127343637739379982995)
              ·
                refine ⟨682691015456609069974493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 455127343637739379982995 682691015456609069974493)
                ·
                  refine ⟨256009130796228401240435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 682691015456609069974493 256009130796228401240435)
                  ·
                    refine ⟨384013696194342601860653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 256009130796228401240435 384013696194342601860653)
                    ·
                      refine ⟨144005136072878475697745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 384013696194342601860653 144005136072878475697745)
                      ·
                        rfl

theorem cell23_280449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_280449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280449 prefixEnd_280449 := by exact prefixLift 280449
  have htrace : WordTrace (prefixWord ++ tailWord_280449) baseStart_280449 baseEnd_280449 := by
    simpa [prefixWord, tailWord_280449, baseEnd_280449] using wordTrace_append hprefix tailTrace_280449
  have hstable : (prefixWord ++ tailWord_280449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280449).length < 2 ^ (prefixWord ++ tailWord_280449).sum := by decide
  have hdescent : baseEnd_280449 < baseStart_280449 := by decide
  rcases family_descends (prefixWord ++ tailWord_280449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280505 : List Nat := [1, 2, 1, 4, 2, 1, 1, 3, 4, 1, 3]
def baseStart_280505 : Nat := 118140960795 + 280505 * 2 ^ 59
def prefixEnd_280505 : Nat := 4983230072969 + 3 ^ 40 * 280505 * 2
def baseEnd_280505 : Nat := 144033890989530256597487

theorem tailTrace_280505 : CollatzResearch.WordTrace tailWord_280505 prefixEnd_280505 144033890989530256597487 := by
  unfold tailWord_280505
  simp only [CollatzResearch.WordTrace]
  refine ⟨10230857848785766285082969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6820571899190510856721979 10230857848785766285082969)
  ·
    refine ⟨7673143386589324713812227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10230857848785766285082969 7673143386589324713812227)
    ·
      refine ⟨11509715079883987070718341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7673143386589324713812227 11509715079883987070718341)
      ·
        refine ⟨2158071577478247575759689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11509715079883987070718341 2158071577478247575759689)
        ·
          refine ⟨1618553683108685681819767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2158071577478247575759689 1618553683108685681819767)
          ·
            refine ⟨2427830524663028522729651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1618553683108685681819767 2427830524663028522729651)
            ·
              refine ⟨3641745786994542784094477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2427830524663028522729651 3641745786994542784094477)
              ·
                refine ⟨1365654670122953544035429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3641745786994542784094477 1365654670122953544035429)
                ·
                  refine ⟨256060250648053789506643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1365654670122953544035429 256060250648053789506643)
                  ·
                    refine ⟨384090375972080684259965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 256060250648053789506643 384090375972080684259965)
                    ·
                      refine ⟨144033890989530256597487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 384090375972080684259965 144033890989530256597487)
                      ·
                        rfl

theorem cell23_280505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_280505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280505 prefixEnd_280505 := by exact prefixLift 280505
  have htrace : WordTrace (prefixWord ++ tailWord_280505) baseStart_280505 baseEnd_280505 := by
    simpa [prefixWord, tailWord_280505, baseEnd_280505] using wordTrace_append hprefix tailTrace_280505
  have hstable : (prefixWord ++ tailWord_280505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280505).length < 2 ^ (prefixWord ++ tailWord_280505).sum := by decide
  have hdescent : baseEnd_280505 < baseStart_280505 := by decide
  rcases family_descends (prefixWord ++ tailWord_280505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280531 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 9]
def baseStart_280531 : Nat := 118140960795 + 280531 * 2 ^ 59
def prefixEnd_280531 : Nat := 4983230072969 + 3 ^ 40 * 280531 * 2
def baseEnd_280531 : Nat := 144047241486547154872367

theorem tailTrace_280531 : CollatzResearch.WordTrace tailWord_280531 prefixEnd_280531 144047241486547154872367 := by
  unfold tailWord_280531
  simp only [CollatzResearch.WordTrace]
  refine ⟨10231806146691572725529447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6821204097794381817019631 10231806146691572725529447)
  ·
    refine ⟨15347709220037359088294171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10231806146691572725529447 15347709220037359088294171)
    ·
      refine ⟨23021563830056038632441257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15347709220037359088294171 23021563830056038632441257)
      ·
        refine ⟨17266172872542028974330943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23021563830056038632441257 17266172872542028974330943)
        ·
          refine ⟨25899259308813043461496415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17266172872542028974330943 25899259308813043461496415)
          ·
            refine ⟨38848888963219565192244623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25899259308813043461496415 38848888963219565192244623)
            ·
              refine ⟨58273333444829347788366935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38848888963219565192244623 58273333444829347788366935)
              ·
                refine ⟨87410000167244021682550403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58273333444829347788366935 87410000167244021682550403)
                ·
                  refine ⟨131115000250866032523825605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87410000167244021682550403 131115000250866032523825605)
                  ·
                    refine ⟨24584062547037381098217301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 131115000250866032523825605 24584062547037381098217301)
                    ·
                      refine ⟨144047241486547154872367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 24584062547037381098217301 144047241486547154872367)
                      ·
                        rfl

theorem cell23_280531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 9].length) (baseStart_280531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280531 prefixEnd_280531 := by exact prefixLift 280531
  have htrace : WordTrace (prefixWord ++ tailWord_280531) baseStart_280531 baseEnd_280531 := by
    simpa [prefixWord, tailWord_280531, baseEnd_280531] using wordTrace_append hprefix tailTrace_280531
  have hstable : (prefixWord ++ tailWord_280531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280531).length < 2 ^ (prefixWord ++ tailWord_280531).sum := by decide
  have hdescent : baseEnd_280531 < baseStart_280531 := by decide
  rcases family_descends (prefixWord ++ tailWord_280531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280532 : List Nat := [2, 4, 1, 2, 1, 1, 3, 1, 3, 3, 2]
def baseStart_280532 : Nat := 118140960795 + 280532 * 2 ^ 59
def prefixEnd_280532 : Nat := 4983230072969 + 3 ^ 40 * 280532 * 2
def baseEnd_280532 : Nat := 144047754967201650959863

theorem tailTrace_280532 : CollatzResearch.WordTrace tailWord_280532 prefixEnd_280532 144047754967201650959863 := by
  unfold tailWord_280532
  simp only [CollatzResearch.WordTrace]
  refine ⟨5115921309843974948157925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6821228413125299930877233 5115921309843974948157925)
  ·
    refine ⟨959235245595745302779611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5115921309843974948157925 959235245595745302779611)
    ·
      refine ⟨1438852868393617954169417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 959235245595745302779611 1438852868393617954169417)
      ·
        refine ⟨1079139651295213465627063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1438852868393617954169417 1079139651295213465627063)
        ·
          refine ⟨1618709476942820198440595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1079139651295213465627063 1618709476942820198440595)
          ·
            refine ⟨2428064215414230297660893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1618709476942820198440595 2428064215414230297660893)
            ·
              refine ⟨910524080780336361622835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2428064215414230297660893 910524080780336361622835)
              ·
                refine ⟨1365786121170504542434253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 910524080780336361622835 1365786121170504542434253)
                ·
                  refine ⟨512169795438939203412845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1365786121170504542434253 512169795438939203412845)
                  ·
                    refine ⟨192063673289602201279817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 512169795438939203412845 192063673289602201279817)
                    ·
                      refine ⟨144047754967201650959863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 192063673289602201279817 144047754967201650959863)
                      ·
                        rfl

theorem cell23_280532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_280532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280532 prefixEnd_280532 := by exact prefixLift 280532
  have htrace : WordTrace (prefixWord ++ tailWord_280532) baseStart_280532 baseEnd_280532 := by
    simpa [prefixWord, tailWord_280532, baseEnd_280532] using wordTrace_append hprefix tailTrace_280532
  have hstable : (prefixWord ++ tailWord_280532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280532).length < 2 ^ (prefixWord ++ tailWord_280532).sum := by decide
  have hdescent : baseEnd_280532 < baseStart_280532 := by decide
  rcases family_descends (prefixWord ++ tailWord_280532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280545 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 3, 4, 2]
def baseStart_280545 : Nat := 118140960795 + 280545 * 2 ^ 59
def prefixEnd_280545 : Nat := 4983230072969 + 3 ^ 40 * 280545 * 2
def baseEnd_280545 : Nat := 144054430215710100097303

theorem tailTrace_280545 : CollatzResearch.WordTrace tailWord_280545 prefixEnd_280545 144054430215710100097303 := by
  unfold tailWord_280545
  simp only [CollatzResearch.WordTrace]
  refine ⟨10232316768640853116539089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6821544512427235411026059 10232316768640853116539089)
  ·
    refine ⟨7674237576480639837404317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10232316768640853116539089 7674237576480639837404317)
    ·
      refine ⟨2877839091180239939026619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7674237576480639837404317 2877839091180239939026619)
      ·
        refine ⟨4316758636770359908539929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2877839091180239939026619 4316758636770359908539929)
        ·
          refine ⟨3237568977577769931404947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4316758636770359908539929 3237568977577769931404947)
          ·
            refine ⟨4856353466366654897107421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3237568977577769931404947 4856353466366654897107421)
            ·
              refine ⟨1821132549887495586415283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4856353466366654897107421 1821132549887495586415283)
              ·
                refine ⟨2731698824831243379622925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1821132549887495586415283 2731698824831243379622925)
                ·
                  refine ⟨1024387059311716267358597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2731698824831243379622925 1024387059311716267358597)
                  ·
                    refine ⟨192072573620946800129737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1024387059311716267358597 192072573620946800129737)
                    ·
                      refine ⟨144054430215710100097303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 192072573620946800129737 144054430215710100097303)
                      ·
                        rfl

theorem cell23_280545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 4, 2].length) (baseStart_280545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280545 prefixEnd_280545 := by exact prefixLift 280545
  have htrace : WordTrace (prefixWord ++ tailWord_280545) baseStart_280545 baseEnd_280545 := by
    simpa [prefixWord, tailWord_280545, baseEnd_280545] using wordTrace_append hprefix tailTrace_280545
  have hstable : (prefixWord ++ tailWord_280545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280545).length < 2 ^ (prefixWord ++ tailWord_280545).sum := by decide
  have hdescent : baseEnd_280545 < baseStart_280545 := by decide
  rcases family_descends (prefixWord ++ tailWord_280545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280548 : List Nat := [2, 3, 1, 1, 1, 1, 3, 3, 2, 1, 5]
def baseStart_280548 : Nat := 118140960795 + 280548 * 2 ^ 59
def prefixEnd_280548 : Nat := 4983230072969 + 3 ^ 40 * 280548 * 2
def baseEnd_280548 : Nat := 144055970657673588359789

theorem tailTrace_280548 : CollatzResearch.WordTrace tailWord_280548 prefixEnd_280548 144055970657673588359789 := by
  unfold tailWord_280548
  simp only [CollatzResearch.WordTrace]
  refine ⟨5116213093814992314449149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6821617458419989752598865 5116213093814992314449149)
  ·
    refine ⟨1918579910180622117918431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5116213093814992314449149 1918579910180622117918431)
    ·
      refine ⟨2877869865270933176877647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1918579910180622117918431 2877869865270933176877647)
      ·
        refine ⟨4316804797906399765316471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2877869865270933176877647 4316804797906399765316471)
        ·
          refine ⟨6475207196859599647974707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4316804797906399765316471 6475207196859599647974707)
          ·
            refine ⟨9712810795289399471962061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6475207196859599647974707 9712810795289399471962061)
            ·
              refine ⟨3642304048233524801985773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9712810795289399471962061 3642304048233524801985773)
              ·
                refine ⟨1365864018087571800744665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3642304048233524801985773 1365864018087571800744665)
                ·
                  refine ⟨1024398013565678850558499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1365864018087571800744665 1024398013565678850558499)
                  ·
                    refine ⟨1536597020348518275837749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1024398013565678850558499 1536597020348518275837749)
                    ·
                      refine ⟨144055970657673588359789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1536597020348518275837749 144055970657673588359789)
                      ·
                        rfl

theorem cell23_280548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_280548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280548 prefixEnd_280548 := by exact prefixLift 280548
  have htrace : WordTrace (prefixWord ++ tailWord_280548) baseStart_280548 baseEnd_280548 := by
    simpa [prefixWord, tailWord_280548, baseEnd_280548] using wordTrace_append hprefix tailTrace_280548
  have hstable : (prefixWord ++ tailWord_280548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280548).length < 2 ^ (prefixWord ++ tailWord_280548).sum := by decide
  have hdescent : baseEnd_280548 < baseStart_280548 := by decide
  rcases family_descends (prefixWord ++ tailWord_280548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280557 : List Nat := [1, 5, 1, 4, 2, 1, 2, 2, 1, 2, 2]
def baseStart_280557 : Nat := 118140960795 + 280557 * 2 ^ 59
def prefixEnd_280557 : Nat := 4983230072969 + 3 ^ 40 * 280557 * 2
def baseEnd_280557 : Nat := 144060591983564053147249

theorem tailTrace_280557 : CollatzResearch.WordTrace tailWord_280557 prefixEnd_280557 144060591983564053147249 := by
  unfold tailWord_280557
  simp only [CollatzResearch.WordTrace]
  refine ⟨10232754444597379165975925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6821836296398252777317283 10232754444597379165975925)
  ·
    refine ⟨959320729181004296810243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10232754444597379165975925 959320729181004296810243)
    ·
      refine ⟨1438981093771506445215365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 959320729181004296810243 1438981093771506445215365)
      ·
        refine ⟨269808955082157458477881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1438981093771506445215365 269808955082157458477881)
        ·
          refine ⟨202356716311618093858411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269808955082157458477881 202356716311618093858411)
          ·
            refine ⟨303535074467427140787617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202356716311618093858411 303535074467427140787617)
            ·
              refine ⟨227651305850570355590713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 303535074467427140787617 227651305850570355590713)
              ·
                refine ⟨170738479387927766693035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227651305850570355590713 170738479387927766693035)
                ·
                  refine ⟨256107719081891650039553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170738479387927766693035 256107719081891650039553)
                  ·
                    refine ⟨192080789311418737529665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 256107719081891650039553 192080789311418737529665)
                    ·
                      refine ⟨144060591983564053147249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 192080789311418737529665 144060591983564053147249)
                      ·
                        rfl

theorem cell23_280557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_280557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280557 prefixEnd_280557 := by exact prefixLift 280557
  have htrace : WordTrace (prefixWord ++ tailWord_280557) baseStart_280557 baseEnd_280557 := by
    simpa [prefixWord, tailWord_280557, baseEnd_280557] using wordTrace_append hprefix tailTrace_280557
  have hstable : (prefixWord ++ tailWord_280557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280557).length < 2 ^ (prefixWord ++ tailWord_280557).sum := by decide
  have hdescent : baseEnd_280557 < baseStart_280557 := by decide
  rcases family_descends (prefixWord ++ tailWord_280557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280602 : List Nat := [3, 1, 1, 3, 1, 4, 2, 3, 5]
def baseStart_280602 : Nat := 118140960795 + 280602 * 2 ^ 59
def prefixEnd_280602 : Nat := 4983230072969 + 3 ^ 40 * 280602 * 2
def baseEnd_280602 : Nat := 16009299845890708564949

theorem tailTrace_280602 : CollatzResearch.WordTrace tailWord_280602 prefixEnd_280602 16009299845890708564949 := by
  unfold tailWord_280602
  simp only [CollatzResearch.WordTrace]
  refine ⟨2558598932358587962841015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6822930486289567900909373 2558598932358587962841015)
  ·
    refine ⟨3837898398537881944261523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2558598932358587962841015 3837898398537881944261523)
    ·
      refine ⟨5756847597806822916392285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3837898398537881944261523 5756847597806822916392285)
      ·
        refine ⟨2158817849177558593647107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5756847597806822916392285 2158817849177558593647107)
        ·
          refine ⟨3238226773766337890470661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2158817849177558593647107 3238226773766337890470661)
          ·
            refine ⟨607167520081188354463249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3238226773766337890470661 607167520081188354463249)
            ·
              refine ⟨455375640060891265847437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 607167520081188354463249 455375640060891265847437)
              ·
                refine ⟨170765865022834224692789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 455375640060891265847437 170765865022834224692789)
                ·
                  refine ⟨16009299845890708564949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 170765865022834224692789 16009299845890708564949)
                  ·
                    rfl

theorem cell23_280602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 3, 5].length) (baseStart_280602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280602 prefixEnd_280602 := by exact prefixLift 280602
  have htrace : WordTrace (prefixWord ++ tailWord_280602) baseStart_280602 baseEnd_280602 := by
    simpa [prefixWord, tailWord_280602, baseEnd_280602] using wordTrace_append hprefix tailTrace_280602
  have hstable : (prefixWord ++ tailWord_280602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280602).length < 2 ^ (prefixWord ++ tailWord_280602).sum := by decide
  have hdescent : baseEnd_280602 < baseStart_280602 := by decide
  rcases family_descends (prefixWord ++ tailWord_280602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280648 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 1, 3, 6]
def baseStart_280648 : Nat := 118140960795 + 280648 * 2 ^ 59
def prefixEnd_280648 : Nat := 4983230072969 + 3 ^ 40 * 280648 * 2
def baseEnd_280648 : Nat := 144107318723123197109329

theorem tailTrace_280648 : CollatzResearch.WordTrace tailWord_280648 prefixEnd_280648 144107318723123197109329 := by
  unfold tailWord_280648
  simp only [CollatzResearch.WordTrace]
  refine ⟨5118036743633850853769299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6824048991511801138359065 5118036743633850853769299)
  ·
    refine ⟨7677055115450776280653949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5118036743633850853769299 7677055115450776280653949)
    ·
      refine ⟨2878895668294041105245231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7677055115450776280653949 2878895668294041105245231)
      ·
        refine ⟨4318343502441061657867847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2878895668294041105245231 4318343502441061657867847)
        ·
          refine ⟨6477515253661592486801771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4318343502441061657867847 6477515253661592486801771)
          ·
            refine ⟨9716272880492388730202657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6477515253661592486801771 9716272880492388730202657)
            ·
              refine ⟨7287204660369291547651993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9716272880492388730202657 7287204660369291547651993)
              ·
                refine ⟨5465403495276968660738995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7287204660369291547651993 5465403495276968660738995)
                ·
                  refine ⟨8198105242915452991108493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5465403495276968660738995 8198105242915452991108493)
                  ·
                    refine ⟨3074289466093294871665685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8198105242915452991108493 3074289466093294871665685)
                    ·
                      refine ⟨144107318723123197109329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3074289466093294871665685 144107318723123197109329)
                      ·
                        rfl

theorem cell23_280648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_280648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280648 prefixEnd_280648 := by exact prefixLift 280648
  have htrace : WordTrace (prefixWord ++ tailWord_280648) baseStart_280648 baseEnd_280648 := by
    simpa [prefixWord, tailWord_280648, baseEnd_280648] using wordTrace_append hprefix tailTrace_280648
  have hstable : (prefixWord ++ tailWord_280648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280648).length < 2 ^ (prefixWord ++ tailWord_280648).sum := by decide
  have hdescent : baseEnd_280648 < baseStart_280648 := by decide
  rcases family_descends (prefixWord ++ tailWord_280648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280669 : List Nat := [1, 4, 4, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_280669 : Nat := 118140960795 + 280669 * 2 ^ 59
def prefixEnd_280669 : Nat := 4983230072969 + 3 ^ 40 * 280669 * 2
def baseEnd_280669 : Nat := 144118101816867614946733

theorem tailTrace_280669 : CollatzResearch.WordTrace tailWord_280669 prefixEnd_280669 144118101816867614946733 := by
  unfold tailWord_280669
  simp only [CollatzResearch.WordTrace]
  refine ⟨10236839420191622294053061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6824559613461081529368707 10236839420191622294053061)
  ·
    refine ⟨1919407391285929180134949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10236839420191622294053061 1919407391285929180134949)
    ·
      refine ⟨359888885866111721275303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1919407391285929180134949 359888885866111721275303)
      ·
        refine ⟨539833328799167581912955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359888885866111721275303 539833328799167581912955)
        ·
          refine ⟨809749993198751372869433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 539833328799167581912955 809749993198751372869433)
          ·
            refine ⟨607312494899063529652075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 809749993198751372869433 607312494899063529652075)
            ·
              refine ⟨910968742348595294478113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 607312494899063529652075 910968742348595294478113)
              ·
                refine ⟨683226556761446470858585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 910968742348595294478113 683226556761446470858585)
                ·
                  refine ⟨512419917571084853143939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 683226556761446470858585 512419917571084853143939)
                  ·
                    refine ⟨768629876356627279715909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 512419917571084853143939 768629876356627279715909)
                    ·
                      refine ⟨144118101816867614946733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 768629876356627279715909 144118101816867614946733)
                      ·
                        rfl

theorem cell23_280669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_280669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280669 prefixEnd_280669 := by exact prefixLift 280669
  have htrace : WordTrace (prefixWord ++ tailWord_280669) baseStart_280669 baseEnd_280669 := by
    simpa [prefixWord, tailWord_280669, baseEnd_280669] using wordTrace_append hprefix tailTrace_280669
  have hstable : (prefixWord ++ tailWord_280669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280669).length < 2 ^ (prefixWord ++ tailWord_280669).sum := by decide
  have hdescent : baseEnd_280669 < baseStart_280669 := by decide
  rcases family_descends (prefixWord ++ tailWord_280669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280672 : List Nat := [2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 3]
def baseStart_280672 : Nat := 118140960795 + 280672 * 2 ^ 59
def prefixEnd_280672 : Nat := 4983230072969 + 3 ^ 40 * 280672 * 2
def baseEnd_280672 : Nat := 144119642258831103209219

theorem tailTrace_280672 : CollatzResearch.WordTrace tailWord_280672 prefixEnd_280672 144119642258831103209219 := by
  unfold tailWord_280672
  simp only [CollatzResearch.WordTrace]
  refine ⟨5118474419590376903206135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6824632559453835870941513 5118474419590376903206135)
  ·
    refine ⟨7677711629385565354809203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5118474419590376903206135 7677711629385565354809203)
    ·
      refine ⟨11516567444078348032213805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7677711629385565354809203 11516567444078348032213805)
      ·
        refine ⟨4318712791529380512080177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11516567444078348032213805 4318712791529380512080177)
        ·
          refine ⟨3239034593647035384060133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4318712791529380512080177 3239034593647035384060133)
          ·
            refine ⟨607318986308819134511275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3239034593647035384060133 607318986308819134511275)
            ·
              refine ⟨910978479463228701766913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 607318986308819134511275 910978479463228701766913)
              ·
                refine ⟨683233859597421526325185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 910978479463228701766913 683233859597421526325185)
                ·
                  refine ⟨512425394698066144743889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 683233859597421526325185 512425394698066144743889)
                  ·
                    refine ⟨384319046023549608557917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 512425394698066144743889 384319046023549608557917)
                    ·
                      refine ⟨144119642258831103209219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 384319046023549608557917 144119642258831103209219)
                      ·
                        rfl

theorem cell23_280672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_280672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280672 prefixEnd_280672 := by exact prefixLift 280672
  have htrace : WordTrace (prefixWord ++ tailWord_280672) baseStart_280672 baseEnd_280672 := by
    simpa [prefixWord, tailWord_280672, baseEnd_280672] using wordTrace_append hprefix tailTrace_280672
  have hstable : (prefixWord ++ tailWord_280672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280672).length < 2 ^ (prefixWord ++ tailWord_280672).sum := by decide
  have hdescent : baseEnd_280672 < baseStart_280672 := by decide
  rcases family_descends (prefixWord ++ tailWord_280672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280730 : List Nat := [3, 1, 1, 5, 3, 1, 2, 2, 1, 4]
def baseStart_280730 : Nat := 118140960795 + 280730 * 2 ^ 59
def prefixEnd_280730 : Nat := 4983230072969 + 3 ^ 40 * 280730 * 2
def baseEnd_280730 : Nat := 48049808045597292094651

theorem tailTrace_280730 : CollatzResearch.WordTrace tailWord_280730 prefixEnd_280730 48049808045597292094651 := by
  unfold tailWord_280730
  simp only [CollatzResearch.WordTrace]
  refine ⟨2559766068242657428005911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6826042848647086474682429 2559766068242657428005911)
  ·
    refine ⟨3839649102363986142008867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2559766068242657428005911 3839649102363986142008867)
    ·
      refine ⟨5759473653545979213013301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3839649102363986142008867 5759473653545979213013301)
      ·
        refine ⟨539950655019935551219997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5759473653545979213013301 539950655019935551219997)
        ·
          refine ⟨202481495632475831707499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 539950655019935551219997 202481495632475831707499)
          ·
            refine ⟨303722243448713747561249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202481495632475831707499 303722243448713747561249)
            ·
              refine ⟨227791682586535310670937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 303722243448713747561249 227791682586535310670937)
              ·
                refine ⟨170843761939901483003203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227791682586535310670937 170843761939901483003203)
                ·
                  refine ⟨256265642909852224504805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170843761939901483003203 256265642909852224504805)
                  ·
                    refine ⟨48049808045597292094651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 256265642909852224504805 48049808045597292094651)
                    ·
                      rfl

theorem cell23_280730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 2, 1, 4].length) (baseStart_280730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280730 prefixEnd_280730 := by exact prefixLift 280730
  have htrace : WordTrace (prefixWord ++ tailWord_280730) baseStart_280730 baseEnd_280730 := by
    simpa [prefixWord, tailWord_280730, baseEnd_280730] using wordTrace_append hprefix tailTrace_280730
  have hstable : (prefixWord ++ tailWord_280730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280730).length < 2 ^ (prefixWord ++ tailWord_280730).sum := by decide
  have hdescent : baseEnd_280730 < baseStart_280730 := by decide
  rcases family_descends (prefixWord ++ tailWord_280730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280736 : List Nat := [2, 1, 1, 4, 2, 3, 1, 4, 1, 1, 3]
def baseStart_280736 : Nat := 118140960795 + 280736 * 2 ^ 59
def prefixEnd_280736 : Nat := 4983230072969 + 3 ^ 40 * 280736 * 2
def baseEnd_280736 : Nat := 144152505020718852808925

theorem tailTrace_280736 : CollatzResearch.WordTrace tailWord_280736 prefixEnd_280736 144152505020718852808925 := by
  unfold tailWord_280736
  simp only [CollatzResearch.WordTrace]
  refine ⟨5119641555474446368371031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6826188740632595157828041 5119641555474446368371031)
  ·
    refine ⟨7679462333211669552556547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5119641555474446368371031 7679462333211669552556547)
    ·
      refine ⟨11519193499817504328834821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7679462333211669552556547 11519193499817504328834821)
      ·
        refine ⟨2159848781215782061656529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11519193499817504328834821 2159848781215782061656529)
        ·
          refine ⟨1619886585911836546242397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2159848781215782061656529 1619886585911836546242397)
          ·
            refine ⟨607457469716938704840899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1619886585911836546242397 607457469716938704840899)
            ·
              refine ⟨911186204575408057261349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 607457469716938704840899 911186204575408057261349)
              ·
                refine ⟨170847413357889010736503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 911186204575408057261349 170847413357889010736503)
                ·
                  refine ⟨256271120036833516104755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170847413357889010736503 256271120036833516104755)
                  ·
                    refine ⟨384406680055250274157133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 256271120036833516104755 384406680055250274157133)
                    ·
                      refine ⟨144152505020718852808925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 384406680055250274157133 144152505020718852808925)
                      ·
                        rfl

theorem cell23_280736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_280736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280736 prefixEnd_280736 := by exact prefixLift 280736
  have htrace : WordTrace (prefixWord ++ tailWord_280736) baseStart_280736 baseEnd_280736 := by
    simpa [prefixWord, tailWord_280736, baseEnd_280736] using wordTrace_append hprefix tailTrace_280736
  have hstable : (prefixWord ++ tailWord_280736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280736).length < 2 ^ (prefixWord ++ tailWord_280736).sum := by decide
  have hdescent : baseEnd_280736 < baseStart_280736 := by decide
  rcases family_descends (prefixWord ++ tailWord_280736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280759 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 5, 2, 2]
def baseStart_280759 : Nat := 118140960795 + 280759 * 2 ^ 59
def prefixEnd_280759 : Nat := 4983230072969 + 3 ^ 40 * 280759 * 2
def baseEnd_280759 : Nat := 144164315075772262821319

theorem tailTrace_280759 : CollatzResearch.WordTrace tailWord_280759 prefixEnd_280759 144164315075772262821319 := by
  unfold tailWord_280759
  simp only [CollatzResearch.WordTrace]
  refine ⟨10240121989865567664829331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6826747993243711776552887 10240121989865567664829331)
  ·
    refine ⟨15360182984798351497243997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10240121989865567664829331 15360182984798351497243997)
    ·
      refine ⟨5760068619299381811466499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15360182984798351497243997 5760068619299381811466499)
      ·
        refine ⟨8640102928949072717199749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5760068619299381811466499 8640102928949072717199749)
        ·
          refine ⟨1620019299177951134474953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8640102928949072717199749 1620019299177951134474953)
          ·
            refine ⟨1215014474383463350856215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1620019299177951134474953 1215014474383463350856215)
            ·
              refine ⟨1822521711575195026284323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1215014474383463350856215 1822521711575195026284323)
              ·
                refine ⟨2733782567362792539426485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1822521711575195026284323 2733782567362792539426485)
                ·
                  refine ⟨256292115690261800571233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2733782567362792539426485 256292115690261800571233)
                  ·
                    refine ⟨192219086767696350428425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 256292115690261800571233 192219086767696350428425)
                    ·
                      refine ⟨144164315075772262821319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 192219086767696350428425 144164315075772262821319)
                      ·
                        rfl

theorem cell23_280759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 5, 2, 2].length) (baseStart_280759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280759 prefixEnd_280759 := by exact prefixLift 280759
  have htrace : WordTrace (prefixWord ++ tailWord_280759) baseStart_280759 baseEnd_280759 := by
    simpa [prefixWord, tailWord_280759, baseEnd_280759] using wordTrace_append hprefix tailTrace_280759
  have hstable : (prefixWord ++ tailWord_280759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280759).length < 2 ^ (prefixWord ++ tailWord_280759).sum := by decide
  have hdescent : baseEnd_280759 < baseStart_280759 := by decide
  rcases family_descends (prefixWord ++ tailWord_280759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280762 : List Nat := [3, 1, 1, 1, 2, 2, 4, 1, 3, 2, 3]
def baseStart_280762 : Nat := 118140960795 + 280762 * 2 ^ 59
def prefixEnd_280762 : Nat := 4983230072969 + 3 ^ 40 * 280762 * 2
def baseEnd_280762 : Nat := 144165855517735751083805

theorem tailTrace_280762 : CollatzResearch.WordTrace tailWord_280762 prefixEnd_280762 144165855517735751083805 := by
  unfold tailWord_280762
  simp only [CollatzResearch.WordTrace]
  refine ⟨2560057852213674794297135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6826820939236466118125693 2560057852213674794297135)
  ·
    refine ⟨3840086778320512191445703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2560057852213674794297135 3840086778320512191445703)
    ·
      refine ⟨5760130167480768287168555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3840086778320512191445703 5760130167480768287168555)
      ·
        refine ⟨8640195251221152430752833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5760130167480768287168555 8640195251221152430752833)
        ·
          refine ⟨6480146438415864323064625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8640195251221152430752833 6480146438415864323064625)
          ·
            refine ⟨4860109828811898242298469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6480146438415864323064625 4860109828811898242298469)
            ·
              refine ⟨911270592902230920430963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4860109828811898242298469 911270592902230920430963)
              ·
                refine ⟨1366905889353346380646445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 911270592902230920430963 1366905889353346380646445)
                ·
                  refine ⟨512589708507504892742417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1366905889353346380646445 512589708507504892742417)
                  ·
                    refine ⟨384442281380628669556813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 512589708507504892742417 384442281380628669556813)
                    ·
                      refine ⟨144165855517735751083805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 384442281380628669556813 144165855517735751083805)
                      ·
                        rfl

theorem cell23_280762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 3, 2, 3].length) (baseStart_280762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280762 prefixEnd_280762 := by exact prefixLift 280762
  have htrace : WordTrace (prefixWord ++ tailWord_280762) baseStart_280762 baseEnd_280762 := by
    simpa [prefixWord, tailWord_280762, baseEnd_280762] using wordTrace_append hprefix tailTrace_280762
  have hstable : (prefixWord ++ tailWord_280762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280762).length < 2 ^ (prefixWord ++ tailWord_280762).sum := by decide
  have hdescent : baseEnd_280762 < baseStart_280762 := by decide
  rcases family_descends (prefixWord ++ tailWord_280762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280770 : List Nat := [3, 5, 1, 1, 1, 1, 1, 5, 1, 1, 3]
def baseStart_280770 : Nat := 118140960795 + 280770 * 2 ^ 59
def prefixEnd_280770 : Nat := 4983230072969 + 3 ^ 40 * 280770 * 2
def baseEnd_280770 : Nat := 144169963362971719783769

theorem tailTrace_280770 : CollatzResearch.WordTrace tailWord_280770 prefixEnd_280770 144169963362971719783769 := by
  unfold tailWord_280770
  simp only [CollatzResearch.WordTrace]
  refine ⟨2560130798206429135869941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6827015461883811028986509 2560130798206429135869941)
  ·
    refine ⟨240012262331852731487807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2560130798206429135869941 240012262331852731487807)
    ·
      refine ⟨360018393497779097231711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240012262331852731487807 360018393497779097231711)
      ·
        refine ⟨540027590246668645847567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360018393497779097231711 540027590246668645847567)
        ·
          refine ⟨810041385370002968771351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 540027590246668645847567 810041385370002968771351)
          ·
            refine ⟨1215062078055004453157027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 810041385370002968771351 1215062078055004453157027)
            ·
              refine ⟨1822593117082506679735541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1215062078055004453157027 1822593117082506679735541)
              ·
                refine ⟨170868104726485001225207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1822593117082506679735541 170868104726485001225207)
                ·
                  refine ⟨256302157089727501837811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170868104726485001225207 256302157089727501837811)
                  ·
                    refine ⟨384453235634591252756717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 256302157089727501837811 384453235634591252756717)
                    ·
                      refine ⟨144169963362971719783769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 384453235634591252756717 144169963362971719783769)
                      ·
                        rfl

theorem cell23_280770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_280770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280770 prefixEnd_280770 := by exact prefixLift 280770
  have htrace : WordTrace (prefixWord ++ tailWord_280770) baseStart_280770 baseEnd_280770 := by
    simpa [prefixWord, tailWord_280770, baseEnd_280770] using wordTrace_append hprefix tailTrace_280770
  have hstable : (prefixWord ++ tailWord_280770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280770).length < 2 ^ (prefixWord ++ tailWord_280770).sum := by decide
  have hdescent : baseEnd_280770 < baseStart_280770 := by decide
  rcases family_descends (prefixWord ++ tailWord_280770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280786 : List Nat := [3, 2, 2, 2, 1, 4, 1, 2, 2, 4]
def baseStart_280786 : Nat := 118140960795 + 280786 * 2 ^ 59
def prefixEnd_280786 : Nat := 4983230072969 + 3 ^ 40 * 280786 * 2
def baseEnd_280786 : Nat := 48059393017814552394565

theorem tailTrace_280786 : CollatzResearch.WordTrace tailWord_280786 prefixEnd_280786 48059393017814552394565 := by
  unfold tailWord_280786
  simp only [CollatzResearch.WordTrace]
  refine ⟨2560276690191937819015553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6827404507178500850708141 2560276690191937819015553)
  ·
    refine ⟨1920207517643953364261665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2560276690191937819015553 1920207517643953364261665)
    ·
      refine ⟨1440155638232965023196249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1920207517643953364261665 1440155638232965023196249)
      ·
        refine ⟨1080116728674723767397187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1440155638232965023196249 1080116728674723767397187)
        ·
          refine ⟨1620175093012085651095781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1080116728674723767397187 1620175093012085651095781)
          ·
            refine ⟨303782829939766059580459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1620175093012085651095781 303782829939766059580459)
            ·
              refine ⟨455674244909649089370689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303782829939766059580459 455674244909649089370689)
              ·
                refine ⟨341755683682236817028017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 455674244909649089370689 341755683682236817028017)
                ·
                  refine ⟨256316762761677612771013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 341755683682236817028017 256316762761677612771013)
                  ·
                    refine ⟨48059393017814552394565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 256316762761677612771013 48059393017814552394565)
                    ·
                      rfl

theorem cell23_280786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_280786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280786 prefixEnd_280786 := by exact prefixLift 280786
  have htrace : WordTrace (prefixWord ++ tailWord_280786) baseStart_280786 baseEnd_280786 := by
    simpa [prefixWord, tailWord_280786, baseEnd_280786] using wordTrace_append hprefix tailTrace_280786
  have hstable : (prefixWord ++ tailWord_280786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280786).length < 2 ^ (prefixWord ++ tailWord_280786).sum := by decide
  have hdescent : baseEnd_280786 < baseStart_280786 := by decide
  rcases family_descends (prefixWord ++ tailWord_280786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280796 : List Nat := [2, 2, 5, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_280796 : Nat := 118140960795 + 280796 * 2 ^ 59
def prefixEnd_280796 : Nat := 4983230072969 + 3 ^ 40 * 280796 * 2
def baseEnd_280796 : Nat := 144183313859988618058649

theorem tailTrace_280796 : CollatzResearch.WordTrace tailWord_280796 prefixEnd_280796 144183313859988618058649 := by
  unfold tailWord_280796
  simp only [CollatzResearch.WordTrace]
  refine ⟨5120735745365761491963121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6827647660487681989284161 5120735745365761491963121)
  ·
    refine ⟨3840551809024321118972341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5120735745365761491963121 3840551809024321118972341)
    ·
      refine ⟨360051732096030104903657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3840551809024321118972341 360051732096030104903657)
      ·
        refine ⟨270038799072022578677743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 360051732096030104903657 270038799072022578677743)
        ·
          refine ⟨405058198608033868016615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270038799072022578677743 405058198608033868016615)
          ·
            refine ⟨607587297912050802024923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405058198608033868016615 607587297912050802024923)
            ·
              refine ⟨911380946868076203037385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 607587297912050802024923 911380946868076203037385)
              ·
                refine ⟨683535710151057152278039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 911380946868076203037385 683535710151057152278039)
                ·
                  refine ⟨1025303565226585728417059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 683535710151057152278039 1025303565226585728417059)
                  ·
                    refine ⟨1537955347839878592625589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1025303565226585728417059 1537955347839878592625589)
                    ·
                      refine ⟨144183313859988618058649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1537955347839878592625589 144183313859988618058649)
                      ·
                        rfl

theorem cell23_280796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_280796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280796 prefixEnd_280796 := by exact prefixLift 280796
  have htrace : WordTrace (prefixWord ++ tailWord_280796) baseStart_280796 baseEnd_280796 := by
    simpa [prefixWord, tailWord_280796, baseEnd_280796] using wordTrace_append hprefix tailTrace_280796
  have hstable : (prefixWord ++ tailWord_280796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280796).length < 2 ^ (prefixWord ++ tailWord_280796).sum := by decide
  have hdescent : baseEnd_280796 < baseStart_280796 := by decide
  rcases family_descends (prefixWord ++ tailWord_280796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280803 : List Nat := [1, 1, 1, 8, 1, 1, 3, 1, 2, 4]
def baseStart_280803 : Nat := 118140960795 + 280803 * 2 ^ 59
def prefixEnd_280803 : Nat := 4983230072969 + 3 ^ 40 * 280803 * 2
def baseEnd_280803 : Nat := 48062302741523363557039

theorem tailTrace_280803 : CollatzResearch.WordTrace tailWord_280803 prefixEnd_280803 48062302741523363557039 := by
  unfold tailWord_280803
  simp only [CollatzResearch.WordTrace]
  refine ⟨10241726801706163179431063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6827817867804108786287375 10241726801706163179431063)
  ·
    refine ⟨15362590202559244769146595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10241726801706163179431063 15362590202559244769146595)
    ·
      refine ⟨23043885303838867153719893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15362590202559244769146595 23043885303838867153719893)
      ·
        refine ⟨270045530904361724457655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 23043885303838867153719893 270045530904361724457655)
        ·
          refine ⟨405068296356542586686483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270045530904361724457655 405068296356542586686483)
          ·
            refine ⟨607602444534813880029725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405068296356542586686483 607602444534813880029725)
            ·
              refine ⟨227850916700555205011147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 607602444534813880029725 227850916700555205011147)
              ·
                refine ⟨341776375050832807516721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 227850916700555205011147 341776375050832807516721)
                ·
                  refine ⟨256332281288124605637541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 341776375050832807516721 256332281288124605637541)
                  ·
                    refine ⟨48062302741523363557039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 256332281288124605637541 48062302741523363557039)
                    ·
                      rfl

theorem cell23_280803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 2, 4].length) (baseStart_280803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280803 prefixEnd_280803 := by exact prefixLift 280803
  have htrace : WordTrace (prefixWord ++ tailWord_280803) baseStart_280803 baseEnd_280803 := by
    simpa [prefixWord, tailWord_280803, baseEnd_280803] using wordTrace_append hprefix tailTrace_280803
  have hstable : (prefixWord ++ tailWord_280803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280803).length < 2 ^ (prefixWord ++ tailWord_280803).sum := by decide
  have hdescent : baseEnd_280803 < baseStart_280803 := by decide
  rcases family_descends (prefixWord ++ tailWord_280803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280822 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5]
def baseStart_280822 : Nat := 118140960795 + 280822 * 2 ^ 59
def prefixEnd_280822 : Nat := 4983230072969 + 3 ^ 40 * 280822 * 2
def baseEnd_280822 : Nat := 144196664357005516333529

theorem tailTrace_280822 : CollatzResearch.WordTrace tailWord_280822 prefixEnd_280822 144196664357005516333529 := by
  unfold tailWord_280822
  simp only [CollatzResearch.WordTrace]
  refine ⟨640151236789833089023295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6828279859091552949581813 640151236789833089023295)
  ·
    refine ⟨960226855184749633534943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 640151236789833089023295 960226855184749633534943)
    ·
      refine ⟨1440340282777124450302415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 960226855184749633534943 1440340282777124450302415)
      ·
        refine ⟨2160510424165686675453623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1440340282777124450302415 2160510424165686675453623)
        ·
          refine ⟨3240765636248530013180435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2160510424165686675453623 3240765636248530013180435)
          ·
            refine ⟨4861148454372795019770653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3240765636248530013180435 4861148454372795019770653)
            ·
              refine ⟨1822930670389798132413995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4861148454372795019770653 1822930670389798132413995)
              ·
                refine ⟨2734396005584697198620993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1822930670389798132413995 2734396005584697198620993)
                ·
                  refine ⟨2050797004188522898965745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2734396005584697198620993 2050797004188522898965745)
                  ·
                    refine ⟨1538097753141392174224309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2050797004188522898965745 1538097753141392174224309)
                    ·
                      refine ⟨144196664357005516333529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1538097753141392174224309 144196664357005516333529)
                      ·
                        rfl

theorem cell23_280822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_280822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280822 prefixEnd_280822 := by exact prefixLift 280822
  have htrace : WordTrace (prefixWord ++ tailWord_280822) baseStart_280822 baseEnd_280822 := by
    simpa [prefixWord, tailWord_280822, baseEnd_280822] using wordTrace_append hprefix tailTrace_280822
  have hstable : (prefixWord ++ tailWord_280822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280822).length < 2 ^ (prefixWord ++ tailWord_280822).sum := by decide
  have hdescent : baseEnd_280822 < baseStart_280822 := by decide
  rcases family_descends (prefixWord ++ tailWord_280822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280825 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 4, 6]
def baseStart_280825 : Nat := 118140960795 + 280825 * 2 ^ 59
def prefixEnd_280825 : Nat := 4983230072969 + 3 ^ 40 * 280825 * 2
def baseEnd_280825 : Nat := 48066068266323001532005

theorem tailTrace_280825 : CollatzResearch.WordTrace tailWord_280825 prefixEnd_280825 48066068266323001532005 := by
  unfold tailWord_280825
  simp only [CollatzResearch.WordTrace]
  refine ⟨10242529207626460936731929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6828352805084307291154619 10242529207626460936731929)
  ·
    refine ⟨7681896905719845702548947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10242529207626460936731929 7681896905719845702548947)
    ·
      refine ⟨11522845358579768553823421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7681896905719845702548947 11522845358579768553823421)
      ·
        refine ⟨4321067009467413207683783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11522845358579768553823421 4321067009467413207683783)
        ·
          refine ⟨6481600514201119811525675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4321067009467413207683783 6481600514201119811525675)
          ·
            refine ⟨9722400771301679717288513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6481600514201119811525675 9722400771301679717288513)
            ·
              refine ⟨7291800578476259787966385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9722400771301679717288513 7291800578476259787966385)
              ·
                refine ⟨5468850433857194840974789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7291800578476259787966385 5468850433857194840974789)
                ·
                  refine ⟨1025409456348224032682773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5468850433857194840974789 1025409456348224032682773)
                  ·
                    refine ⟨48066068266323001532005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1025409456348224032682773 48066068266323001532005)
                    ·
                      rfl

theorem cell23_280825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 6].length) (baseStart_280825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280825 prefixEnd_280825 := by exact prefixLift 280825
  have htrace : WordTrace (prefixWord ++ tailWord_280825) baseStart_280825 baseEnd_280825 := by
    simpa [prefixWord, tailWord_280825, baseEnd_280825] using wordTrace_append hprefix tailTrace_280825
  have hstable : (prefixWord ++ tailWord_280825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280825).length < 2 ^ (prefixWord ++ tailWord_280825).sum := by decide
  have hdescent : baseEnd_280825 < baseStart_280825 := by decide
  rcases family_descends (prefixWord ++ tailWord_280825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280912 : List Nat := [2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 5]
def baseStart_280912 : Nat := 118140960795 + 280912 * 2 ^ 59
def prefixEnd_280912 : Nat := 4983230072969 + 3 ^ 40 * 280912 * 2
def baseEnd_280912 : Nat := 144242877615910164208115

theorem tailTrace_280912 : CollatzResearch.WordTrace tailWord_280912 prefixEnd_280912 144242877615910164208115 := by
  unfold tailWord_280912
  simp only [CollatzResearch.WordTrace]
  refine ⟨5122851179155637397574495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6830468238874183196765993 5122851179155637397574495)
  ·
    refine ⟨7684276768733456096361743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5122851179155637397574495 7684276768733456096361743)
    ·
      refine ⟨11526415153100184144542615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7684276768733456096361743 11526415153100184144542615)
      ·
        refine ⟨17289622729650276216813923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11526415153100184144542615 17289622729650276216813923)
        ·
          refine ⟨25934434094475414325220885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17289622729650276216813923 25934434094475414325220885)
          ·
            refine ⟨1215676598178535046494729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25934434094475414325220885 1215676598178535046494729)
            ·
              refine ⟨911757448633901284871047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1215676598178535046494729 911757448633901284871047)
              ·
                refine ⟨1367636172950851927306571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 911757448633901284871047 1367636172950851927306571)
                ·
                  refine ⟨2051454259426277890959857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1367636172950851927306571 2051454259426277890959857)
                  ·
                    refine ⟨1538590694569708418219893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2051454259426277890959857 1538590694569708418219893)
                    ·
                      refine ⟨144242877615910164208115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1538590694569708418219893 144242877615910164208115)
                      ·
                        rfl

theorem cell23_280912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 5].length) (baseStart_280912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280912 prefixEnd_280912 := by exact prefixLift 280912
  have htrace : WordTrace (prefixWord ++ tailWord_280912) baseStart_280912 baseEnd_280912 := by
    simpa [prefixWord, tailWord_280912, baseEnd_280912] using wordTrace_append hprefix tailTrace_280912
  have hstable : (prefixWord ++ tailWord_280912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280912).length < 2 ^ (prefixWord ++ tailWord_280912).sum := by decide
  have hdescent : baseEnd_280912 < baseStart_280912 := by decide
  rcases family_descends (prefixWord ++ tailWord_280912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280922 : List Nat := [3, 1, 1, 2, 1, 2, 1, 4, 1, 3, 4]
def baseStart_280922 : Nat := 118140960795 + 280922 * 2 ^ 59
def prefixEnd_280922 : Nat := 4983230072969 + 3 ^ 40 * 280922 * 2
def baseEnd_280922 : Nat := 144248012422455125083069

theorem tailTrace_280922 : CollatzResearch.WordTrace tailWord_280922 prefixEnd_280922 144248012422455125083069 := by
  unfold tailWord_280922
  simp only [CollatzResearch.WordTrace]
  refine ⟨2561516772068761625753255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6830711392183364335342013 2561516772068761625753255)
  ·
    refine ⟨3842275158103142438629883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2561516772068761625753255 3842275158103142438629883)
    ·
      refine ⟨5763412737154713657944825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3842275158103142438629883 5763412737154713657944825)
      ·
        refine ⟨4322559552866035243458619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5763412737154713657944825 4322559552866035243458619)
        ·
          refine ⟨6483839329299052865187929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4322559552866035243458619 6483839329299052865187929)
          ·
            refine ⟨4862879496974289648890947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6483839329299052865187929 4862879496974289648890947)
            ·
              refine ⟨7294319245461434473336421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4862879496974289648890947 7294319245461434473336421)
              ·
                refine ⟨1367684858524018963750579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7294319245461434473336421 1367684858524018963750579)
                ·
                  refine ⟨2051527287786028445625869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1367684858524018963750579 2051527287786028445625869)
                  ·
                    refine ⟨769322732919760667109701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2051527287786028445625869 769322732919760667109701)
                    ·
                      refine ⟨144248012422455125083069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 769322732919760667109701 144248012422455125083069)
                      ·
                        rfl

theorem cell23_280922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_280922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280922 prefixEnd_280922 := by exact prefixLift 280922
  have htrace : WordTrace (prefixWord ++ tailWord_280922) baseStart_280922 baseEnd_280922 := by
    simpa [prefixWord, tailWord_280922, baseEnd_280922] using wordTrace_append hprefix tailTrace_280922
  have hstable : (prefixWord ++ tailWord_280922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280922).length < 2 ^ (prefixWord ++ tailWord_280922).sum := by decide
  have hdescent : baseEnd_280922 < baseStart_280922 := by decide
  rcases family_descends (prefixWord ++ tailWord_280922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280936 : List Nat := [2, 1, 4, 2, 2, 3, 1, 1, 2, 5]
def baseStart_280936 : Nat := 118140960795 + 280936 * 2 ^ 59
def prefixEnd_280936 : Nat := 4983230072969 + 3 ^ 40 * 280936 * 2
def baseEnd_280936 : Nat := 48085067050539356769335

theorem tailTrace_280936 : CollatzResearch.WordTrace tailWord_280936 prefixEnd_280936 48085067050539356769335 := by
  unfold tailWord_280936
  simp only [CollatzResearch.WordTrace]
  refine ⟨5123288855112163447011331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6831051806816217929348441 5123288855112163447011331)
  ·
    refine ⟨7684933282668245170516997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5123288855112163447011331 7684933282668245170516997)
    ·
      refine ⟨1440924990500295969471937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7684933282668245170516997 1440924990500295969471937)
      ·
        refine ⟨1080693742875221977103953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1440924990500295969471937 1080693742875221977103953)
        ·
          refine ⟨810520307156416482827965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1080693742875221977103953 810520307156416482827965)
          ·
            refine ⟨303945115183656181060487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 810520307156416482827965 303945115183656181060487)
            ·
              refine ⟨455917672775484271590731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303945115183656181060487 455917672775484271590731)
              ·
                refine ⟨683876509163226407386097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 455917672775484271590731 683876509163226407386097)
                ·
                  refine ⟨512907381872419805539573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 683876509163226407386097 512907381872419805539573)
                  ·
                    refine ⟨48085067050539356769335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 512907381872419805539573 48085067050539356769335)
                    ·
                      rfl

theorem cell23_280936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_280936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_280936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_280936 prefixEnd_280936 := by exact prefixLift 280936
  have htrace : WordTrace (prefixWord ++ tailWord_280936) baseStart_280936 baseEnd_280936 := by
    simpa [prefixWord, tailWord_280936, baseEnd_280936] using wordTrace_append hprefix tailTrace_280936
  have hstable : (prefixWord ++ tailWord_280936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280936).length < 2 ^ (prefixWord ++ tailWord_280936).sum := by decide
  have hdescent : baseEnd_280936 < baseStart_280936 := by decide
  rcases family_descends (prefixWord ++ tailWord_280936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281000 : List Nat := [2, 1, 6, 1, 1, 1, 3, 3, 1, 4]
def baseStart_281000 : Nat := 118140960795 + 281000 * 2 ^ 59
def prefixEnd_281000 : Nat := 4983230072969 + 3 ^ 40 * 281000 * 2
def baseEnd_281000 : Nat := 48096021304501939969237

theorem tailTrace_281000 : CollatzResearch.WordTrace tailWord_281000 prefixEnd_281000 48096021304501939969237 := by
  unfold tailWord_281000
  simp only [CollatzResearch.WordTrace]
  refine ⟨5124455990996232912176227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6832607987994977216234969 5124455990996232912176227)
  ·
    refine ⟨7686683986494349368264341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5124455990996232912176227 7686683986494349368264341)
    ·
      refine ⟨360313311866922626637391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7686683986494349368264341 360313311866922626637391)
      ·
        refine ⟨540469967800383939956087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360313311866922626637391 540469967800383939956087)
        ·
          refine ⟨810704951700575909934131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 540469967800383939956087 810704951700575909934131)
          ·
            refine ⟨1216057427550863864901197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 810704951700575909934131 1216057427550863864901197)
            ·
              refine ⟨456021535331573949337949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1216057427550863864901197 456021535331573949337949)
              ·
                refine ⟨171008075749340231001731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 456021535331573949337949 171008075749340231001731)
                ·
                  refine ⟨256512113624010346502597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171008075749340231001731 256512113624010346502597)
                  ·
                    refine ⟨48096021304501939969237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 256512113624010346502597 48096021304501939969237)
                    ·
                      rfl

theorem cell23_281000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_281000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281000 prefixEnd_281000 := by exact prefixLift 281000
  have htrace : WordTrace (prefixWord ++ tailWord_281000) baseStart_281000 baseEnd_281000 := by
    simpa [prefixWord, tailWord_281000, baseEnd_281000] using wordTrace_append hprefix tailTrace_281000
  have hstable : (prefixWord ++ tailWord_281000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281000).length < 2 ^ (prefixWord ++ tailWord_281000).sum := by decide
  have hdescent : baseEnd_281000 < baseStart_281000 := by decide
  rcases family_descends (prefixWord ++ tailWord_281000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281063 : List Nat := [1, 1, 5, 2, 1, 1, 5, 1, 1, 1, 4]
def baseStart_281063 : Nat := 118140960795 + 281063 * 2 ^ 59
def prefixEnd_281063 : Nat := 4983230072969 + 3 ^ 40 * 281063 * 2
def baseEnd_281063 : Nat := 144320413194739073419921

theorem tailTrace_281063 : CollatzResearch.WordTrace tailWord_281063 prefixEnd_281063 144320413194739073419921 := by
  unfold tailWord_281063
  simp only [CollatzResearch.WordTrace]
  refine ⟨10251209780764227583895843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6834139853842818389263895 10251209780764227583895843)
  ·
    refine ⟨15376814671146341375843765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10251209780764227583895843 15376814671146341375843765)
    ·
      refine ⟨1441576375419969503985353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15376814671146341375843765 1441576375419969503985353)
      ·
        refine ⟨1081182281564977127989015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1441576375419969503985353 1081182281564977127989015)
        ·
          refine ⟨1621773422347465691983523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1081182281564977127989015 1621773422347465691983523)
          ·
            refine ⟨2432660133521198537975285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1621773422347465691983523 2432660133521198537975285)
            ·
              refine ⟨228061887517612362935183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2432660133521198537975285 228061887517612362935183)
              ·
                refine ⟨342092831276418544402775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 228061887517612362935183 342092831276418544402775)
                ·
                  refine ⟨513139246914627816604163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 342092831276418544402775 513139246914627816604163)
                  ·
                    refine ⟨769708870371941724906245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 513139246914627816604163 769708870371941724906245)
                    ·
                      refine ⟨144320413194739073419921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 769708870371941724906245 144320413194739073419921)
                      ·
                        rfl

theorem cell23_281063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_281063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281063 prefixEnd_281063 := by exact prefixLift 281063
  have htrace : WordTrace (prefixWord ++ tailWord_281063) baseStart_281063 baseEnd_281063 := by
    simpa [prefixWord, tailWord_281063, baseEnd_281063] using wordTrace_append hprefix tailTrace_281063
  have hstable : (prefixWord ++ tailWord_281063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281063).length < 2 ^ (prefixWord ++ tailWord_281063).sum := by decide
  have hdescent : baseEnd_281063 < baseStart_281063 := by decide
  rcases family_descends (prefixWord ++ tailWord_281063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281066 : List Nat := [3, 1, 3, 1, 3, 1, 3, 1, 1, 1, 5]
def baseStart_281066 : Nat := 118140960795 + 281066 * 2 ^ 59
def prefixEnd_281066 : Nat := 4983230072969 + 3 ^ 40 * 281066 * 2
def baseEnd_281066 : Nat := 144321953636702561682407

theorem tailTrace_281066 : CollatzResearch.WordTrace tailWord_281066 prefixEnd_281066 144321953636702561682407 := by
  unfold tailWord_281066
  simp only [CollatzResearch.WordTrace]
  refine ⟨2562829799938339774063763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6834212799835572730836701 2562829799938339774063763)
  ·
    refine ⟨3844244699907509661095645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2562829799938339774063763 3844244699907509661095645)
    ·
      refine ⟨1441591762465316122910867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3844244699907509661095645 1441591762465316122910867)
      ·
        refine ⟨2162387643697974184366301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1441591762465316122910867 2162387643697974184366301)
        ·
          refine ⟨810895366386740319137363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2162387643697974184366301 810895366386740319137363)
          ·
            refine ⟨1216343049580110478706045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 810895366386740319137363 1216343049580110478706045)
            ·
              refine ⟨456128643592541429514767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1216343049580110478706045 456128643592541429514767)
              ·
                refine ⟨684192965388812144272151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 456128643592541429514767 684192965388812144272151)
                ·
                  refine ⟨1026289448083218216408227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 684192965388812144272151 1026289448083218216408227)
                  ·
                    refine ⟨1539434172124827324612341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1026289448083218216408227 1539434172124827324612341)
                    ·
                      refine ⟨144321953636702561682407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1539434172124827324612341 144321953636702561682407)
                      ·
                        rfl

theorem cell23_281066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_281066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281066 prefixEnd_281066 := by exact prefixLift 281066
  have htrace : WordTrace (prefixWord ++ tailWord_281066) baseStart_281066 baseEnd_281066 := by
    simpa [prefixWord, tailWord_281066, baseEnd_281066] using wordTrace_append hprefix tailTrace_281066
  have hstable : (prefixWord ++ tailWord_281066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281066).length < 2 ^ (prefixWord ++ tailWord_281066).sum := by decide
  have hdescent : baseEnd_281066 < baseStart_281066 := by decide
  rcases family_descends (prefixWord ++ tailWord_281066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281069 : List Nat := [1, 5, 1, 3, 1, 12]
def baseStart_281069 : Nat := 118140960795 + 281069 * 2 ^ 59
def prefixEnd_281069 : Nat := 4983230072969 + 3 ^ 40 * 281069 * 2
def baseEnd_281069 : Nat := 593923843945127777551

theorem tailTrace_281069 : CollatzResearch.WordTrace tailWord_281069 prefixEnd_281069 593923843945127777551 := by
  unfold tailWord_281069
  simp only [CollatzResearch.WordTrace]
  refine ⟨10251428618742490608614261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6834285745828327072409507 10251428618742490608614261)
  ·
    refine ⟨961071433007108494557587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10251428618742490608614261 961071433007108494557587)
    ·
      refine ⟨1441607149510662741836381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 961071433007108494557587 1441607149510662741836381)
      ·
        refine ⟨540602681066498528188643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1441607149510662741836381 540602681066498528188643)
        ·
          refine ⟨810904021599747792282965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 540602681066498528188643 810904021599747792282965)
          ·
            refine ⟨593923843945127777551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 810904021599747792282965 593923843945127777551)
            ·
              rfl

theorem cell23_281069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 12].length) (baseStart_281069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281069 prefixEnd_281069 := by exact prefixLift 281069
  have htrace : WordTrace (prefixWord ++ tailWord_281069) baseStart_281069 baseEnd_281069 := by
    simpa [prefixWord, tailWord_281069, baseEnd_281069] using wordTrace_append hprefix tailTrace_281069
  have hstable : (prefixWord ++ tailWord_281069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281069).length < 2 ^ (prefixWord ++ tailWord_281069).sum := by decide
  have hdescent : baseEnd_281069 < baseStart_281069 := by decide
  rcases family_descends (prefixWord ++ tailWord_281069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281074 : List Nat := [3, 2, 1, 4, 2, 2, 2, 2, 1, 1, 3]
def baseStart_281074 : Nat := 118140960795 + 281074 * 2 ^ 59
def prefixEnd_281074 : Nat := 4983230072969 + 3 ^ 40 * 281074 * 2
def baseEnd_281074 : Nat := 144326061481938530382371

theorem tailTrace_281074 : CollatzResearch.WordTrace tailWord_281074 prefixEnd_281074 144326061481938530382371 := by
  unfold tailWord_281074
  simp only [CollatzResearch.WordTrace]
  refine ⟨2562902745931094115636569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6834407322482917641697517 2562902745931094115636569)
  ·
    refine ⟨1922177059448320586727427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2562902745931094115636569 1922177059448320586727427)
    ·
      refine ⟨2883265589172480880091141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1922177059448320586727427 2883265589172480880091141)
      ·
        refine ⟨540612297969840165017089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2883265589172480880091141 540612297969840165017089)
        ·
          refine ⟨405459223477380123762817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 540612297969840165017089 405459223477380123762817)
          ·
            refine ⟨304094417608035092822113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 405459223477380123762817 304094417608035092822113)
            ·
              refine ⟨228070813206026319616585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304094417608035092822113 228070813206026319616585)
              ·
                refine ⟨171053109904519739712439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 228070813206026319616585 171053109904519739712439)
                ·
                  refine ⟨256579664856779609568659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171053109904519739712439 256579664856779609568659)
                  ·
                    refine ⟨384869497285169414352989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 256579664856779609568659 384869497285169414352989)
                    ·
                      refine ⟨144326061481938530382371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 384869497285169414352989 144326061481938530382371)
                      ·
                        rfl

theorem cell23_281074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_281074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281074 prefixEnd_281074 := by exact prefixLift 281074
  have htrace : WordTrace (prefixWord ++ tailWord_281074) baseStart_281074 baseEnd_281074 := by
    simpa [prefixWord, tailWord_281074, baseEnd_281074] using wordTrace_append hprefix tailTrace_281074
  have hstable : (prefixWord ++ tailWord_281074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281074).length < 2 ^ (prefixWord ++ tailWord_281074).sum := by decide
  have hdescent : baseEnd_281074 < baseStart_281074 := by decide
  rcases family_descends (prefixWord ++ tailWord_281074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281080 : List Nat := [2, 1, 2, 1, 1, 4, 3, 4, 1, 2, 2]
def baseStart_281080 : Nat := 118140960795 + 281080 * 2 ^ 59
def prefixEnd_281080 : Nat := 4983230072969 + 3 ^ 40 * 281080 * 2
def baseEnd_281080 : Nat := 144329142365865506907343

theorem tailTrace_281080 : CollatzResearch.WordTrace tailWord_281080 prefixEnd_281080 144329142365865506907343 := by
  unfold tailWord_281080
  simp only [CollatzResearch.WordTrace]
  refine ⟨5125914910851319743632347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6834553214468426324843129 5125914910851319743632347)
  ·
    refine ⟨7688872366276979615448521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5125914910851319743632347 7688872366276979615448521)
    ·
      refine ⟨5766654274707734711586391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7688872366276979615448521 5766654274707734711586391)
      ·
        refine ⟨8649981412061602067379587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5766654274707734711586391 8649981412061602067379587)
        ·
          refine ⟨12974972118092403101069381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8649981412061602067379587 12974972118092403101069381)
          ·
            refine ⟨2432807272142325581450509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12974972118092403101069381 2432807272142325581450509)
            ·
              refine ⟨912302727053372093043941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2432807272142325581450509 912302727053372093043941)
              ·
                refine ⟨171056761322507267445739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 912302727053372093043941 171056761322507267445739)
                ·
                  refine ⟨256585141983760901168609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171056761322507267445739 256585141983760901168609)
                  ·
                    refine ⟨192438856487820675876457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 256585141983760901168609 192438856487820675876457)
                    ·
                      refine ⟨144329142365865506907343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 192438856487820675876457 144329142365865506907343)
                      ·
                        rfl

theorem cell23_281080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 4, 1, 2, 2].length) (baseStart_281080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281080 prefixEnd_281080 := by exact prefixLift 281080
  have htrace : WordTrace (prefixWord ++ tailWord_281080) baseStart_281080 baseEnd_281080 := by
    simpa [prefixWord, tailWord_281080, baseEnd_281080] using wordTrace_append hprefix tailTrace_281080
  have hstable : (prefixWord ++ tailWord_281080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281080).length < 2 ^ (prefixWord ++ tailWord_281080).sum := by decide
  have hdescent : baseEnd_281080 < baseStart_281080 := by decide
  rcases family_descends (prefixWord ++ tailWord_281080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281096 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 6, 1, 3]
def baseStart_281096 : Nat := 118140960795 + 281096 * 2 ^ 59
def prefixEnd_281096 : Nat := 4983230072969 + 3 ^ 40 * 281096 * 2
def baseEnd_281096 : Nat := 144337358056337444307269

theorem tailTrace_281096 : CollatzResearch.WordTrace tailWord_281096 prefixEnd_281096 144337358056337444307269 := by
  unfold tailWord_281096
  simp only [CollatzResearch.WordTrace]
  refine ⟨5126206694822337109923571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6834942259763116146564761 5126206694822337109923571)
  ·
    refine ⟨7689310042233505664885357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5126206694822337109923571 7689310042233505664885357)
    ·
      refine ⟨2883491265837564624332009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7689310042233505664885357 2883491265837564624332009)
      ·
        refine ⟨2162618449378173468249007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2883491265837564624332009 2162618449378173468249007)
        ·
          refine ⟨3243927674067260202373511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2162618449378173468249007 3243927674067260202373511)
          ·
            refine ⟨4865891511100890303560267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3243927674067260202373511 4865891511100890303560267)
            ·
              refine ⟨7298837266651335455340401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4865891511100890303560267 7298837266651335455340401)
              ·
                refine ⟨5474127949988501591505301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7298837266651335455340401 5474127949988501591505301)
                ·
                  refine ⟨256599747655711012101811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5474127949988501591505301 256599747655711012101811)
                  ·
                    refine ⟨384899621483566518152717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 256599747655711012101811 384899621483566518152717)
                    ·
                      refine ⟨144337358056337444307269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 384899621483566518152717 144337358056337444307269)
                      ·
                        rfl

theorem cell23_281096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_281096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281096 prefixEnd_281096 := by exact prefixLift 281096
  have htrace : WordTrace (prefixWord ++ tailWord_281096) baseStart_281096 baseEnd_281096 := by
    simpa [prefixWord, tailWord_281096, baseEnd_281096] using wordTrace_append hprefix tailTrace_281096
  have hstable : (prefixWord ++ tailWord_281096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281096).length < 2 ^ (prefixWord ++ tailWord_281096).sum := by decide
  have hdescent : baseEnd_281096 < baseStart_281096 := by decide
  rcases family_descends (prefixWord ++ tailWord_281096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281109 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 2, 2, 5]
def baseStart_281109 : Nat := 118140960795 + 281109 * 2 ^ 59
def prefixEnd_281109 : Nat := 4983230072969 + 3 ^ 40 * 281109 * 2
def baseEnd_281109 : Nat := 144344033304845893444709

theorem tailTrace_281109 : CollatzResearch.WordTrace tailWord_281109 prefixEnd_281109 144344033304845893444709 := by
  unfold tailWord_281109
  simp only [CollatzResearch.WordTrace]
  refine ⟨10252887538597577440070381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6835258359065051626713587 10252887538597577440070381)
  ·
    refine ⟨3844832826974091540026393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10252887538597577440070381 3844832826974091540026393)
    ·
      refine ⟨2883624620230568655019795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3844832826974091540026393 2883624620230568655019795)
      ·
        refine ⟨4325436930345852982529693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2883624620230568655019795 4325436930345852982529693)
        ·
          refine ⟨1622038848879694868448635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4325436930345852982529693 1622038848879694868448635)
          ·
            refine ⟨2433058273319542302672953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1622038848879694868448635 2433058273319542302672953)
            ·
              refine ⟨1824793704989656727004715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2433058273319542302672953 1824793704989656727004715)
              ·
                refine ⟨2737190557484485090507073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1824793704989656727004715 2737190557484485090507073)
                ·
                  refine ⟨2052892918113363817880305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2737190557484485090507073 2052892918113363817880305)
                  ·
                    refine ⟨1539669688585022863410229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2052892918113363817880305 1539669688585022863410229)
                    ·
                      refine ⟨144344033304845893444709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1539669688585022863410229 144344033304845893444709)
                      ·
                        rfl

theorem cell23_281109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_281109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281109 prefixEnd_281109 := by exact prefixLift 281109
  have htrace : WordTrace (prefixWord ++ tailWord_281109) baseStart_281109 baseEnd_281109 := by
    simpa [prefixWord, tailWord_281109, baseEnd_281109] using wordTrace_append hprefix tailTrace_281109
  have hstable : (prefixWord ++ tailWord_281109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281109).length < 2 ^ (prefixWord ++ tailWord_281109).sum := by decide
  have hdescent : baseEnd_281109 < baseStart_281109 := by decide
  rcases family_descends (prefixWord ++ tailWord_281109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281130 : List Nat := [3, 1, 4, 1, 1, 2, 3, 2, 2, 1, 3]
def baseStart_281130 : Nat := 118140960795 + 281130 * 2 ^ 59
def prefixEnd_281130 : Nat := 4983230072969 + 3 ^ 40 * 281130 * 2
def baseEnd_281130 : Nat := 144354816398590311282113

theorem tailTrace_281130 : CollatzResearch.WordTrace tailWord_281130 prefixEnd_281130 144354816398590311282113 := by
  unfold tailWord_281130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2563413367880374506646211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6835768981014332017723229 2563413367880374506646211)
  ·
    refine ⟨3845120051820561759969317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2563413367880374506646211 3845120051820561759969317)
    ·
      refine ⟨720960009716355329994247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3845120051820561759969317 720960009716355329994247)
      ·
        refine ⟨1081440014574532994991371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 720960009716355329994247 1081440014574532994991371)
        ·
          refine ⟨1622160021861799492487057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1081440014574532994991371 1622160021861799492487057)
          ·
            refine ⟨1216620016396349619365293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1622160021861799492487057 1216620016396349619365293)
            ·
              refine ⟨456232506148631107261985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1216620016396349619365293 456232506148631107261985)
              ·
                refine ⟨342174379611473330446489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 456232506148631107261985 342174379611473330446489)
                ·
                  refine ⟨256630784708604997834867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 342174379611473330446489 256630784708604997834867)
                  ·
                    refine ⟨384946177062907496752301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 256630784708604997834867 384946177062907496752301)
                    ·
                      refine ⟨144354816398590311282113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 384946177062907496752301 144354816398590311282113)
                      ·
                        rfl

theorem cell23_281130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_281130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281130 prefixEnd_281130 := by exact prefixLift 281130
  have htrace : WordTrace (prefixWord ++ tailWord_281130) baseStart_281130 baseEnd_281130 := by
    simpa [prefixWord, tailWord_281130, baseEnd_281130] using wordTrace_append hprefix tailTrace_281130
  have hstable : (prefixWord ++ tailWord_281130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281130).length < 2 ^ (prefixWord ++ tailWord_281130).sum := by decide
  have hdescent : baseEnd_281130 < baseStart_281130 := by decide
  rcases family_descends (prefixWord ++ tailWord_281130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281136 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 3, 4, 2]
def baseStart_281136 : Nat := 118140960795 + 281136 * 2 ^ 59
def prefixEnd_281136 : Nat := 4983230072969 + 3 ^ 40 * 281136 * 2
def baseEnd_281136 : Nat := 144357897282517287807085

theorem tailTrace_281136 : CollatzResearch.WordTrace tailWord_281136 prefixEnd_281136 144357897282517287807085 := by
  unfold tailWord_281136
  simp only [CollatzResearch.WordTrace]
  refine ⟨5126936154749880525651631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6835914872999840700868841 5126936154749880525651631)
  ·
    refine ⟨7690404232124820788477447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5126936154749880525651631 7690404232124820788477447)
    ·
      refine ⟨11535606348187231182716171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7690404232124820788477447 11535606348187231182716171)
      ·
        refine ⟨17303409522280846774074257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11535606348187231182716171 17303409522280846774074257)
        ·
          refine ⟨12977557141710635080555693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17303409522280846774074257 12977557141710635080555693)
          ·
            refine ⟨4866583928141488155208385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12977557141710635080555693 4866583928141488155208385)
            ·
              refine ⟨3649937946106116116406289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4866583928141488155208385 3649937946106116116406289)
              ·
                refine ⟨2737453459579587087304717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3649937946106116116406289 2737453459579587087304717)
                ·
                  refine ⟨1026545047342345157739269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2737453459579587087304717 1026545047342345157739269)
                  ·
                    refine ⟨192477196376689717076113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1026545047342345157739269 192477196376689717076113)
                    ·
                      refine ⟨144357897282517287807085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 192477196376689717076113 144357897282517287807085)
                      ·
                        rfl

theorem cell23_281136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 3, 4, 2].length) (baseStart_281136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281136 prefixEnd_281136 := by exact prefixLift 281136
  have htrace : WordTrace (prefixWord ++ tailWord_281136) baseStart_281136 baseEnd_281136 := by
    simpa [prefixWord, tailWord_281136, baseEnd_281136] using wordTrace_append hprefix tailTrace_281136
  have hstable : (prefixWord ++ tailWord_281136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281136).length < 2 ^ (prefixWord ++ tailWord_281136).sum := by decide
  have hdescent : baseEnd_281136 < baseStart_281136 := by decide
  rcases family_descends (prefixWord ++ tailWord_281136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281199 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 7]
def baseStart_281199 : Nat := 118140960795 + 281199 * 2 ^ 59
def prefixEnd_281199 : Nat := 4983230072969 + 3 ^ 40 * 281199 * 2
def baseEnd_281199 : Nat := 144390246563750541319295

theorem tailTrace_281199 : CollatzResearch.WordTrace tailWord_281199 prefixEnd_281199 144390246563750541319295 := by
  unfold tailWord_281199
  simp only [CollatzResearch.WordTrace]
  refine ⟨10256170108271522810846651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6837446738847681873897767 10256170108271522810846651)
  ·
    refine ⟨15384255162407284216269977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10256170108271522810846651 15384255162407284216269977)
    ·
      refine ⟨11538191371805463162202483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15384255162407284216269977 11538191371805463162202483)
      ·
        refine ⟨17307287057708194743303725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11538191371805463162202483 17307287057708194743303725)
        ·
          refine ⟨6490232646640573028738897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17307287057708194743303725 6490232646640573028738897)
          ·
            refine ⟨4867674484980429771554173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6490232646640573028738897 4867674484980429771554173)
            ·
              refine ⟨1825377931867661164332815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4867674484980429771554173 1825377931867661164332815)
              ·
                refine ⟨2738066897801491746499223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1825377931867661164332815 2738066897801491746499223)
                ·
                  refine ⟨4107100346702237619748835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2738066897801491746499223 4107100346702237619748835)
                  ·
                    refine ⟨6160650520053356429623253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4107100346702237619748835 6160650520053356429623253)
                    ·
                      refine ⟨144390246563750541319295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6160650520053356429623253 144390246563750541319295)
                      ·
                        rfl

theorem cell23_281199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 7].length) (baseStart_281199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281199 prefixEnd_281199 := by exact prefixLift 281199
  have htrace : WordTrace (prefixWord ++ tailWord_281199) baseStart_281199 baseEnd_281199 := by
    simpa [prefixWord, tailWord_281199, baseEnd_281199] using wordTrace_append hprefix tailTrace_281199
  have hstable : (prefixWord ++ tailWord_281199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281199).length < 2 ^ (prefixWord ++ tailWord_281199).sum := by decide
  have hdescent : baseEnd_281199 < baseStart_281199 := by decide
  rcases family_descends (prefixWord ++ tailWord_281199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281219 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 2, 8]
def baseStart_281219 : Nat := 118140960795 + 281219 * 2 ^ 59
def prefixEnd_281219 : Nat := 4983230072969 + 3 ^ 40 * 281219 * 2
def baseEnd_281219 : Nat := 48133505392280154356401

theorem tailTrace_281219 : CollatzResearch.WordTrace tailWord_281219 prefixEnd_281219 48133505392280154356401 := by
  unfold tailWord_281219
  simp only [CollatzResearch.WordTrace]
  refine ⟨10256899568199066226574711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6837933045466044151049807 10256899568199066226574711)
  ·
    refine ⟨15385349352298599339862067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10256899568199066226574711 15385349352298599339862067)
    ·
      refine ⟨23078024028447899009793101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15385349352298599339862067 23078024028447899009793101)
      ·
        refine ⟨8654259010667962128672413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23078024028447899009793101 8654259010667962128672413)
        ·
          refine ⟨3245347129000485798252155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8654259010667962128672413 3245347129000485798252155)
          ·
            refine ⟨4868020693500728697378233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3245347129000485798252155 4868020693500728697378233)
            ·
              refine ⟨3651015520125546523033675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4868020693500728697378233 3651015520125546523033675)
              ·
                refine ⟨5476523280188319784550513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3651015520125546523033675 5476523280188319784550513)
                ·
                  refine ⟨4107392460141239838412885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5476523280188319784550513 4107392460141239838412885)
                  ·
                    refine ⟨48133505392280154356401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4107392460141239838412885 48133505392280154356401)
                    ·
                      rfl

theorem cell23_281219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 8].length) (baseStart_281219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281219 prefixEnd_281219 := by exact prefixLift 281219
  have htrace : WordTrace (prefixWord ++ tailWord_281219) baseStart_281219 baseEnd_281219 := by
    simpa [prefixWord, tailWord_281219, baseEnd_281219] using wordTrace_append hprefix tailTrace_281219
  have hstable : (prefixWord ++ tailWord_281219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281219).length < 2 ^ (prefixWord ++ tailWord_281219).sum := by decide
  have hdescent : baseEnd_281219 < baseStart_281219 := by decide
  rcases family_descends (prefixWord ++ tailWord_281219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281280 : List Nat := [2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 3]
def baseStart_281280 : Nat := 118140960795 + 281280 * 2 ^ 59
def prefixEnd_281280 : Nat := 4983230072969 + 3 ^ 40 * 281280 * 2
def baseEnd_281280 : Nat := 144431838496764724406423

theorem tailTrace_281280 : CollatzResearch.WordTrace tailWord_281280 prefixEnd_281280 144431838496764724406423 := by
  unfold tailWord_281280
  simp only [CollatzResearch.WordTrace]
  refine ⟨5129562210489036822272647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6839416280652049096363529 5129562210489036822272647)
  ·
    refine ⟨7694343315733555233408971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5129562210489036822272647 7694343315733555233408971)
    ·
      refine ⟨11541514973600332850113457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7694343315733555233408971 11541514973600332850113457)
      ·
        refine ⟨8656136230200249637585093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11541514973600332850113457 8656136230200249637585093)
        ·
          refine ⟨1623025543162546807047205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8656136230200249637585093 1623025543162546807047205)
          ·
            refine ⟨304317289342977526321351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1623025543162546807047205 304317289342977526321351)
            ·
              refine ⟨456475934014466289482027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304317289342977526321351 456475934014466289482027)
              ·
                refine ⟨684713901021699434223041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 456475934014466289482027 684713901021699434223041)
                ·
                  refine ⟨513535425766274575667281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 684713901021699434223041 513535425766274575667281)
                  ·
                    refine ⟨385151569324705931750461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 513535425766274575667281 385151569324705931750461)
                    ·
                      refine ⟨144431838496764724406423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 385151569324705931750461 144431838496764724406423)
                      ·
                        rfl

theorem cell23_281280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 3].length) (baseStart_281280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281280 prefixEnd_281280 := by exact prefixLift 281280
  have htrace : WordTrace (prefixWord ++ tailWord_281280) baseStart_281280 baseEnd_281280 := by
    simpa [prefixWord, tailWord_281280, baseEnd_281280] using wordTrace_append hprefix tailTrace_281280
  have hstable : (prefixWord ++ tailWord_281280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281280).length < 2 ^ (prefixWord ++ tailWord_281280).sum := by decide
  have hdescent : baseEnd_281280 < baseStart_281280 := by decide
  rcases family_descends (prefixWord ++ tailWord_281280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281330 : List Nat := [3, 2, 1, 3, 1, 3, 2, 2, 1, 5]
def baseStart_281330 : Nat := 118140960795 + 281330 * 2 ^ 59
def prefixEnd_281330 : Nat := 4983230072969 + 3 ^ 40 * 281330 * 2
def baseEnd_281330 : Nat := 48152504176496509593731

theorem tailTrace_281330 : CollatzResearch.WordTrace tailWord_281330 prefixEnd_281330 48152504176496509593731 := by
  unfold tailWord_281330
  simp only [CollatzResearch.WordTrace]
  refine ⟨2565237017699233045966361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6840632047197954789243629 2565237017699233045966361)
  ·
    refine ⟨1923927763274424784474771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2565237017699233045966361 1923927763274424784474771)
    ·
      refine ⟨2885891644911637176712157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1923927763274424784474771 2885891644911637176712157)
      ·
        refine ⟨1082209366841863941267059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2885891644911637176712157 1082209366841863941267059)
        ·
          refine ⟨1623314050262795911900589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1082209366841863941267059 1623314050262795911900589)
          ·
            refine ⟨608742768848548466962721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1623314050262795911900589 608742768848548466962721)
            ·
              refine ⟨456557076636411350222041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 608742768848548466962721 456557076636411350222041)
              ·
                refine ⟨342417807477308512666531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 456557076636411350222041 342417807477308512666531)
                ·
                  refine ⟨513626711215962768999797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 342417807477308512666531 513626711215962768999797)
                  ·
                    refine ⟨48152504176496509593731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 513626711215962768999797 48152504176496509593731)
                    ·
                      rfl

theorem cell23_281330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_281330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281330 prefixEnd_281330 := by exact prefixLift 281330
  have htrace : WordTrace (prefixWord ++ tailWord_281330) baseStart_281330 baseEnd_281330 := by
    simpa [prefixWord, tailWord_281330, baseEnd_281330] using wordTrace_append hprefix tailTrace_281330
  have hstable : (prefixWord ++ tailWord_281330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281330).length < 2 ^ (prefixWord ++ tailWord_281330).sum := by decide
  have hdescent : baseEnd_281330 < baseStart_281330 := by decide
  rcases family_descends (prefixWord ++ tailWord_281330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281336 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 3, 1, 5]
def baseStart_281336 : Nat := 118140960795 + 281336 * 2 ^ 59
def prefixEnd_281336 : Nat := 4983230072969 + 3 ^ 40 * 281336 * 2
def baseEnd_281336 : Nat := 144460593413416505306165

theorem tailTrace_281336 : CollatzResearch.WordTrace tailWord_281336 prefixEnd_281336 144460593413416505306165 := by
  unfold tailWord_281336
  simp only [CollatzResearch.WordTrace]
  refine ⟨5130583454387597604291931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6840777939183463472389241 5130583454387597604291931)
  ·
    refine ⟨7695875181581396406437897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5130583454387597604291931 7695875181581396406437897)
    ·
      refine ⟨5771906386186047304828423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7695875181581396406437897 5771906386186047304828423)
      ·
        refine ⟨8657859579279070957242635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5771906386186047304828423 8657859579279070957242635)
        ·
          refine ⟨12986789368918606435863953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8657859579279070957242635 12986789368918606435863953)
          ·
            refine ⟨9740092026688954826897965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12986789368918606435863953 9740092026688954826897965)
            ·
              refine ⟨3652534510008358060086737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9740092026688954826897965 3652534510008358060086737)
              ·
                refine ⟨2739400882506268545065053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3652534510008358060086737 2739400882506268545065053)
                ·
                  refine ⟨1027275330939850704399395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2739400882506268545065053 1027275330939850704399395)
                  ·
                    refine ⟨1540912996409776056599093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1027275330939850704399395 1540912996409776056599093)
                    ·
                      refine ⟨144460593413416505306165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1540912996409776056599093 144460593413416505306165)
                      ·
                        rfl

theorem cell23_281336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_281336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281336 prefixEnd_281336 := by exact prefixLift 281336
  have htrace : WordTrace (prefixWord ++ tailWord_281336) baseStart_281336 baseEnd_281336 := by
    simpa [prefixWord, tailWord_281336, baseEnd_281336] using wordTrace_append hprefix tailTrace_281336
  have hstable : (prefixWord ++ tailWord_281336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281336).length < 2 ^ (prefixWord ++ tailWord_281336).sum := by decide
  have hdescent : baseEnd_281336 < baseStart_281336 := by decide
  rcases family_descends (prefixWord ++ tailWord_281336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281417 : List Nat := [1, 2, 1, 1, 2, 6, 2, 2, 2, 1, 3]
def baseStart_281417 : Nat := 118140960795 + 281417 * 2 ^ 59
def prefixEnd_281417 : Nat := 4983230072969 + 3 ^ 40 * 281417 * 2
def baseEnd_281417 : Nat := 144502185346430688393293

theorem tailTrace_281417 : CollatzResearch.WordTrace tailWord_281417 prefixEnd_281417 144502185346430688393293 := by
  unfold tailWord_281417
  simp only [CollatzResearch.WordTrace]
  refine ⟨10264121221481746042282505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6842747480987830694855003 10264121221481746042282505)
  ·
    refine ⟨7698090916111309531711879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10264121221481746042282505 7698090916111309531711879)
    ·
      refine ⟨11547136374166964297567819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7698090916111309531711879 11547136374166964297567819)
      ·
        refine ⟨17320704561250446446351729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11547136374166964297567819 17320704561250446446351729)
        ·
          refine ⟨12990528420937834834763797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17320704561250446446351729 12990528420937834834763797)
          ·
            refine ⟨608931019731461007879553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12990528420937834834763797 608931019731461007879553)
            ·
              refine ⟨456698264798595755909665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 608931019731461007879553 456698264798595755909665)
              ·
                refine ⟨342523698598946816932249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 456698264798595755909665 342523698598946816932249)
                ·
                  refine ⟨256892773949210112699187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 342523698598946816932249 256892773949210112699187)
                  ·
                    refine ⟨385339160923815169048781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 256892773949210112699187 385339160923815169048781)
                    ·
                      refine ⟨144502185346430688393293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 385339160923815169048781 144502185346430688393293)
                      ·
                        rfl

theorem cell23_281417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 2, 1, 3].length) (baseStart_281417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281417 prefixEnd_281417 := by exact prefixLift 281417
  have htrace : WordTrace (prefixWord ++ tailWord_281417) baseStart_281417 baseEnd_281417 := by
    simpa [prefixWord, tailWord_281417, baseEnd_281417] using wordTrace_append hprefix tailTrace_281417
  have hstable : (prefixWord ++ tailWord_281417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281417).length < 2 ^ (prefixWord ++ tailWord_281417).sum := by decide
  have hdescent : baseEnd_281417 < baseStart_281417 := by decide
  rcases family_descends (prefixWord ++ tailWord_281417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281433 : List Nat := [1, 2, 1, 2, 2, 5, 1, 1, 2, 6]
def baseStart_281433 : Nat := 118140960795 + 281433 * 2 ^ 59
def prefixEnd_281433 : Nat := 4983230072969 + 3 ^ 40 * 281433 * 2
def baseEnd_281433 : Nat := 48170133678967541931073

theorem tailTrace_281433 : CollatzResearch.WordTrace tailWord_281433 prefixEnd_281433 48170133678967541931073 := by
  unfold tailWord_281433
  simp only [CollatzResearch.WordTrace]
  refine ⟨10264704789423780774864953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6843136526282520516576635 10264704789423780774864953)
  ·
    refine ⟨7698528592067835581148715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10264704789423780774864953 7698528592067835581148715)
    ·
      refine ⟨11547792888101753371723073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7698528592067835581148715 11547792888101753371723073)
      ·
        refine ⟨8660844666076315028792305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11547792888101753371723073 8660844666076315028792305)
        ·
          refine ⟨6495633499557236271594229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8660844666076315028792305 6495633499557236271594229)
          ·
            refine ⟨608965640583490900461959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6495633499557236271594229 608965640583490900461959)
            ·
              refine ⟨913448460875236350692939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 608965640583490900461959 913448460875236350692939)
              ·
                refine ⟨1370172691312854526039409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 913448460875236350692939 1370172691312854526039409)
                ·
                  refine ⟨1027629518484640894529557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1370172691312854526039409 1027629518484640894529557)
                  ·
                    refine ⟨48170133678967541931073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1027629518484640894529557 48170133678967541931073)
                    ·
                      rfl

theorem cell23_281433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 6].length) (baseStart_281433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281433 prefixEnd_281433 := by exact prefixLift 281433
  have htrace : WordTrace (prefixWord ++ tailWord_281433) baseStart_281433 baseEnd_281433 := by
    simpa [prefixWord, tailWord_281433, baseEnd_281433] using wordTrace_append hprefix tailTrace_281433
  have hstable : (prefixWord ++ tailWord_281433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281433).length < 2 ^ (prefixWord ++ tailWord_281433).sum := by decide
  have hdescent : baseEnd_281433 < baseStart_281433 := by decide
  rcases family_descends (prefixWord ++ tailWord_281433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281453 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 3, 4, 4]
def baseStart_281453 : Nat := 118140960795 + 281453 * 2 ^ 59
def prefixEnd_281453 : Nat := 4983230072969 + 3 ^ 40 * 281453 * 2
def baseEnd_281453 : Nat := 144520670649992547543127

theorem tailTrace_281453 : CollatzResearch.WordTrace tailWord_281453 prefixEnd_281453 144520670649992547543127 := by
  unfold tailWord_281453
  simp only [CollatzResearch.WordTrace]
  refine ⟨10265434249351324190593013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6843622832900882793728675 10265434249351324190593013)
  ·
    refine ⟨962384460876686642868095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10265434249351324190593013 962384460876686642868095)
    ·
      refine ⟨1443576691315029964302143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 962384460876686642868095 1443576691315029964302143)
      ·
        refine ⟨2165365036972544946453215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1443576691315029964302143 2165365036972544946453215)
        ·
          refine ⟨3248047555458817419679823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2165365036972544946453215 3248047555458817419679823)
          ·
            refine ⟨4872071333188226129519735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3248047555458817419679823 4872071333188226129519735)
            ·
              refine ⟨7308106999782339194279603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4872071333188226129519735 7308106999782339194279603)
              ·
                refine ⟨10962160499673508791419405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7308106999782339194279603 10962160499673508791419405)
                ·
                  refine ⟨4110810187377565796782277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10962160499673508791419405 4110810187377565796782277)
                  ·
                    refine ⟨770776910133293586896677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4110810187377565796782277 770776910133293586896677)
                    ·
                      refine ⟨144520670649992547543127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 770776910133293586896677 144520670649992547543127)
                      ·
                        rfl

theorem cell23_281453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_281453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281453 prefixEnd_281453 := by exact prefixLift 281453
  have htrace : WordTrace (prefixWord ++ tailWord_281453) baseStart_281453 baseEnd_281453 := by
    simpa [prefixWord, tailWord_281453, baseEnd_281453] using wordTrace_append hprefix tailTrace_281453
  have hstable : (prefixWord ++ tailWord_281453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281453).length < 2 ^ (prefixWord ++ tailWord_281453).sum := by decide
  have hdescent : baseEnd_281453 < baseStart_281453 := by decide
  rcases family_descends (prefixWord ++ tailWord_281453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281461 : List Nat := [1, 3, 4, 1, 1, 4, 2, 1, 1, 3, 2]
def baseStart_281461 : Nat := 118140960795 + 281461 * 2 ^ 59
def prefixEnd_281461 : Nat := 4983230072969 + 3 ^ 40 * 281461 * 2
def baseEnd_281461 : Nat := 144524778495228516243091

theorem tailTrace_281461 : CollatzResearch.WordTrace tailWord_281461 prefixEnd_281461 144524778495228516243091 := by
  unfold tailWord_281461
  simp only [CollatzResearch.WordTrace]
  refine ⟨10265726033322341556884237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6843817355548227704589491 10265726033322341556884237)
  ·
    refine ⟨3849647262495878083831589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10265726033322341556884237 3849647262495878083831589)
    ·
      refine ⟨721808861717977140718423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3849647262495878083831589 721808861717977140718423)
      ·
        refine ⟨1082713292576965711077635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 721808861717977140718423 1082713292576965711077635)
        ·
          refine ⟨1624069938865448566616453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1082713292576965711077635 1624069938865448566616453)
          ·
            refine ⟨304513113537271606240585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1624069938865448566616453 304513113537271606240585)
            ·
              refine ⟨228384835152953704680439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304513113537271606240585 228384835152953704680439)
              ·
                refine ⟨342577252729430557020659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 228384835152953704680439 342577252729430557020659)
                ·
                  refine ⟨513865879094145835530989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 342577252729430557020659 513865879094145835530989)
                  ·
                    refine ⟨192699704660304688324121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 513865879094145835530989 192699704660304688324121)
                    ·
                      refine ⟨144524778495228516243091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 192699704660304688324121 144524778495228516243091)
                      ·
                        rfl

theorem cell23_281461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_281461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281461 prefixEnd_281461 := by exact prefixLift 281461
  have htrace : WordTrace (prefixWord ++ tailWord_281461) baseStart_281461 baseEnd_281461 := by
    simpa [prefixWord, tailWord_281461, baseEnd_281461] using wordTrace_append hprefix tailTrace_281461
  have hstable : (prefixWord ++ tailWord_281461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281461).length < 2 ^ (prefixWord ++ tailWord_281461).sum := by decide
  have hdescent : baseEnd_281461 < baseStart_281461 := by decide
  rcases family_descends (prefixWord ++ tailWord_281461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281480 : List Nat := [2, 1, 3, 3, 2, 2, 2, 1, 7]
def baseStart_281480 : Nat := 118140960795 + 281480 * 2 ^ 59
def prefixEnd_281480 : Nat := 4983230072969 + 3 ^ 40 * 281480 * 2
def baseEnd_281480 : Nat := 16059392736407104656167

theorem tailTrace_281480 : CollatzResearch.WordTrace tailWord_281480 prefixEnd_281480 16059392736407104656167 := by
  unfold tailWord_281480
  simp only [CollatzResearch.WordTrace]
  refine ⟨5133209510126753900912947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6844279346835671867883929 5133209510126753900912947)
  ·
    refine ⟨7699814265190130851369421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5133209510126753900912947 7699814265190130851369421)
    ·
      refine ⟨2887430349446299069263533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7699814265190130851369421 2887430349446299069263533)
      ·
        refine ⟨1082786381042362150973825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2887430349446299069263533 1082786381042362150973825)
        ·
          refine ⟨812089785781771613230369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1082786381042362150973825 812089785781771613230369)
          ·
            refine ⟨609067339336328709922777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 812089785781771613230369 609067339336328709922777)
            ·
              refine ⟨456800504502246532442083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 609067339336328709922777 456800504502246532442083)
              ·
                refine ⟨685200756753369798663125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 456800504502246532442083 685200756753369798663125)
                ·
                  refine ⟨16059392736407104656167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 685200756753369798663125 16059392736407104656167)
                  ·
                    rfl

theorem cell23_281480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 7].length) (baseStart_281480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281480 prefixEnd_281480 := by exact prefixLift 281480
  have htrace : WordTrace (prefixWord ++ tailWord_281480) baseStart_281480 baseEnd_281480 := by
    simpa [prefixWord, tailWord_281480, baseEnd_281480] using wordTrace_append hprefix tailTrace_281480
  have hstable : (prefixWord ++ tailWord_281480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281480).length < 2 ^ (prefixWord ++ tailWord_281480).sum := by decide
  have hdescent : baseEnd_281480 < baseStart_281480 := by decide
  rcases family_descends (prefixWord ++ tailWord_281480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281493 : List Nat := [1, 3, 2, 1, 1, 4, 1, 2, 1, 7]
def baseStart_281493 : Nat := 118140960795 + 281493 * 2 ^ 59
def prefixEnd_281493 : Nat := 4983230072969 + 3 ^ 40 * 281493 * 2
def baseEnd_281493 : Nat := 48180403292057463680981

theorem tailTrace_281493 : CollatzResearch.WordTrace tailWord_281493 prefixEnd_281493 48180403292057463680981 := by
  unfold tailWord_281493
  simp only [CollatzResearch.WordTrace]
  refine ⟨10266893169206411022049133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6844595446137607348032755 10266893169206411022049133)
  ·
    refine ⟨3850084938452404133268425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10266893169206411022049133 3850084938452404133268425)
    ·
      refine ⟨2887563703839303099951319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3850084938452404133268425 2887563703839303099951319)
      ·
        refine ⟨4331345555758954649926979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2887563703839303099951319 4331345555758954649926979)
        ·
          refine ⟨6497018333638431974890469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4331345555758954649926979 6497018333638431974890469)
          ·
            refine ⟨1218190937557205995291963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6497018333638431974890469 1218190937557205995291963)
            ·
              refine ⟨1827286406335808992937945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1218190937557205995291963 1827286406335808992937945)
              ·
                refine ⟨1370464804751856744703459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1827286406335808992937945 1370464804751856744703459)
                ·
                  refine ⟨2055697207127785117055189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1370464804751856744703459 2055697207127785117055189)
                  ·
                    refine ⟨48180403292057463680981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2055697207127785117055189 48180403292057463680981)
                    ·
                      rfl

theorem cell23_281493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_281493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281493 prefixEnd_281493 := by exact prefixLift 281493
  have htrace : WordTrace (prefixWord ++ tailWord_281493) baseStart_281493 baseEnd_281493 := by
    simpa [prefixWord, tailWord_281493, baseEnd_281493] using wordTrace_append hprefix tailTrace_281493
  have hstable : (prefixWord ++ tailWord_281493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281493).length < 2 ^ (prefixWord ++ tailWord_281493).sum := by decide
  have hdescent : baseEnd_281493 < baseStart_281493 := by decide
  rcases family_descends (prefixWord ++ tailWord_281493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281513 : List Nat := [1, 2, 1, 1, 1, 1, 5, 3, 1, 3, 4]
def baseStart_281513 : Nat := 118140960795 + 281513 * 2 ^ 59
def prefixEnd_281513 : Nat := 4983230072969 + 3 ^ 40 * 281513 * 2
def baseEnd_281513 : Nat := 144551479489262312792851

theorem tailTrace_281513 : CollatzResearch.WordTrace tailWord_281513 prefixEnd_281513 144551479489262312792851 := by
  unfold tailWord_281513
  simp only [CollatzResearch.WordTrace]
  refine ⟨10267622629133954437777193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6845081752755969625184795 10267622629133954437777193)
  ·
    refine ⟨7700716971850465828332895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10267622629133954437777193 7700716971850465828332895)
    ·
      refine ⟨11551075457775698742499343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7700716971850465828332895 11551075457775698742499343)
      ·
        refine ⟨17326613186663548113749015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11551075457775698742499343 17326613186663548113749015)
        ·
          refine ⟨25989919779995322170623523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17326613186663548113749015 25989919779995322170623523)
          ·
            refine ⟨38984879669992983255935285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25989919779995322170623523 38984879669992983255935285)
            ·
              refine ⟨3654832469061842180243933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38984879669992983255935285 3654832469061842180243933)
              ·
                refine ⟨1370562175898190817591475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3654832469061842180243933 1370562175898190817591475)
                ·
                  refine ⟨2055843263847286226387213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1370562175898190817591475 2055843263847286226387213)
                  ·
                    refine ⟨770941223942732334895205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2055843263847286226387213 770941223942732334895205)
                    ·
                      refine ⟨144551479489262312792851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 770941223942732334895205 144551479489262312792851)
                      ·
                        rfl

theorem cell23_281513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 3, 4].length) (baseStart_281513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281513 prefixEnd_281513 := by exact prefixLift 281513
  have htrace : WordTrace (prefixWord ++ tailWord_281513) baseStart_281513 baseEnd_281513 := by
    simpa [prefixWord, tailWord_281513, baseEnd_281513] using wordTrace_append hprefix tailTrace_281513
  have hstable : (prefixWord ++ tailWord_281513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281513).length < 2 ^ (prefixWord ++ tailWord_281513).sum := by decide
  have hdescent : baseEnd_281513 < baseStart_281513 := by decide
  rcases family_descends (prefixWord ++ tailWord_281513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281530 : List Nat := [3, 1, 1, 1, 2, 1, 5, 2, 2, 1, 4]
def baseStart_281530 : Nat := 118140960795 + 281530 * 2 ^ 59
def prefixEnd_281530 : Nat := 4983230072969 + 3 ^ 40 * 281530 * 2
def baseEnd_281530 : Nat := 144560208660388746280273

theorem tailTrace_281530 : CollatzResearch.WordTrace tailWord_281530 prefixEnd_281530 144560208660388746280273 := by
  unfold tailWord_281530
  simp only [CollatzResearch.WordTrace]
  refine ⟨2567060667518091585286511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6845495113381577560764029 2567060667518091585286511)
  ·
    refine ⟨3850591001277137377929767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2567060667518091585286511 3850591001277137377929767)
    ·
      refine ⟨5775886501915706066894651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3850591001277137377929767 5775886501915706066894651)
      ·
        refine ⟨8663829752873559100341977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5775886501915706066894651 8663829752873559100341977)
        ·
          refine ⟨6497872314655169325256483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8663829752873559100341977 6497872314655169325256483)
          ·
            refine ⟨9746808471982753987884725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6497872314655169325256483 9746808471982753987884725)
            ·
              refine ⟨913763294248383186364193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9746808471982753987884725 913763294248383186364193)
              ·
                refine ⟨685322470686287389773145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 913763294248383186364193 685322470686287389773145)
                ·
                  refine ⟨513991853014715542329859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 685322470686287389773145 513991853014715542329859)
                  ·
                    refine ⟨770987779522073313494789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 513991853014715542329859 770987779522073313494789)
                    ·
                      refine ⟨144560208660388746280273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 770987779522073313494789 144560208660388746280273)
                      ·
                        rfl

theorem cell23_281530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_281530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281530 prefixEnd_281530 := by exact prefixLift 281530
  have htrace : WordTrace (prefixWord ++ tailWord_281530) baseStart_281530 baseEnd_281530 := by
    simpa [prefixWord, tailWord_281530, baseEnd_281530] using wordTrace_append hprefix tailTrace_281530
  have hstable : (prefixWord ++ tailWord_281530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281530).length < 2 ^ (prefixWord ++ tailWord_281530).sum := by decide
  have hdescent : baseEnd_281530 < baseStart_281530 := by decide
  rcases family_descends (prefixWord ++ tailWord_281530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281542 : List Nat := [6, 1, 3, 1, 1, 1, 1, 3, 2, 2, 2]
def baseStart_281542 : Nat := 118140960795 + 281542 * 2 ^ 59
def prefixEnd_281542 : Nat := 4983230072969 + 3 ^ 40 * 281542 * 2
def baseEnd_281542 : Nat := 144566370428242699330219

theorem tailTrace_281542 : CollatzResearch.WordTrace tailWord_281542 prefixEnd_281542 144566370428242699330219 := by
  unfold tailWord_281542
  simp only [CollatzResearch.WordTrace]
  refine ⟨320896260813402887205715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6845786897352594927055253 320896260813402887205715)
  ·
    refine ⟨481344391220104330808573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 320896260813402887205715 481344391220104330808573)
    ·
      refine ⟨180504146707539124053215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 481344391220104330808573 180504146707539124053215)
      ·
        refine ⟨270756220061308686079823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180504146707539124053215 270756220061308686079823)
        ·
          refine ⟨406134330091963029119735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270756220061308686079823 406134330091963029119735)
          ·
            refine ⟨609201495137944543679603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406134330091963029119735 609201495137944543679603)
            ·
              refine ⟨913802242706916815519405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 609201495137944543679603 913802242706916815519405)
              ·
                refine ⟨342675841015093805819777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 913802242706916815519405 342675841015093805819777)
                ·
                  refine ⟨257006880761320354364833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 342675841015093805819777 257006880761320354364833)
                  ·
                    refine ⟨192755160570990265773625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 257006880761320354364833 192755160570990265773625)
                    ·
                      refine ⟨144566370428242699330219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 192755160570990265773625 144566370428242699330219)
                      ·
                        rfl

theorem cell23_281542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_281542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281542 prefixEnd_281542 := by exact prefixLift 281542
  have htrace : WordTrace (prefixWord ++ tailWord_281542) baseStart_281542 baseEnd_281542 := by
    simpa [prefixWord, tailWord_281542, baseEnd_281542] using wordTrace_append hprefix tailTrace_281542
  have hstable : (prefixWord ++ tailWord_281542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281542).length < 2 ^ (prefixWord ++ tailWord_281542).sum := by decide
  have hdescent : baseEnd_281542 < baseStart_281542 := by decide
  rcases family_descends (prefixWord ++ tailWord_281542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281543 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 6]
def baseStart_281543 : Nat := 118140960795 + 281543 * 2 ^ 59
def prefixEnd_281543 : Nat := 4983230072969 + 3 ^ 40 * 281543 * 2
def baseEnd_281543 : Nat := 144566883908897195417713

theorem tailTrace_281543 : CollatzResearch.WordTrace tailWord_281543 prefixEnd_281543 144566883908897195417713 := by
  unfold tailWord_281543
  simp only [CollatzResearch.WordTrace]
  refine ⟨10268716819025269561369283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6845811212683513040912855 10268716819025269561369283)
  ·
    refine ⟨15403075228537904342053925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10268716819025269561369283 15403075228537904342053925)
    ·
      refine ⟨2888076605350857064135111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15403075228537904342053925 2888076605350857064135111)
      ·
        refine ⟨4332114908026285596202667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2888076605350857064135111 4332114908026285596202667)
        ·
          refine ⟨6498172362039428394304001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4332114908026285596202667 6498172362039428394304001)
          ·
            refine ⟨4873629271529571295728001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6498172362039428394304001 4873629271529571295728001)
            ·
              refine ⟨3655221953647178471796001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4873629271529571295728001 3655221953647178471796001)
              ·
                refine ⟨2741416465235383853847001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3655221953647178471796001 2741416465235383853847001)
                ·
                  refine ⟨2056062348926537890385251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2741416465235383853847001 2056062348926537890385251)
                  ·
                    refine ⟨3084093523389806835577877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2056062348926537890385251 3084093523389806835577877)
                    ·
                      refine ⟨144566883908897195417713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3084093523389806835577877 144566883908897195417713)
                      ·
                        rfl

theorem cell23_281543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_281543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281543 prefixEnd_281543 := by exact prefixLift 281543
  have htrace : WordTrace (prefixWord ++ tailWord_281543) baseStart_281543 baseEnd_281543 := by
    simpa [prefixWord, tailWord_281543, baseEnd_281543] using wordTrace_append hprefix tailTrace_281543
  have hstable : (prefixWord ++ tailWord_281543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281543).length < 2 ^ (prefixWord ++ tailWord_281543).sum := by decide
  have hdescent : baseEnd_281543 < baseStart_281543 := by decide
  rcases family_descends (prefixWord ++ tailWord_281543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281597 : List Nat := [1, 4, 1, 1, 1, 2, 1, 5, 3, 1, 3]
def baseStart_281597 : Nat := 118140960795 + 281597 * 2 ^ 59
def prefixEnd_281597 : Nat := 4983230072969 + 3 ^ 40 * 281597 * 2
def baseEnd_281597 : Nat := 144594611864239984142465

theorem tailTrace_281597 : CollatzResearch.WordTrace tailWord_281597 prefixEnd_281597 144594611864239984142465 := by
  unfold tailWord_281597
  simp only [CollatzResearch.WordTrace]
  refine ⟨10270686360829636783835045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6847124240553091189223363 10270686360829636783835045)
  ·
    refine ⟨1925753692655556896969071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10270686360829636783835045 1925753692655556896969071)
    ·
      refine ⟨2888630538983335345453607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1925753692655556896969071 2888630538983335345453607)
      ·
        refine ⟨4332945808475003018180411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2888630538983335345453607 4332945808475003018180411)
        ·
          refine ⟨6499418712712504527270617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4332945808475003018180411 6499418712712504527270617)
          ·
            refine ⟨4874564034534378395452963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6499418712712504527270617 4874564034534378395452963)
            ·
              refine ⟨7311846051801567593179445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4874564034534378395452963 7311846051801567593179445)
              ·
                refine ⟨685485567356396961860573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7311846051801567593179445 685485567356396961860573)
                ·
                  refine ⟨257057087758648860697715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 685485567356396961860573 257057087758648860697715)
                  ·
                    refine ⟨385585631637973291046573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 257057087758648860697715 385585631637973291046573)
                    ·
                      refine ⟨144594611864239984142465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 385585631637973291046573 144594611864239984142465)
                      ·
                        rfl

theorem cell23_281597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_281597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281597 prefixEnd_281597 := by exact prefixLift 281597
  have htrace : WordTrace (prefixWord ++ tailWord_281597) baseStart_281597 baseEnd_281597 := by
    simpa [prefixWord, tailWord_281597, baseEnd_281597] using wordTrace_append hprefix tailTrace_281597
  have hstable : (prefixWord ++ tailWord_281597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281597).length < 2 ^ (prefixWord ++ tailWord_281597).sum := by decide
  have hdescent : baseEnd_281597 < baseStart_281597 := by decide
  rcases family_descends (prefixWord ++ tailWord_281597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281607 : List Nat := [1, 1, 4, 3, 1, 1, 2, 2, 1, 5, 2]
def baseStart_281607 : Nat := 118140960795 + 281607 * 2 ^ 59
def prefixEnd_281607 : Nat := 4983230072969 + 3 ^ 40 * 281607 * 2
def baseEnd_281607 : Nat := 144599746670784945017419

theorem tailTrace_281607 : CollatzResearch.WordTrace tailWord_281607 prefixEnd_281607 144599746670784945017419 := by
  unfold tailWord_281607
  simp only [CollatzResearch.WordTrace]
  refine ⟨10271051090793408491699075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6847367393862272327799383 10271051090793408491699075)
  ·
    refine ⟨15406576636190112737548613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10271051090793408491699075 15406576636190112737548613)
    ·
      refine ⟨2888733119285646138290365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15406576636190112737548613 2888733119285646138290365)
      ·
        refine ⟨1083274919732117301858887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2888733119285646138290365 1083274919732117301858887)
        ·
          refine ⟨1624912379598175952788331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1083274919732117301858887 1624912379598175952788331)
          ·
            refine ⟨2437368569397263929182497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1624912379598175952788331 2437368569397263929182497)
            ·
              refine ⟨1828026427047947946886873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2437368569397263929182497 1828026427047947946886873)
              ·
                refine ⟨1371019820285960960165155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1828026427047947946886873 1371019820285960960165155)
                ·
                  refine ⟨2056529730428941440247733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1371019820285960960165155 2056529730428941440247733)
                  ·
                    refine ⟨192799662227713260023225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2056529730428941440247733 192799662227713260023225)
                    ·
                      refine ⟨144599746670784945017419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 192799662227713260023225 144599746670784945017419)
                      ·
                        rfl

theorem cell23_281607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_281607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281607 prefixEnd_281607 := by exact prefixLift 281607
  have htrace : WordTrace (prefixWord ++ tailWord_281607) baseStart_281607 baseEnd_281607 := by
    simpa [prefixWord, tailWord_281607, baseEnd_281607] using wordTrace_append hprefix tailTrace_281607
  have hstable : (prefixWord ++ tailWord_281607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281607).length < 2 ^ (prefixWord ++ tailWord_281607).sum := by decide
  have hdescent : baseEnd_281607 < baseStart_281607 := by decide
  rcases family_descends (prefixWord ++ tailWord_281607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281614 : List Nat := [4, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3]
def baseStart_281614 : Nat := 118140960795 + 281614 * 2 ^ 59
def prefixEnd_281614 : Nat := 4983230072969 + 3 ^ 40 * 281614 * 2
def baseEnd_281614 : Nat := 144603341035366417629887

theorem tailTrace_281614 : CollatzResearch.WordTrace tailWord_281614 prefixEnd_281614 144603341035366417629887 := by
  unfold tailWord_281614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1283913300221006085900487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6847537601178699124802597 1283913300221006085900487)
  ·
    refine ⟨1925869950331509128850731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1283913300221006085900487 1925869950331509128850731)
    ·
      refine ⟨2888804925497263693276097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1925869950331509128850731 2888804925497263693276097)
      ·
        refine ⟨2166603694122947769957073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2888804925497263693276097 2166603694122947769957073)
        ·
          refine ⟨1624952770592210827467805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2166603694122947769957073 1624952770592210827467805)
          ·
            refine ⟨609357288972079060300427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1624952770592210827467805 609357288972079060300427)
            ·
              refine ⟨914035933458118590450641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 609357288972079060300427 914035933458118590450641)
              ·
                refine ⟨685526950093588942837981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 914035933458118590450641 685526950093588942837981)
                ·
                  refine ⟨257072606285095853564243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 685526950093588942837981 257072606285095853564243)
                  ·
                    refine ⟨385608909427643780346365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 257072606285095853564243 385608909427643780346365)
                    ·
                      refine ⟨144603341035366417629887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 385608909427643780346365 144603341035366417629887)
                      ·
                        rfl

theorem cell23_281614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_281614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281614 prefixEnd_281614 := by exact prefixLift 281614
  have htrace : WordTrace (prefixWord ++ tailWord_281614) baseStart_281614 baseEnd_281614 := by
    simpa [prefixWord, tailWord_281614, baseEnd_281614] using wordTrace_append hprefix tailTrace_281614
  have hstable : (prefixWord ++ tailWord_281614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281614).length < 2 ^ (prefixWord ++ tailWord_281614).sum := by decide
  have hdescent : baseEnd_281614 < baseStart_281614 := by decide
  rcases family_descends (prefixWord ++ tailWord_281614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281624 : List Nat := [2, 1, 2, 3, 2, 2, 3, 1, 2, 3, 2]
def baseStart_281624 : Nat := 118140960795 + 281624 * 2 ^ 59
def prefixEnd_281624 : Nat := 4983230072969 + 3 ^ 40 * 281624 * 2
def baseEnd_281624 : Nat := 144608475841911378504841

theorem tailTrace_281624 : CollatzResearch.WordTrace tailWord_281624 prefixEnd_281624 144608475841911378504841 := by
  unfold tailWord_281624
  simp only [CollatzResearch.WordTrace]
  refine ⟨5135835565865910197533963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6847780754487880263378617 5135835565865910197533963)
  ·
    refine ⟨7703753348798865296300945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5135835565865910197533963 7703753348798865296300945)
    ·
      refine ⟨5777815011599148972225709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7703753348798865296300945 5777815011599148972225709)
      ·
        refine ⟨2166680629349680864584641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5777815011599148972225709 2166680629349680864584641)
        ·
          refine ⟨1625010472012260648438481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2166680629349680864584641 1625010472012260648438481)
          ·
            refine ⟨1218757854009195486328861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1625010472012260648438481 1218757854009195486328861)
            ·
              refine ⟨457034195253448307373323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1218757854009195486328861 457034195253448307373323)
              ·
                refine ⟨685551292880172461059985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 457034195253448307373323 685551292880172461059985)
                ·
                  refine ⟨514163469660129345794989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 685551292880172461059985 514163469660129345794989)
                  ·
                    refine ⟨192811301122548504673121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 514163469660129345794989 192811301122548504673121)
                    ·
                      refine ⟨144608475841911378504841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 192811301122548504673121 144608475841911378504841)
                      ·
                        rfl

theorem cell23_281624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_281624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281624 prefixEnd_281624 := by exact prefixLift 281624
  have htrace : WordTrace (prefixWord ++ tailWord_281624) baseStart_281624 baseEnd_281624 := by
    simpa [prefixWord, tailWord_281624, baseEnd_281624] using wordTrace_append hprefix tailTrace_281624
  have hstable : (prefixWord ++ tailWord_281624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281624).length < 2 ^ (prefixWord ++ tailWord_281624).sum := by decide
  have hdescent : baseEnd_281624 < baseStart_281624 := by decide
  rcases family_descends (prefixWord ++ tailWord_281624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281631 : List Nat := [1, 1, 2, 4, 1, 4, 2, 3, 1, 1, 3]
def baseStart_281631 : Nat := 118140960795 + 281631 * 2 ^ 59
def prefixEnd_281631 : Nat := 4983230072969 + 3 ^ 40 * 281631 * 2
def baseEnd_281631 : Nat := 144612070206492851117309

theorem tailTrace_281631 : CollatzResearch.WordTrace tailWord_281631 prefixEnd_281631 144612070206492851117309 := by
  unfold tailWord_281631
  simp only [CollatzResearch.WordTrace]
  refine ⟨10271926442706460590572747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6847950961804307060381831 10271926442706460590572747)
  ·
    refine ⟨15407889664059690885859121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10271926442706460590572747 15407889664059690885859121)
    ·
      refine ⟨11555917248044768164394341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15407889664059690885859121 11555917248044768164394341)
      ·
        refine ⟨2166734484008394030823939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11555917248044768164394341 2166734484008394030823939)
        ·
          refine ⟨3250101726012591046235909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2166734484008394030823939 3250101726012591046235909)
          ·
            refine ⟨609394073627360821169233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3250101726012591046235909 609394073627360821169233)
            ·
              refine ⟨457045555220520615876925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 609394073627360821169233 457045555220520615876925)
              ·
                refine ⟨171392083207695230953847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 457045555220520615876925 171392083207695230953847)
                ·
                  refine ⟨257088124811542846430771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171392083207695230953847 257088124811542846430771)
                  ·
                    refine ⟨385632187217314269646157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 257088124811542846430771 385632187217314269646157)
                    ·
                      refine ⟨144612070206492851117309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 385632187217314269646157 144612070206492851117309)
                      ·
                        rfl

theorem cell23_281631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_281631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281631 prefixEnd_281631 := by exact prefixLift 281631
  have htrace : WordTrace (prefixWord ++ tailWord_281631) baseStart_281631 baseEnd_281631 := by
    simpa [prefixWord, tailWord_281631, baseEnd_281631] using wordTrace_append hprefix tailTrace_281631
  have hstable : (prefixWord ++ tailWord_281631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281631).length < 2 ^ (prefixWord ++ tailWord_281631).sum := by decide
  have hdescent : baseEnd_281631 < baseStart_281631 := by decide
  rcases family_descends (prefixWord ++ tailWord_281631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281634 : List Nat := [3, 3, 1, 1, 1, 3, 4, 1, 1, 5]
def baseStart_281634 : Nat := 118140960795 + 281634 * 2 ^ 59
def prefixEnd_281634 : Nat := 4983230072969 + 3 ^ 40 * 281634 * 2
def baseEnd_281634 : Nat := 48204536882818779793265

theorem tailTrace_281634 : CollatzResearch.WordTrace tailWord_281634 prefixEnd_281634 48204536882818779793265 := by
  unfold tailWord_281634
  simp only [CollatzResearch.WordTrace]
  refine ⟨2568008965423898025732989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6848023907797061401954637 2568008965423898025732989)
  ·
    refine ⟨963003362033961759649871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2568008965423898025732989 963003362033961759649871)
    ·
      refine ⟨1444505043050942639474807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 963003362033961759649871 1444505043050942639474807)
      ·
        refine ⟨2166757564576413959212211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1444505043050942639474807 2166757564576413959212211)
        ·
          refine ⟨3250136346864620938818317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2166757564576413959212211 3250136346864620938818317)
          ·
            refine ⟨1218801130074232852056869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3250136346864620938818317 1218801130074232852056869)
            ·
              refine ⟨228525211888918659760663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1218801130074232852056869 228525211888918659760663)
              ·
                refine ⟨342787817833377989640995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 228525211888918659760663 342787817833377989640995)
                ·
                  refine ⟨514181726750066984461493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 342787817833377989640995 514181726750066984461493)
                  ·
                    refine ⟨48204536882818779793265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 514181726750066984461493 48204536882818779793265)
                    ·
                      rfl

theorem cell23_281634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_281634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281634 prefixEnd_281634 := by exact prefixLift 281634
  have htrace : WordTrace (prefixWord ++ tailWord_281634) baseStart_281634 baseEnd_281634 := by
    simpa [prefixWord, tailWord_281634, baseEnd_281634] using wordTrace_append hprefix tailTrace_281634
  have hstable : (prefixWord ++ tailWord_281634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281634).length < 2 ^ (prefixWord ++ tailWord_281634).sum := by decide
  have hdescent : baseEnd_281634 < baseStart_281634 := by decide
  rcases family_descends (prefixWord ++ tailWord_281634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281637 : List Nat := [1, 3, 1, 2, 2, 2, 3, 3, 1, 1, 4]
def baseStart_281637 : Nat := 118140960795 + 281637 * 2 ^ 59
def prefixEnd_281637 : Nat := 4983230072969 + 3 ^ 40 * 281637 * 2
def baseEnd_281637 : Nat := 144615151090419827642281

theorem tailTrace_281637 : CollatzResearch.WordTrace tailWord_281637 prefixEnd_281637 144615151090419827642281 := by
  unfold tailWord_281637
  simp only [CollatzResearch.WordTrace]
  refine ⟨10272145280684723615291165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6848096853789815743527443 10272145280684723615291165)
  ·
    refine ⟨3852054480256771355734187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10272145280684723615291165 3852054480256771355734187)
    ·
      refine ⟨5778081720385157033601281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3852054480256771355734187 5778081720385157033601281)
      ·
        refine ⟨4333561290288867775200961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5778081720385157033601281 4333561290288867775200961)
        ·
          refine ⟨3250170967716650831400721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4333561290288867775200961 3250170967716650831400721)
          ·
            refine ⟨2437628225787488123550541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3250170967716650831400721 2437628225787488123550541)
            ·
              refine ⟨914110584670308046331453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2437628225787488123550541 914110584670308046331453)
              ·
                refine ⟨342791469251365517374295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 914110584670308046331453 342791469251365517374295)
                ·
                  refine ⟨514187203877048276061443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 342791469251365517374295 514187203877048276061443)
                  ·
                    refine ⟨771280805815572414092165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 514187203877048276061443 771280805815572414092165)
                    ·
                      refine ⟨144615151090419827642281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 771280805815572414092165 144615151090419827642281)
                      ·
                        rfl

theorem cell23_281637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_281637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281637 prefixEnd_281637 := by exact prefixLift 281637
  have htrace : WordTrace (prefixWord ++ tailWord_281637) baseStart_281637 baseEnd_281637 := by
    simpa [prefixWord, tailWord_281637, baseEnd_281637] using wordTrace_append hprefix tailTrace_281637
  have hstable : (prefixWord ++ tailWord_281637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281637).length < 2 ^ (prefixWord ++ tailWord_281637).sum := by decide
  have hdescent : baseEnd_281637 < baseStart_281637 := by decide
  rcases family_descends (prefixWord ++ tailWord_281637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281643 : List Nat := [1, 1, 1, 1, 2, 1, 16]
def baseStart_281643 : Nat := 118140960795 + 281643 * 2 ^ 59
def prefixEnd_281643 : Nat := 4983230072969 + 3 ^ 40 * 281643 * 2
def baseEnd_281643 : Nat := 1785410271288232150213

theorem tailTrace_281643 : CollatzResearch.WordTrace tailWord_281643 prefixEnd_281643 1785410271288232150213 := by
  unfold tailWord_281643
  simp only [CollatzResearch.WordTrace]
  refine ⟨10272364118662986640009583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6848242745775324426673055 10272364118662986640009583)
  ·
    refine ⟨15408546177994479960014375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10272364118662986640009583 15408546177994479960014375)
    ·
      refine ⟨23112819266991719940021563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15408546177994479960014375 23112819266991719940021563)
      ·
        refine ⟨34669228900487579910032345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23112819266991719940021563 34669228900487579910032345)
        ·
          refine ⟨26001921675365684932524259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34669228900487579910032345 26001921675365684932524259)
          ·
            refine ⟨39002882513048527398786389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26001921675365684932524259 39002882513048527398786389)
            ·
              refine ⟨1785410271288232150213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 16 39002882513048527398786389 1785410271288232150213)
              ·
                rfl

theorem cell23_281643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 16].length) (baseStart_281643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281643 prefixEnd_281643 := by exact prefixLift 281643
  have htrace : WordTrace (prefixWord ++ tailWord_281643) baseStart_281643 baseEnd_281643 := by
    simpa [prefixWord, tailWord_281643, baseEnd_281643] using wordTrace_append hprefix tailTrace_281643
  have hstable : (prefixWord ++ tailWord_281643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281643).length < 2 ^ (prefixWord ++ tailWord_281643).sum := by decide
  have hdescent : baseEnd_281643 < baseStart_281643 := by decide
  rcases family_descends (prefixWord ++ tailWord_281643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281650 : List Nat := [3, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6]
def baseStart_281650 : Nat := 118140960795 + 281650 * 2 ^ 59
def prefixEnd_281650 : Nat := 4983230072969 + 3 ^ 40 * 281650 * 2
def baseEnd_281650 : Nat := 144621826338928276779721

theorem tailTrace_281650 : CollatzResearch.WordTrace tailWord_281650 prefixEnd_281650 144621826338928276779721 := by
  unfold tailWord_281650
  simp only [CollatzResearch.WordTrace]
  refine ⟨2568154857409406708878601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6848412953091751223676269 2568154857409406708878601)
  ·
    refine ⟨1926116143057055031658951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2568154857409406708878601 1926116143057055031658951)
    ·
      refine ⟨2889174214585582547488427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1926116143057055031658951 2889174214585582547488427)
      ·
        refine ⟨4333761321878373821232641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2889174214585582547488427 4333761321878373821232641)
        ·
          refine ⟨3250320991408780365924481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4333761321878373821232641 3250320991408780365924481)
          ·
            refine ⟨2437740743556585274443361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3250320991408780365924481 2437740743556585274443361)
            ·
              refine ⟨1828305557667438955832521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2437740743556585274443361 1828305557667438955832521)
              ·
                refine ⟨1371229168250579216874391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1828305557667438955832521 1371229168250579216874391)
                ·
                  refine ⟨2056843752375868825311587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1371229168250579216874391 2056843752375868825311587)
                  ·
                    refine ⟨3085265628563803237967381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2056843752375868825311587 3085265628563803237967381)
                    ·
                      refine ⟨144621826338928276779721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3085265628563803237967381 144621826338928276779721)
                      ·
                        rfl

theorem cell23_281650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_281650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281650 prefixEnd_281650 := by exact prefixLift 281650
  have htrace : WordTrace (prefixWord ++ tailWord_281650) baseStart_281650 baseEnd_281650 := by
    simpa [prefixWord, tailWord_281650, baseEnd_281650] using wordTrace_append hprefix tailTrace_281650
  have hstable : (prefixWord ++ tailWord_281650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281650).length < 2 ^ (prefixWord ++ tailWord_281650).sum := by decide
  have hdescent : baseEnd_281650 < baseStart_281650 := by decide
  rcases family_descends (prefixWord ++ tailWord_281650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281657 : List Nat := [1, 2, 1, 5, 2, 2, 1, 2, 1, 1, 5]
def baseStart_281657 : Nat := 118140960795 + 281657 * 2 ^ 59
def prefixEnd_281657 : Nat := 4983230072969 + 3 ^ 40 * 281657 * 2
def baseEnd_281657 : Nat := 144625420703509749392189

theorem tailTrace_281657 : CollatzResearch.WordTrace tailWord_281657 prefixEnd_281657 144625420703509749392189 := by
  unfold tailWord_281657
  simp only [CollatzResearch.WordTrace]
  refine ⟨10272874740612267031019225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6848583160408178020679483 10272874740612267031019225)
  ·
    refine ⟨7704656055459200273264419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10272874740612267031019225 7704656055459200273264419)
    ·
      refine ⟨11556984083188800409896629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7704656055459200273264419 11556984083188800409896629)
      ·
        refine ⟨1083467257798950038427809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11556984083188800409896629 1083467257798950038427809)
        ·
          refine ⟨812600443349212528820857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1083467257798950038427809 812600443349212528820857)
          ·
            refine ⟨609450332511909396615643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 812600443349212528820857 609450332511909396615643)
            ·
              refine ⟨914175498767864094923465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 609450332511909396615643 914175498767864094923465)
              ·
                refine ⟨685631624075898071192599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 914175498767864094923465 685631624075898071192599)
                ·
                  refine ⟨1028447436113847106788899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 685631624075898071192599 1028447436113847106788899)
                  ·
                    refine ⟨1542671154170770660183349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1028447436113847106788899 1542671154170770660183349)
                    ·
                      refine ⟨144625420703509749392189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1542671154170770660183349 144625420703509749392189)
                      ·
                        rfl

theorem cell23_281657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_281657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281657 prefixEnd_281657 := by exact prefixLift 281657
  have htrace : WordTrace (prefixWord ++ tailWord_281657) baseStart_281657 baseEnd_281657 := by
    simpa [prefixWord, tailWord_281657, baseEnd_281657] using wordTrace_append hprefix tailTrace_281657
  have hstable : (prefixWord ++ tailWord_281657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281657).length < 2 ^ (prefixWord ++ tailWord_281657).sum := by decide
  have hdescent : baseEnd_281657 < baseStart_281657 := by decide
  rcases family_descends (prefixWord ++ tailWord_281657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281664 : List Nat := [2, 1, 1, 2, 2, 3, 5, 1, 2, 4]
def baseStart_281664 : Nat := 118140960795 + 281664 * 2 ^ 59
def prefixEnd_281664 : Nat := 4983230072969 + 3 ^ 40 * 281664 * 2
def baseEnd_281664 : Nat := 48209671689363740668219

theorem tailTrace_281664 : CollatzResearch.WordTrace tailWord_281664 prefixEnd_281664 48209671689363740668219 := by
  unfold tailWord_281664
  simp only [CollatzResearch.WordTrace]
  refine ⟨5136565025793453613262023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6848753367724604817682697 5136565025793453613262023)
  ·
    refine ⟨7704847538690180419893035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5136565025793453613262023 7704847538690180419893035)
    ·
      refine ⟨11557271308035270629839553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7704847538690180419893035 11557271308035270629839553)
      ·
        refine ⟨8667953481026452972379665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11557271308035270629839553 8667953481026452972379665)
        ·
          refine ⟨6500965110769839729284749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8667953481026452972379665 6500965110769839729284749)
          ·
            refine ⟨2437861916538689898481781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6500965110769839729284749 2437861916538689898481781)
            ·
              refine ⟨228549554675502177982667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2437861916538689898481781 228549554675502177982667)
              ·
                refine ⟨342824332013253266974001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 228549554675502177982667 342824332013253266974001)
                ·
                  refine ⟨257118249009939950230501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 342824332013253266974001 257118249009939950230501)
                  ·
                    refine ⟨48209671689363740668219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 257118249009939950230501 48209671689363740668219)
                    ·
                      rfl

theorem cell23_281664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 2, 4].length) (baseStart_281664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281664 prefixEnd_281664 := by exact prefixLift 281664
  have htrace : WordTrace (prefixWord ++ tailWord_281664) baseStart_281664 baseEnd_281664 := by
    simpa [prefixWord, tailWord_281664, baseEnd_281664] using wordTrace_append hprefix tailTrace_281664
  have hstable : (prefixWord ++ tailWord_281664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281664).length < 2 ^ (prefixWord ++ tailWord_281664).sum := by decide
  have hdescent : baseEnd_281664 < baseStart_281664 := by decide
  rcases family_descends (prefixWord ++ tailWord_281664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281677 : List Nat := [1, 6, 1, 1, 1, 3, 1, 9]
def baseStart_281677 : Nat := 118140960795 + 281677 * 2 ^ 59
def prefixEnd_281677 : Nat := 4983230072969 + 3 ^ 40 * 281677 * 2
def baseEnd_281677 : Nat := 5356877419133321153411

theorem tailTrace_281677 : CollatzResearch.WordTrace tailWord_281677 prefixEnd_281677 5356877419133321153411 := by
  unfold tailWord_281677
  simp only [CollatzResearch.WordTrace]
  refine ⟨10273604200539810446747285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6849069467026540297831523 10273604200539810446747285)
  ·
    refine ⟨481575196900303614691279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10273604200539810446747285 481575196900303614691279)
    ·
      refine ⟨722362795350455422036919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 481575196900303614691279 722362795350455422036919)
      ·
        refine ⟨1083544193025683133055379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 722362795350455422036919 1083544193025683133055379)
        ·
          refine ⟨1625316289538524699583069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1083544193025683133055379 1625316289538524699583069)
          ·
            refine ⟨609493608576946762343651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1625316289538524699583069 609493608576946762343651)
            ·
              refine ⟨914240412865420143515477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 609493608576946762343651 914240412865420143515477)
              ·
                refine ⟨5356877419133321153411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 914240412865420143515477 5356877419133321153411)
                ·
                  rfl

theorem cell23_281677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 9].length) (baseStart_281677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281677 prefixEnd_281677 := by exact prefixLift 281677
  have htrace : WordTrace (prefixWord ++ tailWord_281677) baseStart_281677 baseEnd_281677 := by
    simpa [prefixWord, tailWord_281677, baseEnd_281677] using wordTrace_append hprefix tailTrace_281677
  have hstable : (prefixWord ++ tailWord_281677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281677).length < 2 ^ (prefixWord ++ tailWord_281677).sum := by decide
  have hdescent : baseEnd_281677 < baseStart_281677 := by decide
  rcases family_descends (prefixWord ++ tailWord_281677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281694 : List Nat := [4, 4, 1, 1, 1, 1, 11]
def baseStart_281694 : Nat := 118140960795 + 281694 * 2 ^ 59
def prefixEnd_281694 : Nat := 4983230072969 + 3 ^ 40 * 281694 * 2
def baseEnd_281694 : Nat := 1785733573922544501599

theorem tailTrace_281694 : CollatzResearch.WordTrace tailWord_281694 prefixEnd_281694 1785733573922544501599 := by
  unfold tailWord_281694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1284278030184777793764517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6849482827652148233410757 1284278030184777793764517)
  ·
    refine ⟨240802130659645836330847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1284278030184777793764517 240802130659645836330847)
    ·
      refine ⟨361203195989468754496271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240802130659645836330847 361203195989468754496271)
      ·
        refine ⟨541804793984203131744407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361203195989468754496271 541804793984203131744407)
        ·
          refine ⟨812707190976304697616611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 541804793984203131744407 812707190976304697616611)
          ·
            refine ⟨1219060786464457046424917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 812707190976304697616611 1219060786464457046424917)
            ·
              refine ⟨1785733573922544501599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 1219060786464457046424917 1785733573922544501599)
              ·
                rfl

theorem cell23_281694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 11].length) (baseStart_281694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281694 prefixEnd_281694 := by exact prefixLift 281694
  have htrace : WordTrace (prefixWord ++ tailWord_281694) baseStart_281694 baseEnd_281694 := by
    simpa [prefixWord, tailWord_281694, baseEnd_281694] using wordTrace_append hprefix tailTrace_281694
  have hstable : (prefixWord ++ tailWord_281694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281694).length < 2 ^ (prefixWord ++ tailWord_281694).sum := by decide
  have hdescent : baseEnd_281694 < baseStart_281694 := by decide
  rcases family_descends (prefixWord ++ tailWord_281694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281700 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 4, 2, 5]
def baseStart_281700 : Nat := 118140960795 + 281700 * 2 ^ 59
def prefixEnd_281700 : Nat := 4983230072969 + 3 ^ 40 * 281700 * 2
def baseEnd_281700 : Nat := 144647500371653081154491

theorem tailTrace_281700 : CollatzResearch.WordTrace tailWord_281700 prefixEnd_281700 144647500371653081154491 := by
  unfold tailWord_281700
  simp only [CollatzResearch.WordTrace]
  refine ⟨5137221539728242687417277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6849628719637656916556369 5137221539728242687417277)
  ·
    refine ⟨1926458077398091007781479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5137221539728242687417277 1926458077398091007781479)
    ·
      refine ⟨2889687116097136511672219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1926458077398091007781479 2889687116097136511672219)
      ·
        refine ⟨4334530674145704767508329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2889687116097136511672219 4334530674145704767508329)
        ·
          refine ⟨3250898005609278575631247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4334530674145704767508329 3250898005609278575631247)
          ·
            refine ⟨4876347008413917863446871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3250898005609278575631247 4876347008413917863446871)
            ·
              refine ⟨7314520512620876795170307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4876347008413917863446871 7314520512620876795170307)
              ·
                refine ⟨10971780768931315192755461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7314520512620876795170307 10971780768931315192755461)
                ·
                  refine ⟨2057208894174621598641649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10971780768931315192755461 2057208894174621598641649)
                  ·
                    refine ⟨1542906670630966198981237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2057208894174621598641649 1542906670630966198981237)
                    ·
                      refine ⟨144647500371653081154491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1542906670630966198981237 144647500371653081154491)
                      ·
                        rfl

theorem cell23_281700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_281700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281700 prefixEnd_281700 := by exact prefixLift 281700
  have htrace : WordTrace (prefixWord ++ tailWord_281700) baseStart_281700 baseEnd_281700 := by
    simpa [prefixWord, tailWord_281700, baseEnd_281700] using wordTrace_append hprefix tailTrace_281700
  have hstable : (prefixWord ++ tailWord_281700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281700).length < 2 ^ (prefixWord ++ tailWord_281700).sum := by decide
  have hdescent : baseEnd_281700 < baseStart_281700 := by decide
  rcases family_descends (prefixWord ++ tailWord_281700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281714 : List Nat := [3, 2, 1, 2, 2, 1, 2, 2, 3, 3, 2]
def baseStart_281714 : Nat := 118140960795 + 281714 * 2 ^ 59
def prefixEnd_281714 : Nat := 4983230072969 + 3 ^ 40 * 281714 * 2
def baseEnd_281714 : Nat := 144654689100816026379427

theorem tailTrace_281714 : CollatzResearch.WordTrace tailWord_281714 prefixEnd_281714 144654689100816026379427 := by
  unfold tailWord_281714
  simp only [CollatzResearch.WordTrace]
  refine ⟨2568738425351441441461049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6849969134270510510562797 2568738425351441441461049)
  ·
    refine ⟨1926553819013581081095787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2568738425351441441461049 1926553819013581081095787)
    ·
      refine ⟨2889830728520371621643681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1926553819013581081095787 2889830728520371621643681)
      ·
        refine ⟨2167373046390278716232761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2889830728520371621643681 2167373046390278716232761)
        ·
          refine ⟨1625529784792709037174571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2167373046390278716232761 1625529784792709037174571)
          ·
            refine ⟨2438294677189063555761857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1625529784792709037174571 2438294677189063555761857)
            ·
              refine ⟨1828721007891797666821393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2438294677189063555761857 1828721007891797666821393)
              ·
                refine ⟨1371540755918848250116045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1828721007891797666821393 1371540755918848250116045)
                ·
                  refine ⟨514327783469568093793517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1371540755918848250116045 514327783469568093793517)
                  ·
                    refine ⟨192872918801088035172569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 514327783469568093793517 192872918801088035172569)
                    ·
                      refine ⟨144654689100816026379427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 192872918801088035172569 144654689100816026379427)
                      ·
                        rfl

theorem cell23_281714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_281714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281714 prefixEnd_281714 := by exact prefixLift 281714
  have htrace : WordTrace (prefixWord ++ tailWord_281714) baseStart_281714 baseEnd_281714 := by
    simpa [prefixWord, tailWord_281714, baseEnd_281714] using wordTrace_append hprefix tailTrace_281714
  have hstable : (prefixWord ++ tailWord_281714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281714).length < 2 ^ (prefixWord ++ tailWord_281714).sum := by decide
  have hdescent : baseEnd_281714 < baseStart_281714 := by decide
  rcases family_descends (prefixWord ++ tailWord_281714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281720 : List Nat := [2, 1, 2, 1, 1, 1, 4, 3, 2, 6]
def baseStart_281720 : Nat := 118140960795 + 281720 * 2 ^ 59
def prefixEnd_281720 : Nat := 4983230072969 + 3 ^ 40 * 281720 * 2
def baseEnd_281720 : Nat := 48219256661581000968133

theorem tailTrace_281720 : CollatzResearch.WordTrace tailWord_281720 prefixEnd_281720 48219256661581000968133 := by
  unfold tailWord_281720
  simp only [CollatzResearch.WordTrace]
  refine ⟨5137586269692014395281307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6850115026256019193708409 5137586269692014395281307)
  ·
    refine ⟨7706379404538021592921961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5137586269692014395281307 7706379404538021592921961)
    ·
      refine ⟨5779784553403516194691471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7706379404538021592921961 5779784553403516194691471)
      ·
        refine ⟨8669676830105274292037207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5779784553403516194691471 8669676830105274292037207)
        ·
          refine ⟨13004515245157911438055811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8669676830105274292037207 13004515245157911438055811)
          ·
            refine ⟨19506772867736867157083717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13004515245157911438055811 19506772867736867157083717)
            ·
              refine ⟨3657519912700662591953197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19506772867736867157083717 3657519912700662591953197)
              ·
                refine ⟨1371569967262748471982449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3657519912700662591953197 1371569967262748471982449)
                ·
                  refine ⟨1028677475447061353986837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1371569967262748471982449 1028677475447061353986837)
                  ·
                    refine ⟨48219256661581000968133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1028677475447061353986837 48219256661581000968133)
                    ·
                      rfl

theorem cell23_281720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 2, 6].length) (baseStart_281720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281720 prefixEnd_281720 := by exact prefixLift 281720
  have htrace : WordTrace (prefixWord ++ tailWord_281720) baseStart_281720 baseEnd_281720 := by
    simpa [prefixWord, tailWord_281720, baseEnd_281720] using wordTrace_append hprefix tailTrace_281720
  have hstable : (prefixWord ++ tailWord_281720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281720).length < 2 ^ (prefixWord ++ tailWord_281720).sum := by decide
  have hdescent : baseEnd_281720 < baseStart_281720 := by decide
  rcases family_descends (prefixWord ++ tailWord_281720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281721 : List Nat := [1, 2, 1, 3, 5, 1, 1, 3, 2, 1, 3]
def baseStart_281721 : Nat := 118140960795 + 281721 * 2 ^ 59
def prefixEnd_281721 : Nat := 4983230072969 + 3 ^ 40 * 281721 * 2
def baseEnd_281721 : Nat := 144658283465397498991895

theorem tailTrace_281721 : CollatzResearch.WordTrace tailWord_281721 prefixEnd_281721 144658283465397498991895 := by
  unfold tailWord_281721
  simp only [CollatzResearch.WordTrace]
  refine ⟨10275209012380405961349017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6850139341586937307566011 10275209012380405961349017)
  ·
    refine ⟨7706406759285304471011763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10275209012380405961349017 7706406759285304471011763)
    ·
      refine ⟨11559610138927956706517645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7706406759285304471011763 11559610138927956706517645)
      ·
        refine ⟨4334853802097983764944117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11559610138927956706517645 4334853802097983764944117)
        ·
          refine ⟨406392543946685977963511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4334853802097983764944117 406392543946685977963511)
          ·
            refine ⟨609588815920028966945267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406392543946685977963511 609588815920028966945267)
            ·
              refine ⟨914383223880043450417901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 609588815920028966945267 914383223880043450417901)
              ·
                refine ⟨342893708955016293906713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 914383223880043450417901 342893708955016293906713)
                ·
                  refine ⟨257170281716262220430035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 342893708955016293906713 257170281716262220430035)
                  ·
                    refine ⟨385755422574393330645053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 257170281716262220430035 385755422574393330645053)
                    ·
                      refine ⟨144658283465397498991895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 385755422574393330645053 144658283465397498991895)
                      ·
                        rfl

theorem cell23_281721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_281721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281721 prefixEnd_281721 := by exact prefixLift 281721
  have htrace : WordTrace (prefixWord ++ tailWord_281721) baseStart_281721 baseEnd_281721 := by
    simpa [prefixWord, tailWord_281721, baseEnd_281721] using wordTrace_append hprefix tailTrace_281721
  have hstable : (prefixWord ++ tailWord_281721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281721).length < 2 ^ (prefixWord ++ tailWord_281721).sum := by decide
  have hdescent : baseEnd_281721 < baseStart_281721 := by decide
  rcases family_descends (prefixWord ++ tailWord_281721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281727 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 7, 4, 2]
def baseStart_281727 : Nat := 118140960795 + 281727 * 2 ^ 59
def prefixEnd_281727 : Nat := 4983230072969 + 3 ^ 40 * 281727 * 2
def baseEnd_281727 : Nat := 144661364349324475516867

theorem tailTrace_281727 : CollatzResearch.WordTrace tailWord_281727 prefixEnd_281727 144661364349324475516867 := by
  unfold tailWord_281727
  simp only [CollatzResearch.WordTrace]
  refine ⟨10275427850358668986067435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6850285233572445990711623 10275427850358668986067435)
  ·
    refine ⟨15413141775538003479101153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10275427850358668986067435 15413141775538003479101153)
    ·
      refine ⟨11559856331653502609325865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15413141775538003479101153 11559856331653502609325865)
      ·
        refine ⟨8669892248740126956994399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11559856331653502609325865 8669892248740126956994399)
        ·
          refine ⟨13004838373110190435491599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8669892248740126956994399 13004838373110190435491599)
          ·
            refine ⟨19507257559665285653237399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13004838373110190435491599 19507257559665285653237399)
            ·
              refine ⟨29260886339497928479856099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19507257559665285653237399 29260886339497928479856099)
              ·
                refine ⟨43891329509246892719784149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29260886339497928479856099 43891329509246892719784149)
                ·
                  refine ⟨1028703035372974048119941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 43891329509246892719784149 1028703035372974048119941)
                  ·
                    refine ⟨192881819132432634022489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1028703035372974048119941 192881819132432634022489)
                    ·
                      refine ⟨144661364349324475516867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 192881819132432634022489 144661364349324475516867)
                      ·
                        rfl

theorem cell23_281727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 4, 2].length) (baseStart_281727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281727 prefixEnd_281727 := by exact prefixLift 281727
  have htrace : WordTrace (prefixWord ++ tailWord_281727) baseStart_281727 baseEnd_281727 := by
    simpa [prefixWord, tailWord_281727, baseEnd_281727] using wordTrace_append hprefix tailTrace_281727
  have hstable : (prefixWord ++ tailWord_281727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281727).length < 2 ^ (prefixWord ++ tailWord_281727).sum := by decide
  have hdescent : baseEnd_281727 < baseStart_281727 := by decide
  rcases family_descends (prefixWord ++ tailWord_281727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281744 : List Nat := [2, 1, 1, 1, 1, 1, 4, 4, 4, 2, 2]
def baseStart_281744 : Nat := 118140960795 + 281744 * 2 ^ 59
def prefixEnd_281744 : Nat := 4983230072969 + 3 ^ 40 * 281744 * 2
def baseEnd_281744 : Nat := 144670093520450909004289

theorem tailTrace_281744 : CollatzResearch.WordTrace tailWord_281744 prefixEnd_281744 144670093520450909004289 := by
  unfold tailWord_281744
  simp only [CollatzResearch.WordTrace]
  refine ⟨5138023945648540444718143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6850698594198053926290857 5138023945648540444718143)
  ·
    refine ⟨7707035918472810667077215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5138023945648540444718143 7707035918472810667077215)
    ·
      refine ⟨11560553877709216000615823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7707035918472810667077215 11560553877709216000615823)
      ·
        refine ⟨17340830816563824000923735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11560553877709216000615823 17340830816563824000923735)
        ·
          refine ⟨26011246224845736001385603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17340830816563824000923735 26011246224845736001385603)
          ·
            refine ⟨39016869337268604002078405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26011246224845736001385603 39016869337268604002078405)
            ·
              refine ⟨7315663000737863250389701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39016869337268604002078405 7315663000737863250389701)
              ·
                refine ⟨1371686812638349359448069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7315663000737863250389701 1371686812638349359448069)
                ·
                  refine ⟨257191277369690504896513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1371686812638349359448069 257191277369690504896513)
                  ·
                    refine ⟨192893458027267878672385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 257191277369690504896513 192893458027267878672385)
                    ·
                      refine ⟨144670093520450909004289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 192893458027267878672385 144670093520450909004289)
                      ·
                        rfl

theorem cell23_281744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 4, 2, 2].length) (baseStart_281744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281744 prefixEnd_281744 := by exact prefixLift 281744
  have htrace : WordTrace (prefixWord ++ tailWord_281744) baseStart_281744 baseEnd_281744 := by
    simpa [prefixWord, tailWord_281744, baseEnd_281744] using wordTrace_append hprefix tailTrace_281744
  have hstable : (prefixWord ++ tailWord_281744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281744).length < 2 ^ (prefixWord ++ tailWord_281744).sum := by decide
  have hdescent : baseEnd_281744 < baseStart_281744 := by decide
  rcases family_descends (prefixWord ++ tailWord_281744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281757 : List Nat := [1, 4, 2, 1, 1, 2, 2, 2, 2, 2, 4]
def baseStart_281757 : Nat := 118140960795 + 281757 * 2 ^ 59
def prefixEnd_281757 : Nat := 4983230072969 + 3 ^ 40 * 281757 * 2
def baseEnd_281757 : Nat := 144676768768959358141729

theorem tailTrace_281757 : CollatzResearch.WordTrace tailWord_281757 prefixEnd_281757 144676768768959358141729 := by
  unfold tailWord_281757
  simp only [CollatzResearch.WordTrace]
  refine ⟨10276522040249984109659525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6851014693499989406439683 10276522040249984109659525)
  ·
    refine ⟨1926847882546872020561161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10276522040249984109659525 1926847882546872020561161)
    ·
      refine ⟨1445135911910154015420871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1926847882546872020561161 1445135911910154015420871)
      ·
        refine ⟨2167703867865231023131307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1445135911910154015420871 2167703867865231023131307)
        ·
          refine ⟨3251555801797846534696961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2167703867865231023131307 3251555801797846534696961)
          ·
            refine ⟨2438666851348384901022721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3251555801797846534696961 2438666851348384901022721)
            ·
              refine ⟨1829000138511288675767041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2438666851348384901022721 1829000138511288675767041)
              ·
                refine ⟨1371750103883466506825281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1829000138511288675767041 1371750103883466506825281)
                ·
                  refine ⟨1028812577912599880118961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1371750103883466506825281 1028812577912599880118961)
                  ·
                    refine ⟨771609433434449910089221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1028812577912599880118961 771609433434449910089221)
                    ·
                      refine ⟨144676768768959358141729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 771609433434449910089221 144676768768959358141729)
                      ·
                        rfl

theorem cell23_281757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_281757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281757 prefixEnd_281757 := by exact prefixLift 281757
  have htrace : WordTrace (prefixWord ++ tailWord_281757) baseStart_281757 baseEnd_281757 := by
    simpa [prefixWord, tailWord_281757, baseEnd_281757] using wordTrace_append hprefix tailTrace_281757
  have hstable : (prefixWord ++ tailWord_281757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281757).length < 2 ^ (prefixWord ++ tailWord_281757).sum := by decide
  have hdescent : baseEnd_281757 < baseStart_281757 := by decide
  rcases family_descends (prefixWord ++ tailWord_281757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281812 : List Nat := [2, 4, 1, 4, 1, 2, 1, 2, 2, 2, 2]
def baseStart_281812 : Nat := 118140960795 + 281812 * 2 ^ 59
def prefixEnd_281812 : Nat := 4983230072969 + 3 ^ 40 * 281812 * 2
def baseEnd_281812 : Nat := 144705010204956642953977

theorem tailTrace_281812 : CollatzResearch.WordTrace tailWord_281812 prefixEnd_281812 144705010204956642953977 := by
  unfold tailWord_281812
  simp only [CollatzResearch.WordTrace]
  refine ⟨5139264027525364251455845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6852352036700485668607793 5139264027525364251455845)
  ·
    refine ⟨963612005161005797147971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5139264027525364251455845 963612005161005797147971)
    ·
      refine ⟨1445418007741508695721957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 963612005161005797147971 1445418007741508695721957)
      ·
        refine ⟨271015876451532880447867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1445418007741508695721957 271015876451532880447867)
        ·
          refine ⟨406523814677299320671801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271015876451532880447867 406523814677299320671801)
          ·
            refine ⟨304892861007974490503851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 406523814677299320671801 304892861007974490503851)
            ·
              refine ⟨457339291511961735755777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304892861007974490503851 457339291511961735755777)
              ·
                refine ⟨343004468633971301816833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 457339291511961735755777 343004468633971301816833)
                ·
                  refine ⟨257253351475478476362625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 343004468633971301816833 257253351475478476362625)
                  ·
                    refine ⟨192940013606608857271969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 257253351475478476362625 192940013606608857271969)
                    ·
                      refine ⟨144705010204956642953977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 192940013606608857271969 144705010204956642953977)
                      ·
                        rfl

theorem cell23_281812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_281812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281812 prefixEnd_281812 := by exact prefixLift 281812
  have htrace : WordTrace (prefixWord ++ tailWord_281812) baseStart_281812 baseEnd_281812 := by
    simpa [prefixWord, tailWord_281812, baseEnd_281812] using wordTrace_append hprefix tailTrace_281812
  have hstable : (prefixWord ++ tailWord_281812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281812).length < 2 ^ (prefixWord ++ tailWord_281812).sum := by decide
  have hdescent : baseEnd_281812 < baseStart_281812 := by decide
  rcases family_descends (prefixWord ++ tailWord_281812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281817 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 4, 1, 4]
def baseStart_281817 : Nat := 118140960795 + 281817 * 2 ^ 59
def prefixEnd_281817 : Nat := 4983230072969 + 3 ^ 40 * 281817 * 2
def baseEnd_281817 : Nat := 144707577608229123391453

theorem tailTrace_281817 : CollatzResearch.WordTrace tailWord_281817 prefixEnd_281817 144707577608229123391453 := by
  unfold tailWord_281817
  simp only [CollatzResearch.WordTrace]
  refine ⟨10278710420032614356843705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6852473613355076237895803 10278710420032614356843705)
  ·
    refine ⟨7709032815024460767632779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10278710420032614356843705 7709032815024460767632779)
    ·
      refine ⟨11563549222536691151449169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7709032815024460767632779 11563549222536691151449169)
      ·
        refine ⟨8672661916902518363586877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11563549222536691151449169 8672661916902518363586877)
        ·
          refine ⟨3252248218838444386345079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8672661916902518363586877 3252248218838444386345079)
          ·
            refine ⟨4878372328257666579517619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3252248218838444386345079 4878372328257666579517619)
            ·
              refine ⟨7317558492386499869276429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4878372328257666579517619 7317558492386499869276429)
              ·
                refine ⟨2744084434644937450978661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7317558492386499869276429 2744084434644937450978661)
                ·
                  refine ⟨514515831495925772058499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2744084434644937450978661 514515831495925772058499)
                  ·
                    refine ⟨771773747243888658087749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 514515831495925772058499 771773747243888658087749)
                    ·
                      refine ⟨144707577608229123391453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 771773747243888658087749 144707577608229123391453)
                      ·
                        rfl

theorem cell23_281817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_281817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281817 prefixEnd_281817 := by exact prefixLift 281817
  have htrace : WordTrace (prefixWord ++ tailWord_281817) baseStart_281817 baseEnd_281817 := by
    simpa [prefixWord, tailWord_281817, baseEnd_281817] using wordTrace_append hprefix tailTrace_281817
  have hstable : (prefixWord ++ tailWord_281817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281817).length < 2 ^ (prefixWord ++ tailWord_281817).sum := by decide
  have hdescent : baseEnd_281817 < baseStart_281817 := by decide
  rcases family_descends (prefixWord ++ tailWord_281817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281857 : List Nat := [1, 2, 4, 1, 1, 3, 1, 2, 8]
def baseStart_281857 : Nat := 118140960795 + 281857 * 2 ^ 59
def prefixEnd_281857 : Nat := 4983230072969 + 3 ^ 40 * 281857 * 2
def baseEnd_281857 : Nat := 16080901870489885210141

theorem tailTrace_281857 : CollatzResearch.WordTrace tailWord_281857 prefixEnd_281857 16080901870489885210141 := by
  unfold tailWord_281857
  simp only [CollatzResearch.WordTrace]
  refine ⟨10280169339887701188299825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6853446226591800792199883 10280169339887701188299825)
  ·
    refine ⟨7710127004915775891224869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10280169339887701188299825 7710127004915775891224869)
    ·
      refine ⟨1445648813421707979604663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7710127004915775891224869 1445648813421707979604663)
      ·
        refine ⟨2168473220132561969406995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1445648813421707979604663 2168473220132561969406995)
        ·
          refine ⟨3252709830198842954110493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2168473220132561969406995 3252709830198842954110493)
          ·
            refine ⟨1219766186324566107791435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3252709830198842954110493 1219766186324566107791435)
            ·
              refine ⟨1829649279486849161687153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1219766186324566107791435 1829649279486849161687153)
              ·
                refine ⟨1372236959615136871265365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1829649279486849161687153 1372236959615136871265365)
                ·
                  refine ⟨16080901870489885210141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1372236959615136871265365 16080901870489885210141)
                  ·
                    rfl

theorem cell23_281857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 8].length) (baseStart_281857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281857 prefixEnd_281857 := by exact prefixLift 281857
  have htrace : WordTrace (prefixWord ++ tailWord_281857) baseStart_281857 baseEnd_281857 := by
    simpa [prefixWord, tailWord_281857, baseEnd_281857] using wordTrace_append hprefix tailTrace_281857
  have hstable : (prefixWord ++ tailWord_281857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281857).length < 2 ^ (prefixWord ++ tailWord_281857).sum := by decide
  have hdescent : baseEnd_281857 < baseStart_281857 := by decide
  rcases family_descends (prefixWord ++ tailWord_281857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281891 : List Nat := [1, 1, 1, 4, 2, 5, 2, 1, 6]
def baseStart_281891 : Nat := 118140960795 + 281891 * 2 ^ 59
def prefixEnd_281891 : Nat := 4983230072969 + 3 ^ 40 * 281891 * 2
def baseEnd_281891 : Nat := 16082841686295759318457

theorem tailTrace_281891 : CollatzResearch.WordTrace tailWord_281891 prefixEnd_281891 16082841686295759318457 := by
  unfold tailWord_281891
  simp only [CollatzResearch.WordTrace]
  refine ⟨10281409421764524995037527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6854272947843016663358351 10281409421764524995037527)
  ·
    refine ⟨15422114132646787492556291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10281409421764524995037527 15422114132646787492556291)
    ·
      refine ⟨23133171198970181238834437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15422114132646787492556291 23133171198970181238834437)
      ·
        refine ⟨4337469599806908982281457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23133171198970181238834437 4337469599806908982281457)
        ·
          refine ⟨3253102199855181736711093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4337469599806908982281457 3253102199855181736711093)
          ·
            refine ⟨304978331236423287816665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3253102199855181736711093 304978331236423287816665)
            ·
              refine ⟨228733748427317465862499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304978331236423287816665 228733748427317465862499)
              ·
                refine ⟨343100622640976198793749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 228733748427317465862499 343100622640976198793749)
                ·
                  refine ⟨16082841686295759318457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 343100622640976198793749 16082841686295759318457)
                  ·
                    rfl

theorem cell23_281891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 6].length) (baseStart_281891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281891 prefixEnd_281891 := by exact prefixLift 281891
  have htrace : WordTrace (prefixWord ++ tailWord_281891) baseStart_281891 baseEnd_281891 := by
    simpa [prefixWord, tailWord_281891, baseEnd_281891] using wordTrace_append hprefix tailTrace_281891
  have hstable : (prefixWord ++ tailWord_281891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281891).length < 2 ^ (prefixWord ++ tailWord_281891).sum := by decide
  have hdescent : baseEnd_281891 < baseStart_281891 := by decide
  rcases family_descends (prefixWord ++ tailWord_281891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281944 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 5, 2, 3]
def baseStart_281944 : Nat := 118140960795 + 281944 * 2 ^ 59
def prefixEnd_281944 : Nat := 4983230072969 + 3 ^ 40 * 281944 * 2
def baseEnd_281944 : Nat := 144772789651350126503369

theorem tailTrace_281944 : CollatzResearch.WordTrace tailWord_281944 prefixEnd_281944 144772789651350126503369 := by
  unfold tailWord_281944
  simp only [CollatzResearch.WordTrace]
  refine ⟨5141671245286257523358443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6855561660381676697811257 5141671245286257523358443)
  ·
    refine ⟨7712506867929386285037665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5141671245286257523358443 7712506867929386285037665)
    ·
      refine ⟨5784380150947039713778249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7712506867929386285037665 5784380150947039713778249)
      ·
        refine ⟨4338285113210279785333687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5784380150947039713778249 4338285113210279785333687)
        ·
          refine ⟨6507427669815419678000531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4338285113210279785333687 6507427669815419678000531)
          ·
            refine ⟨9761141504723129517000797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6507427669815419678000531 9761141504723129517000797)
            ·
              refine ⟨3660428064271173568875299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9761141504723129517000797 3660428064271173568875299)
              ·
                refine ⟨5490642096406760353312949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3660428064271173568875299 5490642096406760353312949)
                ·
                  refine ⟨514747696538133783123089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5490642096406760353312949 514747696538133783123089)
                  ·
                    refine ⟨386060772403600337342317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 514747696538133783123089 386060772403600337342317)
                    ·
                      refine ⟨144772789651350126503369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 386060772403600337342317 144772789651350126503369)
                      ·
                        rfl

theorem cell23_281944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_281944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281944 prefixEnd_281944 := by exact prefixLift 281944
  have htrace : WordTrace (prefixWord ++ tailWord_281944) baseStart_281944 baseEnd_281944 := by
    simpa [prefixWord, tailWord_281944, baseEnd_281944] using wordTrace_append hprefix tailTrace_281944
  have hstable : (prefixWord ++ tailWord_281944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281944).length < 2 ^ (prefixWord ++ tailWord_281944).sum := by decide
  have hdescent : baseEnd_281944 < baseStart_281944 := by decide
  rcases family_descends (prefixWord ++ tailWord_281944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281962 : List Nat := [3, 1, 3, 3, 3, 1, 1, 1, 2, 3, 2]
def baseStart_281962 : Nat := 118140960795 + 281962 * 2 ^ 59
def prefixEnd_281962 : Nat := 4983230072969 + 3 ^ 40 * 281962 * 2
def baseEnd_281962 : Nat := 144782032303131056078287

theorem tailTrace_281962 : CollatzResearch.WordTrace tailWord_281962 prefixEnd_281962 144782032303131056078287 := by
  unfold tailWord_281962
  simp only [CollatzResearch.WordTrace]
  refine ⟨2570999751126826030218035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6855999336338202747248093 2570999751126826030218035)
  ·
    refine ⟨3856499626690239045327053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2570999751126826030218035 3856499626690239045327053)
    ·
      refine ⟨1446187360008839641997645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3856499626690239045327053 1446187360008839641997645)
      ·
        refine ⟨542320260003314865749117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1446187360008839641997645 542320260003314865749117)
        ·
          refine ⟨203370097501243074655919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 542320260003314865749117 203370097501243074655919)
          ·
            refine ⟨305055146251864611983879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203370097501243074655919 305055146251864611983879)
            ·
              refine ⟨457582719377796917975819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305055146251864611983879 457582719377796917975819)
              ·
                refine ⟨686374079066695376963729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 457582719377796917975819 686374079066695376963729)
                ·
                  refine ⟨514780559300021532722797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 686374079066695376963729 514780559300021532722797)
                  ·
                    refine ⟨193042709737508074771049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 514780559300021532722797 193042709737508074771049)
                    ·
                      refine ⟨144782032303131056078287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 193042709737508074771049 144782032303131056078287)
                      ·
                        rfl

theorem cell23_281962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_281962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281962 prefixEnd_281962 := by exact prefixLift 281962
  have htrace : WordTrace (prefixWord ++ tailWord_281962) baseStart_281962 baseEnd_281962 := by
    simpa [prefixWord, tailWord_281962, baseEnd_281962] using wordTrace_append hprefix tailTrace_281962
  have hstable : (prefixWord ++ tailWord_281962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281962).length < 2 ^ (prefixWord ++ tailWord_281962).sum := by decide
  have hdescent : baseEnd_281962 < baseStart_281962 := by decide
  rcases family_descends (prefixWord ++ tailWord_281962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281975 : List Nat := [1, 1, 3, 1, 1, 2, 6, 3, 1, 2, 2]
def baseStart_281975 : Nat := 118140960795 + 281975 * 2 ^ 59
def prefixEnd_281975 : Nat := 4983230072969 + 3 ^ 40 * 281975 * 2
def baseEnd_281975 : Nat := 144788707551639505215727

theorem tailTrace_281975 : CollatzResearch.WordTrace tailWord_281975 prefixEnd_281975 144788707551639505215727 := by
  unfold tailWord_281975
  simp only [CollatzResearch.WordTrace]
  refine ⟨10284473153460207341095379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6856315435640138227396919 10284473153460207341095379)
  ·
    refine ⟨15426709730190311011643069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10284473153460207341095379 15426709730190311011643069)
    ·
      refine ⟨5785016148821366629366151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15426709730190311011643069 5785016148821366629366151)
      ·
        refine ⟨8677524223232049944049227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5785016148821366629366151 8677524223232049944049227)
        ·
          refine ⟨13016286334848074916073841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8677524223232049944049227 13016286334848074916073841)
          ·
            refine ⟨9762214751136056187055381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13016286334848074916073841 9762214751136056187055381)
            ·
              refine ⟨457603816459502633768221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9762214751136056187055381 457603816459502633768221)
              ·
                refine ⟨171601431172313487663083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 457603816459502633768221 171601431172313487663083)
                ·
                  refine ⟨257402146758470231494625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171601431172313487663083 257402146758470231494625)
                  ·
                    refine ⟨193051610068852673620969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 257402146758470231494625 193051610068852673620969)
                    ·
                      refine ⟨144788707551639505215727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 193051610068852673620969 144788707551639505215727)
                      ·
                        rfl

theorem cell23_281975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 3, 1, 2, 2].length) (baseStart_281975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281975 prefixEnd_281975 := by exact prefixLift 281975
  have htrace : WordTrace (prefixWord ++ tailWord_281975) baseStart_281975 baseEnd_281975 := by
    simpa [prefixWord, tailWord_281975, baseEnd_281975] using wordTrace_append hprefix tailTrace_281975
  have hstable : (prefixWord ++ tailWord_281975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281975).length < 2 ^ (prefixWord ++ tailWord_281975).sum := by decide
  have hdescent : baseEnd_281975 < baseStart_281975 := by decide
  rcases family_descends (prefixWord ++ tailWord_281975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281985 : List Nat := [1, 2, 4, 3, 2, 2, 1, 2, 2, 4]
def baseStart_281985 : Nat := 118140960795 + 281985 * 2 ^ 59
def prefixEnd_281985 : Nat := 4983230072969 + 3 ^ 40 * 281985 * 2
def baseEnd_281985 : Nat := 48264614119394822030227

theorem tailTrace_281985 : CollatzResearch.WordTrace tailWord_281985 prefixEnd_281985 48264614119394822030227 := by
  unfold tailWord_281985
  simp only [CollatzResearch.WordTrace]
  refine ⟨10284837883423979048959409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6856558588949319365972939 10284837883423979048959409)
  ·
    refine ⟨7713628412567984286719557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10284837883423979048959409 7713628412567984286719557)
    ·
      refine ⟨1446305327356497053759917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7713628412567984286719557 1446305327356497053759917)
      ·
        refine ⟨542364497758686395159969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1446305327356497053759917 542364497758686395159969)
        ·
          refine ⟨406773373319014796369977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 542364497758686395159969 406773373319014796369977)
          ·
            refine ⟨305080029989261097277483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 406773373319014796369977 305080029989261097277483)
            ·
              refine ⟨457620044983891645916225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305080029989261097277483 457620044983891645916225)
              ·
                refine ⟨343215033737918734437169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 457620044983891645916225 343215033737918734437169)
                ·
                  refine ⟨257411275303439050827877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 343215033737918734437169 257411275303439050827877)
                  ·
                    refine ⟨48264614119394822030227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 257411275303439050827877 48264614119394822030227)
                    ·
                      rfl

theorem cell23_281985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_281985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_281985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_281985 prefixEnd_281985 := by exact prefixLift 281985
  have htrace : WordTrace (prefixWord ++ tailWord_281985) baseStart_281985 baseEnd_281985 := by
    simpa [prefixWord, tailWord_281985, baseEnd_281985] using wordTrace_append hprefix tailTrace_281985
  have hstable : (prefixWord ++ tailWord_281985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281985).length < 2 ^ (prefixWord ++ tailWord_281985).sum := by decide
  have hdescent : baseEnd_281985 < baseStart_281985 := by decide
  rcases family_descends (prefixWord ++ tailWord_281985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282002 : List Nat := [3, 2, 3, 3, 1, 1, 3, 1, 2, 4]
def baseStart_282002 : Nat := 118140960795 + 282002 * 2 ^ 59
def prefixEnd_282002 : Nat := 4983230072969 + 3 ^ 40 * 282002 * 2
def baseEnd_282002 : Nat := 48267523843103633192701

theorem tailTrace_282002 : CollatzResearch.WordTrace tailWord_282002 prefixEnd_282002 48267523843103633192701 := by
  unfold tailWord_282002
  simp only [CollatzResearch.WordTrace]
  refine ⟨2571364481090597738082065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6856971949574927301552173 2571364481090597738082065)
  ·
    refine ⟨1928523360817948303561549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2571364481090597738082065 1928523360817948303561549)
    ·
      refine ⟨723196260306730613835581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1928523360817948303561549 723196260306730613835581)
      ·
        refine ⟨271198597615023980188343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 723196260306730613835581 271198597615023980188343)
        ·
          refine ⟨406797896422535970282515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271198597615023980188343 406797896422535970282515)
          ·
            refine ⟨610196844633803955423773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406797896422535970282515 610196844633803955423773)
            ·
              refine ⟨228823816737676483283915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 610196844633803955423773 228823816737676483283915)
              ·
                refine ⟨343235725106514724925873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 228823816737676483283915 343235725106514724925873)
                ·
                  refine ⟨257426793829886043694405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 343235725106514724925873 257426793829886043694405)
                  ·
                    refine ⟨48267523843103633192701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 257426793829886043694405 48267523843103633192701)
                    ·
                      rfl

theorem cell23_282002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_282002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282002 prefixEnd_282002 := by exact prefixLift 282002
  have htrace : WordTrace (prefixWord ++ tailWord_282002) baseStart_282002 baseEnd_282002 := by
    simpa [prefixWord, tailWord_282002, baseEnd_282002] using wordTrace_append hprefix tailTrace_282002
  have hstable : (prefixWord ++ tailWord_282002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282002).length < 2 ^ (prefixWord ++ tailWord_282002).sum := by decide
  have hdescent : baseEnd_282002 < baseStart_282002 := by decide
  rcases family_descends (prefixWord ++ tailWord_282002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282031 : List Nat := [1, 1, 2, 1, 2, 2, 1, 6, 1, 4, 2]
def baseStart_282031 : Nat := 118140960795 + 282031 * 2 ^ 59
def prefixEnd_282031 : Nat := 4983230072969 + 3 ^ 40 * 282031 * 2
def baseEnd_282031 : Nat := 144817462468291286115469

theorem tailTrace_282031 : CollatzResearch.WordTrace tailWord_282031 prefixEnd_282031 144817462468291286115469 := by
  unfold tailWord_282031
  simp only [CollatzResearch.WordTrace]
  refine ⟨10286515641257328905133947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6857677094171552603422631 10286515641257328905133947)
  ·
    refine ⟨15429773461885993357700921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10286515641257328905133947 15429773461885993357700921)
    ·
      refine ⟨11572330096414495018275691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15429773461885993357700921 11572330096414495018275691)
      ·
        refine ⟨17358495144621742527413537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11572330096414495018275691 17358495144621742527413537)
        ·
          refine ⟨13018871358466306895560153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17358495144621742527413537 13018871358466306895560153)
          ·
            refine ⟨9764153518849730171670115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13018871358466306895560153 9764153518849730171670115)
            ·
              refine ⟨14646230278274595257505173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9764153518849730171670115 14646230278274595257505173)
              ·
                refine ⟨686542044294121652695555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14646230278274595257505173 686542044294121652695555)
                ·
                  refine ⟨1029813066441182479043333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 686542044294121652695555 1029813066441182479043333)
                  ·
                    refine ⟨193089949957721714820625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1029813066441182479043333 193089949957721714820625)
                    ·
                      refine ⟨144817462468291286115469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 193089949957721714820625 144817462468291286115469)
                      ·
                        rfl

theorem cell23_282031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 4, 2].length) (baseStart_282031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282031 prefixEnd_282031 := by exact prefixLift 282031
  have htrace : WordTrace (prefixWord ++ tailWord_282031) baseStart_282031 baseEnd_282031 := by
    simpa [prefixWord, tailWord_282031, baseEnd_282031] using wordTrace_append hprefix tailTrace_282031
  have hstable : (prefixWord ++ tailWord_282031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282031).length < 2 ^ (prefixWord ++ tailWord_282031).sum := by decide
  have hdescent : baseEnd_282031 < baseStart_282031 := by decide
  rcases family_descends (prefixWord ++ tailWord_282031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282048 : List Nat := [2, 1, 1, 2, 3, 1, 4, 1, 4, 2, 2]
def baseStart_282048 : Nat := 118140960795 + 282048 * 2 ^ 59
def prefixEnd_282048 : Nat := 4983230072969 + 3 ^ 40 * 282048 * 2
def baseEnd_282048 : Nat := 144826191639417719602891

theorem tailTrace_282048 : CollatzResearch.WordTrace tailWord_282048 prefixEnd_282048 144826191639417719602891 := by
  unfold tailWord_282048
  simp only [CollatzResearch.WordTrace]
  refine ⟨5143567841097870404251399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6858090454797160539001865 5143567841097870404251399)
  ·
    refine ⟨7715351761646805606377099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5143567841097870404251399 7715351761646805606377099)
    ·
      refine ⟨11573027642470208409565649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7715351761646805606377099 11573027642470208409565649)
      ·
        refine ⟨8679770731852656307174237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11573027642470208409565649 8679770731852656307174237)
        ·
          refine ⟨3254914024444746115190339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8679770731852656307174237 3254914024444746115190339)
          ·
            refine ⟨4882371036667119172785509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3254914024444746115190339 4882371036667119172785509)
            ·
              refine ⟨915444569375084844897283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4882371036667119172785509 915444569375084844897283)
              ·
                refine ⟨1373166854062627267345925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 915444569375084844897283 1373166854062627267345925)
                ·
                  refine ⟨257468785136742612627361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1373166854062627267345925 257468785136742612627361)
                  ·
                    refine ⟨193101588852556959470521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 257468785136742612627361 193101588852556959470521)
                    ·
                      refine ⟨144826191639417719602891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 193101588852556959470521 144826191639417719602891)
                      ·
                        rfl

theorem cell23_282048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 4, 2, 2].length) (baseStart_282048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282048 prefixEnd_282048 := by exact prefixLift 282048
  have htrace : WordTrace (prefixWord ++ tailWord_282048) baseStart_282048 baseEnd_282048 := by
    simpa [prefixWord, tailWord_282048, baseEnd_282048] using wordTrace_append hprefix tailTrace_282048
  have hstable : (prefixWord ++ tailWord_282048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282048).length < 2 ^ (prefixWord ++ tailWord_282048).sum := by decide
  have hdescent : baseEnd_282048 < baseStart_282048 := by decide
  rcases family_descends (prefixWord ++ tailWord_282048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282084 : List Nat := [2, 3, 1, 1, 1, 1, 1, 5, 1, 7]
def baseStart_282084 : Nat := 118140960795 + 282084 * 2 ^ 59
def prefixEnd_282084 : Nat := 4983230072969 + 3 ^ 40 * 282084 * 2
def baseEnd_282084 : Nat := 48281558980993192917575

theorem tailTrace_282084 : CollatzResearch.WordTrace tailWord_282084 prefixEnd_282084 48281558980993192917575 := by
  unfold tailWord_282084
  simp only [CollatzResearch.WordTrace]
  refine ⟨5144224355032659478406653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6858965806710212637875537 5144224355032659478406653)
  ·
    refine ⟨1929084133137247304402495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5144224355032659478406653 1929084133137247304402495)
    ·
      refine ⟨2893626199705870956603743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1929084133137247304402495 2893626199705870956603743)
      ·
        refine ⟨4340439299558806434905615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2893626199705870956603743 4340439299558806434905615)
        ·
          refine ⟨6510658949338209652358423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4340439299558806434905615 6510658949338209652358423)
          ·
            refine ⟨9765988424007314478537635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6510658949338209652358423 9765988424007314478537635)
            ·
              refine ⟨14648982636010971717806453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9765988424007314478537635 14648982636010971717806453)
              ·
                refine ⟨1373342122126028598544355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14648982636010971717806453 1373342122126028598544355)
                ·
                  refine ⟨2060013183189042897816533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1373342122126028598544355 2060013183189042897816533)
                  ·
                    refine ⟨48281558980993192917575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2060013183189042897816533 48281558980993192917575)
                    ·
                      rfl

theorem cell23_282084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_282084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282084 prefixEnd_282084 := by exact prefixLift 282084
  have htrace : WordTrace (prefixWord ++ tailWord_282084) baseStart_282084 baseEnd_282084 := by
    simpa [prefixWord, tailWord_282084, baseEnd_282084] using wordTrace_append hprefix tailTrace_282084
  have hstable : (prefixWord ++ tailWord_282084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282084).length < 2 ^ (prefixWord ++ tailWord_282084).sum := by decide
  have hdescent : baseEnd_282084 < baseStart_282084 := by decide
  rcases family_descends (prefixWord ++ tailWord_282084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282131 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 5, 4]
def baseStart_282131 : Nat := 118140960795 + 282131 * 2 ^ 59
def prefixEnd_282131 : Nat := 4983230072969 + 3 ^ 40 * 282131 * 2
def baseEnd_282131 : Nat := 48289603511246964955003

theorem tailTrace_282131 : CollatzResearch.WordTrace tailWord_282131 prefixEnd_282131 48289603511246964955003 := by
  unfold tailWord_282131
  simp only [CollatzResearch.WordTrace]
  refine ⟨10290162940895045983774247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6860108627263363989182831 10290162940895045983774247)
  ·
    refine ⟨15435244411342568975661371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10290162940895045983774247 15435244411342568975661371)
    ·
      refine ⟨23152866617013853463492057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15435244411342568975661371 23152866617013853463492057)
      ·
        refine ⟨17364649962760390097619043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23152866617013853463492057 17364649962760390097619043)
        ·
          refine ⟨26046974944140585146428565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17364649962760390097619043 26046974944140585146428565)
          ·
            refine ⟨1220951950506589928738839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 26046974944140585146428565 1220951950506589928738839)
            ·
              refine ⟨1831427925759884893108259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1220951950506589928738839 1831427925759884893108259)
              ·
                refine ⟨2747141888639827339662389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1831427925759884893108259 2747141888639827339662389)
                ·
                  refine ⟨257544552059983813093349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2747141888639827339662389 257544552059983813093349)
                  ·
                    refine ⟨48289603511246964955003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 257544552059983813093349 48289603511246964955003)
                    ·
                      rfl

theorem cell23_282131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 5, 4].length) (baseStart_282131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282131 prefixEnd_282131 := by exact prefixLift 282131
  have htrace : WordTrace (prefixWord ++ tailWord_282131) baseStart_282131 baseEnd_282131 := by
    simpa [prefixWord, tailWord_282131, baseEnd_282131] using wordTrace_append hprefix tailTrace_282131
  have hstable : (prefixWord ++ tailWord_282131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282131).length < 2 ^ (prefixWord ++ tailWord_282131).sum := by decide
  have hdescent : baseEnd_282131 < baseStart_282131 := by decide
  rcases family_descends (prefixWord ++ tailWord_282131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282165 : List Nat := [1, 3, 3, 1, 1, 3, 2, 4, 1, 4]
def baseStart_282165 : Nat := 118140960795 + 282165 * 2 ^ 59
def prefixEnd_282165 : Nat := 4983230072969 + 3 ^ 40 * 282165 * 2
def baseEnd_282165 : Nat := 48295422958664587279951

theorem tailTrace_282165 : CollatzResearch.WordTrace tailWord_282165 prefixEnd_282165 48295422958664587279951 := by
  unfold tailWord_282165
  simp only [CollatzResearch.WordTrace]
  refine ⟨10291403022771869790511949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6860935348514579860341299 10291403022771869790511949)
  ·
    refine ⟨3859276133539451171441981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10291403022771869790511949 3859276133539451171441981)
    ·
      refine ⟨1447228550077294189290743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3859276133539451171441981 1447228550077294189290743)
      ·
        refine ⟨2170842825115941283936115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1447228550077294189290743 2170842825115941283936115)
        ·
          refine ⟨3256264237673911925904173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2170842825115941283936115 3256264237673911925904173)
          ·
            refine ⟨1221099089127716972214065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3256264237673911925904173 1221099089127716972214065)
            ·
              refine ⟨915824316845787729160549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1221099089127716972214065 915824316845787729160549)
              ·
                refine ⟨171717059408585199217603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 915824316845787729160549 171717059408585199217603)
                ·
                  refine ⟨257575589112877798826405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171717059408585199217603 257575589112877798826405)
                  ·
                    refine ⟨48295422958664587279951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 257575589112877798826405 48295422958664587279951)
                    ·
                      rfl

theorem cell23_282165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_282165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282165 prefixEnd_282165 := by exact prefixLift 282165
  have htrace : WordTrace (prefixWord ++ tailWord_282165) baseStart_282165 baseEnd_282165 := by
    simpa [prefixWord, tailWord_282165, baseEnd_282165] using wordTrace_append hprefix tailTrace_282165
  have hstable : (prefixWord ++ tailWord_282165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282165).length < 2 ^ (prefixWord ++ tailWord_282165).sum := by decide
  have hdescent : baseEnd_282165 < baseStart_282165 := by decide
  rcases family_descends (prefixWord ++ tailWord_282165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282231 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 2, 6, 3]
def baseStart_282231 : Nat := 118140960795 + 282231 * 2 ^ 59
def prefixEnd_282231 : Nat := 4983230072969 + 3 ^ 40 * 282231 * 2
def baseEnd_282231 : Nat := 144920158599190503614549

theorem tailTrace_282231 : CollatzResearch.WordTrace tailWord_282231 prefixEnd_282231 144920158599190503614549 := by
  unfold tailWord_282231
  simp only [CollatzResearch.WordTrace]
  refine ⟨10293810240532763062414547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6862540160355175374943031 10293810240532763062414547)
  ·
    refine ⟨15440715360799144593621821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10293810240532763062414547 15440715360799144593621821)
    ·
      refine ⟨5790268260299679222608183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15440715360799144593621821 5790268260299679222608183)
      ·
        refine ⟨8685402390449518833912275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5790268260299679222608183 8685402390449518833912275)
        ·
          refine ⟨13028103585674278250868413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8685402390449518833912275 13028103585674278250868413)
          ·
            refine ⟨4885538844627854344075655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13028103585674278250868413 4885538844627854344075655)
            ·
              refine ⟨7328308266941781516113483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4885538844627854344075655 7328308266941781516113483)
              ·
                refine ⟨10992462400412672274170225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7328308266941781516113483 10992462400412672274170225)
                ·
                  refine ⟨8244346800309504205627669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10992462400412672274170225 8244346800309504205627669)
                  ·
                    refine ⟨386453756264508009638797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8244346800309504205627669 386453756264508009638797)
                    ·
                      refine ⟨144920158599190503614549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 386453756264508009638797 144920158599190503614549)
                      ·
                        rfl

theorem cell23_282231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 6, 3].length) (baseStart_282231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282231 prefixEnd_282231 := by exact prefixLift 282231
  have htrace : WordTrace (prefixWord ++ tailWord_282231) baseStart_282231 baseEnd_282231 := by
    simpa [prefixWord, tailWord_282231, baseEnd_282231] using wordTrace_append hprefix tailTrace_282231
  have hstable : (prefixWord ++ tailWord_282231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282231).length < 2 ^ (prefixWord ++ tailWord_282231).sum := by decide
  have hdescent : baseEnd_282231 < baseStart_282231 := by decide
  rcases family_descends (prefixWord ++ tailWord_282231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282245 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 5, 2, 2]
def baseStart_282245 : Nat := 118140960795 + 282245 * 2 ^ 59
def prefixEnd_282245 : Nat := 4983230072969 + 3 ^ 40 * 282245 * 2
def baseEnd_282245 : Nat := 144927347328353448839485

theorem tailTrace_282245 : CollatzResearch.WordTrace tailWord_282245 prefixEnd_282245 144927347328353448839485 := by
  unfold tailWord_282245
  simp only [CollatzResearch.WordTrace]
  refine ⟨10294320862482043453424189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6862880574988028968949459 10294320862482043453424189)
  ·
    refine ⟨3860370323430766295034071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10294320862482043453424189 3860370323430766295034071)
    ·
      refine ⟨5790555485146149442551107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3860370323430766295034071 5790555485146149442551107)
      ·
        refine ⟨8685833227719224163826661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5790555485146149442551107 8685833227719224163826661)
        ·
          refine ⟨1628593730197354530717499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8685833227719224163826661 1628593730197354530717499)
          ·
            refine ⟨2442890595296031796076249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1628593730197354530717499 2442890595296031796076249)
            ·
              refine ⟨1832167946472023847057187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2442890595296031796076249 1832167946472023847057187)
              ·
                refine ⟨2748251919708035770585781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1832167946472023847057187 2748251919708035770585781)
                ·
                  refine ⟨257648617472628353492417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2748251919708035770585781 257648617472628353492417)
                  ·
                    refine ⟨193236463104471265119313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 257648617472628353492417 193236463104471265119313)
                    ·
                      refine ⟨144927347328353448839485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 193236463104471265119313 144927347328353448839485)
                      ·
                        rfl

theorem cell23_282245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 5, 2, 2].length) (baseStart_282245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282245 prefixEnd_282245 := by exact prefixLift 282245
  have htrace : WordTrace (prefixWord ++ tailWord_282245) baseStart_282245 baseEnd_282245 := by
    simpa [prefixWord, tailWord_282245, baseEnd_282245] using wordTrace_append hprefix tailTrace_282245
  have hstable : (prefixWord ++ tailWord_282245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282245).length < 2 ^ (prefixWord ++ tailWord_282245).sum := by decide
  have hdescent : baseEnd_282245 < baseStart_282245 := by decide
  rcases family_descends (prefixWord ++ tailWord_282245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282268 : List Nat := [2, 2, 3, 2, 4, 10]
def baseStart_282268 : Nat := 118140960795 + 282268 * 2 ^ 59
def prefixEnd_282268 : Nat := 4983230072969 + 3 ^ 40 * 282268 * 2
def baseEnd_282268 : Nat := 596457437791797773053

theorem tailTrace_282268 : CollatzResearch.WordTrace tailWord_282268 prefixEnd_282268 596457437791797773053 := by
  unfold tailWord_282268
  simp only [CollatzResearch.WordTrace]
  refine ⟨5147579870699359190755729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6863439827599145587674305 5147579870699359190755729)
  ·
    refine ⟨3860684903024519393066797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5147579870699359190755729 3860684903024519393066797)
    ·
      refine ⟨1447756838634194772400049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3860684903024519393066797 1447756838634194772400049)
      ·
        refine ⟨1085817628975646079300037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1447756838634194772400049 1085817628975646079300037)
        ·
          refine ⟨203590805432933639868757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1085817628975646079300037 203590805432933639868757)
          ·
            refine ⟨596457437791797773053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 203590805432933639868757 596457437791797773053)
            ·
              rfl

theorem cell23_282268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 10].length) (baseStart_282268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282268 prefixEnd_282268 := by exact prefixLift 282268
  have htrace : WordTrace (prefixWord ++ tailWord_282268) baseStart_282268 baseEnd_282268 := by
    simpa [prefixWord, tailWord_282268, baseEnd_282268] using wordTrace_append hprefix tailTrace_282268
  have hstable : (prefixWord ++ tailWord_282268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282268).length < 2 ^ (prefixWord ++ tailWord_282268).sum := by decide
  have hdescent : baseEnd_282268 < baseStart_282268 := by decide
  rcases family_descends (prefixWord ++ tailWord_282268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282295 : List Nat := [1, 1, 3, 1, 5, 2, 2, 1, 1, 3, 3]
def baseStart_282295 : Nat := 118140960795 + 282295 * 2 ^ 59
def prefixEnd_282295 : Nat := 4983230072969 + 3 ^ 40 * 282295 * 2
def baseEnd_282295 : Nat := 144953021361078253214255

theorem tailTrace_282295 : CollatzResearch.WordTrace tailWord_282295 prefixEnd_282295 144953021361078253214255 := by
  unfold tailWord_282295
  simp only [CollatzResearch.WordTrace]
  refine ⟨10296144512300901992744339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6864096341533934661829559 10296144512300901992744339)
  ·
    refine ⟨15444216768451352989116509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10296144512300901992744339 15444216768451352989116509)
    ·
      refine ⟨5791581288169257370918691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15444216768451352989116509 5791581288169257370918691)
      ·
        refine ⟨8687371932253886056378037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5791581288169257370918691 8687371932253886056378037)
        ·
          refine ⟨814441118648801817785441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8687371932253886056378037 814441118648801817785441)
          ·
            refine ⟨610830838986601363339081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 814441118648801817785441 610830838986601363339081)
            ·
              refine ⟨458123129239951022504311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 610830838986601363339081 458123129239951022504311)
              ·
                refine ⟨687184693859926533756467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 458123129239951022504311 687184693859926533756467)
                ·
                  refine ⟨1030777040789889800634701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 687184693859926533756467 1030777040789889800634701)
                  ·
                    refine ⟨386541390296208675238013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1030777040789889800634701 386541390296208675238013)
                    ·
                      refine ⟨144953021361078253214255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 386541390296208675238013 144953021361078253214255)
                      ·
                        rfl

theorem cell23_282295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 3, 3].length) (baseStart_282295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282295 prefixEnd_282295 := by exact prefixLift 282295
  have htrace : WordTrace (prefixWord ++ tailWord_282295) baseStart_282295 baseEnd_282295 := by
    simpa [prefixWord, tailWord_282295, baseEnd_282295] using wordTrace_append hprefix tailTrace_282295
  have hstable : (prefixWord ++ tailWord_282295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282295).length < 2 ^ (prefixWord ++ tailWord_282295).sum := by decide
  have hdescent : baseEnd_282295 < baseStart_282295 := by decide
  rcases family_descends (prefixWord ++ tailWord_282295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282308 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_282308 : Nat := 118140960795 + 282308 * 2 ^ 59
def prefixEnd_282308 : Nat := 4983230072969 + 3 ^ 40 * 282308 * 2
def baseEnd_282308 : Nat := 144959696609586702351695

theorem tailTrace_282308 : CollatzResearch.WordTrace tailWord_282308 prefixEnd_282308 144959696609586702351695 := by
  unfold tailWord_282308
  simp only [CollatzResearch.WordTrace]
  refine ⟨5148309330626902606483789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6864412440835870141978385 5148309330626902606483789)
  ·
    refine ⟨1930615998985088477431421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5148309330626902606483789 1930615998985088477431421)
    ·
      refine ⟨723980999619408179036783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1930615998985088477431421 723980999619408179036783)
      ·
        refine ⟨1085971499429112268555175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 723980999619408179036783 1085971499429112268555175)
        ·
          refine ⟨1628957249143668402832763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1085971499429112268555175 1628957249143668402832763)
          ·
            refine ⟨2443435873715502604249145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1628957249143668402832763 2443435873715502604249145)
            ·
              refine ⟨1832576905286626953186859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2443435873715502604249145 1832576905286626953186859)
              ·
                refine ⟨2748865357929940429780289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1832576905286626953186859 2748865357929940429780289)
                ·
                  refine ⟨2061649018447455322335217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2748865357929940429780289 2061649018447455322335217)
                  ·
                    refine ⟨1546236763835591491751413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2061649018447455322335217 1546236763835591491751413)
                    ·
                      refine ⟨144959696609586702351695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1546236763835591491751413 144959696609586702351695)
                      ·
                        rfl

theorem cell23_282308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_282308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282308 prefixEnd_282308 := by exact prefixLift 282308
  have htrace : WordTrace (prefixWord ++ tailWord_282308) baseStart_282308 baseEnd_282308 := by
    simpa [prefixWord, tailWord_282308, baseEnd_282308] using wordTrace_append hprefix tailTrace_282308
  have hstable : (prefixWord ++ tailWord_282308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282308).length < 2 ^ (prefixWord ++ tailWord_282308).sum := by decide
  have hdescent : baseEnd_282308 < baseStart_282308 := by decide
  rcases family_descends (prefixWord ++ tailWord_282308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282311 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 1, 8]
def baseStart_282311 : Nat := 118140960795 + 282311 * 2 ^ 59
def prefixEnd_282311 : Nat := 4983230072969 + 3 ^ 40 * 282311 * 2
def baseEnd_282311 : Nat := 48320412350516730204727

theorem tailTrace_282311 : CollatzResearch.WordTrace tailWord_282311 prefixEnd_282311 48320412350516730204727 := by
  unfold tailWord_282311
  simp only [CollatzResearch.WordTrace]
  refine ⟨10296728080242936725326787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6864485386828624483551191 10296728080242936725326787)
  ·
    refine ⟨15445092120364405087990181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10296728080242936725326787 15445092120364405087990181)
    ·
      refine ⟨2895954772568325953998159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15445092120364405087990181 2895954772568325953998159)
      ·
        refine ⟨4343932158852488930997239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2895954772568325953998159 4343932158852488930997239)
        ·
          refine ⟨6515898238278733396495859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4343932158852488930997239 6515898238278733396495859)
          ·
            refine ⟨9773847357418100094743789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6515898238278733396495859 9773847357418100094743789)
            ·
              refine ⟨3665192759031787535528921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9773847357418100094743789 3665192759031787535528921)
              ·
                refine ⟨2748894569273840651646691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3665192759031787535528921 2748894569273840651646691)
                ·
                  refine ⟨4123341853910760977470037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2748894569273840651646691 4123341853910760977470037)
                  ·
                    refine ⟨48320412350516730204727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4123341853910760977470037 48320412350516730204727)
                    ·
                      rfl

theorem cell23_282311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_282311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282311 prefixEnd_282311 := by exact prefixLift 282311
  have htrace : WordTrace (prefixWord ++ tailWord_282311) baseStart_282311 baseEnd_282311 := by
    simpa [prefixWord, tailWord_282311, baseEnd_282311] using wordTrace_append hprefix tailTrace_282311
  have hstable : (prefixWord ++ tailWord_282311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282311).length < 2 ^ (prefixWord ++ tailWord_282311).sum := by decide
  have hdescent : baseEnd_282311 < baseStart_282311 := by decide
  rcases family_descends (prefixWord ++ tailWord_282311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282316 : List Nat := [2, 2, 1, 5, 3, 1, 2, 1, 1, 2, 3]
def baseStart_282316 : Nat := 118140960795 + 282316 * 2 ^ 59
def prefixEnd_282316 : Nat := 4983230072969 + 3 ^ 40 * 282316 * 2
def baseEnd_282316 : Nat := 144963804454822671051659

theorem tailTrace_282316 : CollatzResearch.WordTrace tailWord_282316 prefixEnd_282316 144963804454822671051659 := by
  unfold tailWord_282316
  simp only [CollatzResearch.WordTrace]
  refine ⟨5148455222612411289629401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6864606963483215052839201 5148455222612411289629401)
  ·
    refine ⟨3861341416959308467222051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5148455222612411289629401 3861341416959308467222051)
    ·
      refine ⟨5792012125438962700833077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3861341416959308467222051 5792012125438962700833077)
      ·
        refine ⟨543001136759902753203101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5792012125438962700833077 543001136759902753203101)
        ·
          refine ⟨203625426284963532451163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 543001136759902753203101 203625426284963532451163)
          ·
            refine ⟨305438139427445298676745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203625426284963532451163 305438139427445298676745)
            ·
              refine ⟨229078604570583974007559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305438139427445298676745 229078604570583974007559)
              ·
                refine ⟨343617906855875961011339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229078604570583974007559 343617906855875961011339)
                ·
                  refine ⟨515426860283813941517009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 343617906855875961011339 515426860283813941517009)
                  ·
                    refine ⟨386570145212860456137757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 515426860283813941517009 386570145212860456137757)
                    ·
                      refine ⟨144963804454822671051659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 386570145212860456137757 144963804454822671051659)
                      ·
                        rfl

theorem cell23_282316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_282316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282316 prefixEnd_282316 := by exact prefixLift 282316
  have htrace : WordTrace (prefixWord ++ tailWord_282316) baseStart_282316 baseEnd_282316 := by
    simpa [prefixWord, tailWord_282316, baseEnd_282316] using wordTrace_append hprefix tailTrace_282316
  have hstable : (prefixWord ++ tailWord_282316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282316).length < 2 ^ (prefixWord ++ tailWord_282316).sum := by decide
  have hdescent : baseEnd_282316 < baseStart_282316 := by decide
  rcases family_descends (prefixWord ++ tailWord_282316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282348 : List Nat := [2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 4]
def baseStart_282348 : Nat := 118140960795 + 282348 * 2 ^ 59
def prefixEnd_282348 : Nat := 4983230072969 + 3 ^ 40 * 282348 * 2
def baseEnd_282348 : Nat := 144980235835766545851511

theorem tailTrace_282348 : CollatzResearch.WordTrace tailWord_282348 prefixEnd_282348 144980235835766545851511 := by
  unfold tailWord_282348
  simp only [CollatzResearch.WordTrace]
  refine ⟨5149038790554446022211849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6865385054072594696282465 5149038790554446022211849)
  ·
    refine ⟨3861779092915834516658887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5149038790554446022211849 3861779092915834516658887)
    ·
      refine ⟨5792668639373751774988331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3861779092915834516658887 5792668639373751774988331)
      ·
        refine ⟨8689002959060627662482497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5792668639373751774988331 8689002959060627662482497)
        ·
          refine ⟨6516752219295470746861873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8689002959060627662482497 6516752219295470746861873)
          ·
            refine ⟨4887564164471603060146405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6516752219295470746861873 4887564164471603060146405)
            ·
              refine ⟨916418280838425573777451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4887564164471603060146405 916418280838425573777451)
              ·
                refine ⟨1374627421257638360666177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 916418280838425573777451 1374627421257638360666177)
                ·
                  refine ⟨1030970565943228770499633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1374627421257638360666177 1030970565943228770499633)
                  ·
                    refine ⟨773227924457421577874725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1030970565943228770499633 773227924457421577874725)
                    ·
                      refine ⟨144980235835766545851511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 773227924457421577874725 144980235835766545851511)
                      ·
                        rfl

theorem cell23_282348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_282348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282348 prefixEnd_282348 := by exact prefixLift 282348
  have htrace : WordTrace (prefixWord ++ tailWord_282348) baseStart_282348 baseEnd_282348 := by
    simpa [prefixWord, tailWord_282348, baseEnd_282348] using wordTrace_append hprefix tailTrace_282348
  have hstable : (prefixWord ++ tailWord_282348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282348).length < 2 ^ (prefixWord ++ tailWord_282348).sum := by decide
  have hdescent : baseEnd_282348 < baseStart_282348 := by decide
  rcases family_descends (prefixWord ++ tailWord_282348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282356 : List Nat := [2, 6, 1, 1, 1, 1, 1, 4, 1, 3, 2]
def baseStart_282356 : Nat := 118140960795 + 282356 * 2 ^ 59
def prefixEnd_282356 : Nat := 4983230072969 + 3 ^ 40 * 282356 * 2
def baseEnd_282356 : Nat := 144984343681002514551475

theorem tailTrace_282356 : CollatzResearch.WordTrace tailWord_282356 prefixEnd_282356 144984343681002514551475 := by
  unfold tailWord_282356
  simp only [CollatzResearch.WordTrace]
  refine ⟨5149184682539954705357461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6865579576719939607143281 5149184682539954705357461)
  ·
    refine ⟨241368031994060376813631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5149184682539954705357461 241368031994060376813631)
    ·
      refine ⟨362052047991090565220447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241368031994060376813631 362052047991090565220447)
      ·
        refine ⟨543078071986635847830671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362052047991090565220447 543078071986635847830671)
        ·
          refine ⟨814617107979953771746007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 543078071986635847830671 814617107979953771746007)
          ·
            refine ⟨1221925661969930657619011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 814617107979953771746007 1221925661969930657619011)
            ·
              refine ⟨1832888492954895986428517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1221925661969930657619011 1832888492954895986428517)
              ·
                refine ⟨343666592429042997455347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1832888492954895986428517 343666592429042997455347)
                ·
                  refine ⟨515499888643564496183021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 343666592429042997455347 515499888643564496183021)
                  ·
                    refine ⟨193312458241336686068633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 515499888643564496183021 193312458241336686068633)
                    ·
                      refine ⟨144984343681002514551475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 193312458241336686068633 144984343681002514551475)
                      ·
                        rfl

theorem cell23_282356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_282356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282356 prefixEnd_282356 := by exact prefixLift 282356
  have htrace : WordTrace (prefixWord ++ tailWord_282356) baseStart_282356 baseEnd_282356 := by
    simpa [prefixWord, tailWord_282356, baseEnd_282356] using wordTrace_append hprefix tailTrace_282356
  have hstable : (prefixWord ++ tailWord_282356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282356).length < 2 ^ (prefixWord ++ tailWord_282356).sum := by decide
  have hdescent : baseEnd_282356 < baseStart_282356 := by decide
  rcases family_descends (prefixWord ++ tailWord_282356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282422 : List Nat := [5, 1, 2, 2, 1, 1, 1, 3, 2, 5]
def baseStart_282422 : Nat := 118140960795 + 282422 * 2 ^ 59
def prefixEnd_282422 : Nat := 4983230072969 + 3 ^ 40 * 282422 * 2
def baseEnd_282422 : Nat := 48339411134733085442057

theorem tailTrace_282422 : CollatzResearch.WordTrace tailWord_282422 prefixEnd_282422 48339411134733085442057 := by
  unfold tailWord_282422
  simp only [CollatzResearch.WordTrace]
  refine ⟨643798536427550167663595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6867184388560535121745013 643798536427550167663595)
  ·
    refine ⟨965697804641325251495393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 643798536427550167663595 965697804641325251495393)
    ·
      refine ⟨724273353480993938621545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 965697804641325251495393 724273353480993938621545)
      ·
        refine ⟨543205015110745453966159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 724273353480993938621545 543205015110745453966159)
        ·
          refine ⟨814807522666118180949239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 543205015110745453966159 814807522666118180949239)
          ·
            refine ⟨1222211283999177271423859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 814807522666118180949239 1222211283999177271423859)
            ·
              refine ⟨1833316925998765907135789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1222211283999177271423859 1833316925998765907135789)
              ·
                refine ⟨687493847249537215175921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1833316925998765907135789 687493847249537215175921)
                ·
                  refine ⟨515620385437152911381941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 687493847249537215175921 515620385437152911381941)
                  ·
                    refine ⟨48339411134733085442057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 515620385437152911381941 48339411134733085442057)
                    ·
                      rfl

theorem cell23_282422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_282422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282422 prefixEnd_282422 := by exact prefixLift 282422
  have htrace : WordTrace (prefixWord ++ tailWord_282422) baseStart_282422 baseEnd_282422 := by
    simpa [prefixWord, tailWord_282422, baseEnd_282422] using wordTrace_append hprefix tailTrace_282422
  have hstable : (prefixWord ++ tailWord_282422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282422).length < 2 ^ (prefixWord ++ tailWord_282422).sum := by decide
  have hdescent : baseEnd_282422 < baseStart_282422 := by decide
  rcases family_descends (prefixWord ++ tailWord_282422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282529 : List Nat := [1, 2, 3, 4, 2, 1, 2, 2, 1, 5]
def baseStart_282529 : Nat := 118140960795 + 282529 * 2 ^ 59
def prefixEnd_282529 : Nat := 4983230072969 + 3 ^ 40 * 282529 * 2
def baseEnd_282529 : Nat := 48357725278076779229393

theorem tailTrace_282529 : CollatzResearch.WordTrace tailWord_282529 prefixEnd_282529 48357725278076779229393 := by
  unfold tailWord_282529
  simp only [CollatzResearch.WordTrace]
  refine ⟨10304679193453159956762641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6869786128968773304508427 10304679193453159956762641)
  ·
    refine ⟨7728509395089869967571981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10304679193453159956762641 7728509395089869967571981)
    ·
      refine ⟨2898191023158701237839493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7728509395089869967571981 2898191023158701237839493)
      ·
        refine ⟨543410816842256482094905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2898191023158701237839493 543410816842256482094905)
        ·
          refine ⟨407558112631692361571179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 543410816842256482094905 407558112631692361571179)
          ·
            refine ⟨611337168947538542356769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407558112631692361571179 611337168947538542356769)
            ·
              refine ⟨458502876710653906767577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 611337168947538542356769 458502876710653906767577)
              ·
                refine ⟨343877157532990430075683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 458502876710653906767577 343877157532990430075683)
                ·
                  refine ⟨515815736299485645113525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 343877157532990430075683 515815736299485645113525)
                  ·
                    refine ⟨48357725278076779229393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 515815736299485645113525 48357725278076779229393)
                    ·
                      rfl

theorem cell23_282529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_282529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282529 prefixEnd_282529 := by exact prefixLift 282529
  have htrace : WordTrace (prefixWord ++ tailWord_282529) baseStart_282529 baseEnd_282529 := by
    simpa [prefixWord, tailWord_282529, baseEnd_282529] using wordTrace_append hprefix tailTrace_282529
  have hstable : (prefixWord ++ tailWord_282529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282529).length < 2 ^ (prefixWord ++ tailWord_282529).sum := by decide
  have hdescent : baseEnd_282529 < baseStart_282529 := by decide
  rcases family_descends (prefixWord ++ tailWord_282529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282532 : List Nat := [2, 3, 1, 2, 1, 3, 1, 4, 1, 1, 4]
def baseStart_282532 : Nat := 118140960795 + 282532 * 2 ^ 59
def prefixEnd_282532 : Nat := 4983230072969 + 3 ^ 40 * 282532 * 2
def baseEnd_282532 : Nat := 145074716276193825950665

theorem tailTrace_282532 : CollatzResearch.WordTrace tailWord_282532 prefixEnd_282532 145074716276193825950665 := by
  unfold tailWord_282532
  simp only [CollatzResearch.WordTrace]
  refine ⟨5152394306221145734560925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6869859074961527646081233 5152394306221145734560925)
  ·
    refine ⟨1932147864832929650460347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5152394306221145734560925 1932147864832929650460347)
    ·
      refine ⟨2898221797249394475690521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1932147864832929650460347 2898221797249394475690521)
      ·
        refine ⟨2173666347937045856767891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2898221797249394475690521 2173666347937045856767891)
        ·
          refine ⟨3260499521905568785151837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2173666347937045856767891 3260499521905568785151837)
          ·
            refine ⟨1222687320714588294431939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3260499521905568785151837 1222687320714588294431939)
            ·
              refine ⟨1834030981071882441647909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1222687320714588294431939 1834030981071882441647909)
              ·
                refine ⟨343880808950977957808983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1834030981071882441647909 343880808950977957808983)
                ·
                  refine ⟨515821213426466936713475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 343880808950977957808983 515821213426466936713475)
                  ·
                    refine ⟨773731820139700405070213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 515821213426466936713475 773731820139700405070213)
                    ·
                      refine ⟨145074716276193825950665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 773731820139700405070213 145074716276193825950665)
                      ·
                        rfl

theorem cell23_282532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_282532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282532 prefixEnd_282532 := by exact prefixLift 282532
  have htrace : WordTrace (prefixWord ++ tailWord_282532) baseStart_282532 baseEnd_282532 := by
    simpa [prefixWord, tailWord_282532, baseEnd_282532] using wordTrace_append hprefix tailTrace_282532
  have hstable : (prefixWord ++ tailWord_282532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282532).length < 2 ^ (prefixWord ++ tailWord_282532).sum := by decide
  have hdescent : baseEnd_282532 < baseStart_282532 := by decide
  rcases family_descends (prefixWord ++ tailWord_282532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282552 : List Nat := [2, 1, 2, 1, 2, 3, 1, 5, 1, 2, 3]
def baseStart_282552 : Nat := 118140960795 + 282552 * 2 ^ 59
def prefixEnd_282552 : Nat := 4983230072969 + 3 ^ 40 * 282552 * 2
def baseEnd_282552 : Nat := 145084985889283747700573

theorem tailTrace_282552 : CollatzResearch.WordTrace tailWord_282552 prefixEnd_282552 145084985889283747700573 := by
  unfold tailWord_282552
  simp only [CollatzResearch.WordTrace]
  refine ⟨5152759036184917442424955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6870345381579889923233273 5152759036184917442424955)
  ·
    refine ⟨7729138554277376163637433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5152759036184917442424955 7729138554277376163637433)
    ·
      refine ⟨5796853915708032122728075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7729138554277376163637433 5796853915708032122728075)
      ·
        refine ⟨8695280873562048184092113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5796853915708032122728075 8695280873562048184092113)
        ·
          refine ⟨6521460655171536138069085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8695280873562048184092113 6521460655171536138069085)
          ·
            refine ⟨2445547745689326051775907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6521460655171536138069085 2445547745689326051775907)
            ·
              refine ⟨3668321618533989077663861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2445547745689326051775907 3668321618533989077663861)
              ·
                refine ⟨343905151737561476030987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3668321618533989077663861 343905151737561476030987)
                ·
                  refine ⟨515857727606342214046481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 343905151737561476030987 515857727606342214046481)
                  ·
                    refine ⟨386893295704756660534861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 515857727606342214046481 386893295704756660534861)
                    ·
                      refine ⟨145084985889283747700573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 386893295704756660534861 145084985889283747700573)
                      ·
                        rfl

theorem cell23_282552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 1, 2, 3].length) (baseStart_282552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282552 prefixEnd_282552 := by exact prefixLift 282552
  have htrace : WordTrace (prefixWord ++ tailWord_282552) baseStart_282552 baseEnd_282552 := by
    simpa [prefixWord, tailWord_282552, baseEnd_282552] using wordTrace_append hprefix tailTrace_282552
  have hstable : (prefixWord ++ tailWord_282552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282552).length < 2 ^ (prefixWord ++ tailWord_282552).sum := by decide
  have hdescent : baseEnd_282552 < baseStart_282552 := by decide
  rcases family_descends (prefixWord ++ tailWord_282552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282565 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 5, 3, 3]
def baseStart_282565 : Nat := 118140960795 + 282565 * 2 ^ 59
def prefixEnd_282565 : Nat := 4983230072969 + 3 ^ 40 * 282565 * 2
def baseEnd_282565 : Nat := 145091661137792196838013

theorem tailTrace_282565 : CollatzResearch.WordTrace tailWord_282565 prefixEnd_282565 145091661137792196838013 := by
  unfold tailWord_282565
  simp only [CollatzResearch.WordTrace]
  refine ⟨10305992221322738105073149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6870661480881825403382099 10305992221322738105073149)
  ·
    refine ⟨3864747082996026789402431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10305992221322738105073149 3864747082996026789402431)
    ·
      refine ⟨5797120624494040184103647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3864747082996026789402431 5797120624494040184103647)
      ·
        refine ⟨8695680936741060276155471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5797120624494040184103647 8695680936741060276155471)
        ·
          refine ⟨13043521405111590414233207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8695680936741060276155471 13043521405111590414233207)
          ·
            refine ⟨19565282107667385621349811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13043521405111590414233207 19565282107667385621349811)
            ·
              refine ⟨29347923161501078432024717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19565282107667385621349811 29347923161501078432024717)
              ·
                refine ⟨11005471185562904412009269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29347923161501078432024717 11005471185562904412009269)
                ·
                  refine ⟨1031762923646522288625869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11005471185562904412009269 1031762923646522288625869)
                  ·
                    refine ⟨386911096367445858234701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1031762923646522288625869 386911096367445858234701)
                    ·
                      refine ⟨145091661137792196838013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 386911096367445858234701 145091661137792196838013)
                      ·
                        rfl

theorem cell23_282565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 3, 3].length) (baseStart_282565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282565 prefixEnd_282565 := by exact prefixLift 282565
  have htrace : WordTrace (prefixWord ++ tailWord_282565) baseStart_282565 baseEnd_282565 := by
    simpa [prefixWord, tailWord_282565, baseEnd_282565] using wordTrace_append hprefix tailTrace_282565
  have hstable : (prefixWord ++ tailWord_282565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282565).length < 2 ^ (prefixWord ++ tailWord_282565).sum := by decide
  have hdescent : baseEnd_282565 < baseStart_282565 := by decide
  rcases family_descends (prefixWord ++ tailWord_282565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282586 : List Nat := [3, 1, 1, 2, 5, 2, 1, 2, 1, 2, 3]
def baseStart_282586 : Nat := 118140960795 + 282586 * 2 ^ 59
def prefixEnd_282586 : Nat := 4983230072969 + 3 ^ 40 * 282586 * 2
def baseEnd_282586 : Nat := 145102444231536614675417

theorem tailTrace_282586 : CollatzResearch.WordTrace tailWord_282586 prefixEnd_282586 145102444231536614675417 := by
  unfold tailWord_282586
  simp only [CollatzResearch.WordTrace]
  refine ⟨2576689538561664672896903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6871172102831105794391741 2576689538561664672896903)
  ·
    refine ⟨3865034307842497009345355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2576689538561664672896903 3865034307842497009345355)
    ·
      refine ⟨5797551461763745514018033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3865034307842497009345355 5797551461763745514018033)
      ·
        refine ⟨4348163596322809135513525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5797551461763745514018033 4348163596322809135513525)
        ·
          refine ⟨407640337155263356454393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4348163596322809135513525 407640337155263356454393)
          ·
            refine ⟨305730252866447517340795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 407640337155263356454393 305730252866447517340795)
            ·
              refine ⟨458595379299671276011193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305730252866447517340795 458595379299671276011193)
              ·
                refine ⟨343946534474753457008395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 458595379299671276011193 343946534474753457008395)
                ·
                  refine ⟨515919801712130185512593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 343946534474753457008395 515919801712130185512593)
                  ·
                    refine ⟨386939851284097639134445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 515919801712130185512593 386939851284097639134445)
                    ·
                      refine ⟨145102444231536614675417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 386939851284097639134445 145102444231536614675417)
                      ·
                        rfl

theorem cell23_282586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_282586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282586 prefixEnd_282586 := by exact prefixLift 282586
  have htrace : WordTrace (prefixWord ++ tailWord_282586) baseStart_282586 baseEnd_282586 := by
    simpa [prefixWord, tailWord_282586, baseEnd_282586] using wordTrace_append hprefix tailTrace_282586
  have hstable : (prefixWord ++ tailWord_282586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282586).length < 2 ^ (prefixWord ++ tailWord_282586).sum := by decide
  have hdescent : baseEnd_282586 < baseStart_282586 := by decide
  rcases family_descends (prefixWord ++ tailWord_282586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282599 : List Nat := [1, 1, 5, 2, 3, 1, 1, 2, 1, 3, 3]
def baseStart_282599 : Nat := 118140960795 + 282599 * 2 ^ 59
def prefixEnd_282599 : Nat := 4983230072969 + 3 ^ 40 * 282599 * 2
def baseEnd_282599 : Nat := 145109119480045063812857

theorem tailTrace_282599 : CollatzResearch.WordTrace tailWord_282599 prefixEnd_282599 145109119480045063812857 := by
  unfold tailWord_282599
  simp only [CollatzResearch.WordTrace]
  refine ⟨10307232303199561911810851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6871488202133041274540567 10307232303199561911810851)
  ·
    refine ⟨15460848454799342867716277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10307232303199561911810851 15460848454799342867716277)
    ·
      refine ⟨1449454542637438393848401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15460848454799342867716277 1449454542637438393848401)
      ·
        refine ⟨1087090906978078795386301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1449454542637438393848401 1087090906978078795386301)
        ·
          refine ⟨407659090116779548269863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1087090906978078795386301 407659090116779548269863)
          ·
            refine ⟨611488635175169322404795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407659090116779548269863 611488635175169322404795)
            ·
              refine ⟨917232952762753983607193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 611488635175169322404795 917232952762753983607193)
              ·
                refine ⟨687924714572065487705395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 917232952762753983607193 687924714572065487705395)
                ·
                  refine ⟨1031887071858098231558093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 687924714572065487705395 1031887071858098231558093)
                  ·
                    refine ⟨386957651946786836834285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1031887071858098231558093 386957651946786836834285)
                    ·
                      refine ⟨145109119480045063812857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 386957651946786836834285 145109119480045063812857)
                      ·
                        rfl

theorem cell23_282599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_282599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282599 prefixEnd_282599 := by exact prefixLift 282599
  have htrace : WordTrace (prefixWord ++ tailWord_282599) baseStart_282599 baseEnd_282599 := by
    simpa [prefixWord, tailWord_282599, baseEnd_282599] using wordTrace_append hprefix tailTrace_282599
  have hstable : (prefixWord ++ tailWord_282599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282599).length < 2 ^ (prefixWord ++ tailWord_282599).sum := by decide
  have hdescent : baseEnd_282599 < baseStart_282599 := by decide
  rcases family_descends (prefixWord ++ tailWord_282599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282630 : List Nat := [6, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_282630 : Nat := 118140960795 + 282630 * 2 ^ 59
def prefixEnd_282630 : Nat := 4983230072969 + 3 ^ 40 * 282630 * 2
def baseEnd_282630 : Nat := 145125037380334442525215

theorem tailTrace_282630 : CollatzResearch.WordTrace tailWord_282630 prefixEnd_282630 145125037380334442525215 := by
  unfold tailWord_282630
  simp only [CollatzResearch.WordTrace]
  refine ⟨322136342690226693943417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6872241977391502804126229 322136342690226693943417)
  ·
    refine ⟨241602257017670020457563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 322136342690226693943417 241602257017670020457563)
    ·
      refine ⟨362403385526505030686345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241602257017670020457563 362403385526505030686345)
      ·
        refine ⟨271802539144878773014759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 362403385526505030686345 271802539144878773014759)
        ·
          refine ⟨407703808717318159522139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271802539144878773014759 407703808717318159522139)
          ·
            refine ⟨611555713075977239283209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407703808717318159522139 611555713075977239283209)
            ·
              refine ⟨458666784806982929462407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 611555713075977239283209 458666784806982929462407)
              ·
                refine ⟨688000177210474394193611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 458666784806982929462407 688000177210474394193611)
                ·
                  refine ⟨1032000265815711591290417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 688000177210474394193611 1032000265815711591290417)
                  ·
                    refine ⟨774000199361783693467813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1032000265815711591290417 774000199361783693467813)
                    ·
                      refine ⟨145125037380334442525215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 774000199361783693467813 145125037380334442525215)
                      ·
                        rfl

theorem cell23_282630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_282630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282630 prefixEnd_282630 := by exact prefixLift 282630
  have htrace : WordTrace (prefixWord ++ tailWord_282630) baseStart_282630 baseEnd_282630 := by
    simpa [prefixWord, tailWord_282630, baseEnd_282630] using wordTrace_append hprefix tailTrace_282630
  have hstable : (prefixWord ++ tailWord_282630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282630).length < 2 ^ (prefixWord ++ tailWord_282630).sum := by decide
  have hdescent : baseEnd_282630 < baseStart_282630 := by decide
  rcases family_descends (prefixWord ++ tailWord_282630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282660 : List Nat := [2, 3, 1, 4, 2, 2, 2, 1, 1, 3, 2]
def baseStart_282660 : Nat := 118140960795 + 282660 * 2 ^ 59
def prefixEnd_282660 : Nat := 4983230072969 + 3 ^ 40 * 282660 * 2
def baseEnd_282660 : Nat := 145140441799969325150077

theorem tailTrace_282660 : CollatzResearch.WordTrace tailWord_282660 prefixEnd_282660 145140441799969325150077 := by
  unfold tailWord_282660
  simp only [CollatzResearch.WordTrace]
  refine ⟨5154728577989284664890717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6872971437319046219854289 5154728577989284664890717)
  ·
    refine ⟨1933023216745981749334019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5154728577989284664890717 1933023216745981749334019)
    ·
      refine ⟨2899534825118972624001029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1933023216745981749334019 2899534825118972624001029)
      ·
        refine ⟨543662779709807367000193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2899534825118972624001029 543662779709807367000193)
        ·
          refine ⟨407747084782355525250145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 543662779709807367000193 407747084782355525250145)
          ·
            refine ⟨305810313586766643937609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 407747084782355525250145 305810313586766643937609)
            ·
              refine ⟨229357735190074982953207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305810313586766643937609 229357735190074982953207)
              ·
                refine ⟨344036602785112474429811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229357735190074982953207 344036602785112474429811)
                ·
                  refine ⟨516054904177668711644717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 344036602785112474429811 516054904177668711644717)
                  ·
                    refine ⟨193520589066625766866769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 516054904177668711644717 193520589066625766866769)
                    ·
                      refine ⟨145140441799969325150077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 193520589066625766866769 145140441799969325150077)
                      ·
                        rfl

theorem cell23_282660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_282660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282660 prefixEnd_282660 := by exact prefixLift 282660
  have htrace : WordTrace (prefixWord ++ tailWord_282660) baseStart_282660 baseEnd_282660 := by
    simpa [prefixWord, tailWord_282660, baseEnd_282660] using wordTrace_append hprefix tailTrace_282660
  have hstable : (prefixWord ++ tailWord_282660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282660).length < 2 ^ (prefixWord ++ tailWord_282660).sum := by decide
  have hdescent : baseEnd_282660 < baseStart_282660 := by decide
  rcases family_descends (prefixWord ++ tailWord_282660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282672 : List Nat := [2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 3]
def baseStart_282672 : Nat := 118140960795 + 282672 * 2 ^ 59
def prefixEnd_282672 : Nat := 4983230072969 + 3 ^ 40 * 282672 * 2
def baseEnd_282672 : Nat := 145146603567823278200021

theorem tailTrace_282672 : CollatzResearch.WordTrace tailWord_282672 prefixEnd_282672 145146603567823278200021 := by
  unfold tailWord_282672
  simp only [CollatzResearch.WordTrace]
  refine ⟨5154947415967547689609135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6873263221290063586145513 5154947415967547689609135)
  ·
    refine ⟨7732421123951321534413703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5154947415967547689609135 7732421123951321534413703)
    ·
      refine ⟨11598631685926982301620555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7732421123951321534413703 11598631685926982301620555)
      ·
        refine ⟨17397947528890473452430833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11598631685926982301620555 17397947528890473452430833)
        ·
          refine ⟨13048460646667855089323125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17397947528890473452430833 13048460646667855089323125)
          ·
            refine ⟨1223293185625111414624043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13048460646667855089323125 1223293185625111414624043)
            ·
              refine ⟨1834939778437667121936065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1223293185625111414624043 1834939778437667121936065)
              ·
                refine ⟨1376204833828250341452049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1834939778437667121936065 1376204833828250341452049)
                ·
                  refine ⟨1032153625371187756089037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1376204833828250341452049 1032153625371187756089037)
                  ·
                    refine ⟨387057609514195408533389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1032153625371187756089037 387057609514195408533389)
                    ·
                      refine ⟨145146603567823278200021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 387057609514195408533389 145146603567823278200021)
                      ·
                        rfl

theorem cell23_282672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 3].length) (baseStart_282672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282672 prefixEnd_282672 := by exact prefixLift 282672
  have htrace : WordTrace (prefixWord ++ tailWord_282672) baseStart_282672 baseEnd_282672 := by
    simpa [prefixWord, tailWord_282672, baseEnd_282672] using wordTrace_append hprefix tailTrace_282672
  have hstable : (prefixWord ++ tailWord_282672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282672).length < 2 ^ (prefixWord ++ tailWord_282672).sum := by decide
  have hdescent : baseEnd_282672 < baseStart_282672 := by decide
  rcases family_descends (prefixWord ++ tailWord_282672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282673 : List Nat := [1, 2, 2, 3, 1, 5, 1, 2, 2, 2, 2]
def baseStart_282673 : Nat := 118140960795 + 282673 * 2 ^ 59
def prefixEnd_282673 : Nat := 4983230072969 + 3 ^ 40 * 282673 * 2
def baseEnd_282673 : Nat := 145147117048477774287517

theorem tailTrace_282673 : CollatzResearch.WordTrace tailWord_282673 prefixEnd_282673 145147117048477774287517 := by
  unfold tailWord_282673
  simp only [CollatzResearch.WordTrace]
  refine ⟨10309931304931472550004673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6873287536620981700003115 10309931304931472550004673)
  ·
    refine ⟨7732448478698604412503505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10309931304931472550004673 7732448478698604412503505)
    ·
      refine ⟨5799336359023953309377629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7732448478698604412503505 5799336359023953309377629)
      ·
        refine ⟨2174751134633982491016611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5799336359023953309377629 2174751134633982491016611)
        ·
          refine ⟨3262126701950973736524917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2174751134633982491016611 3262126701950973736524917)
          ·
            refine ⟨305824378307903787799211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3262126701950973736524917 305824378307903787799211)
            ·
              refine ⟨458736567461855681698817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305824378307903787799211 458736567461855681698817)
              ·
                refine ⟨344052425596391761274113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 458736567461855681698817 344052425596391761274113)
                ·
                  refine ⟨258039319197293820955585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 344052425596391761274113 258039319197293820955585)
                  ·
                    refine ⟨193529489397970365716689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 258039319197293820955585 193529489397970365716689)
                    ·
                      refine ⟨145147117048477774287517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 193529489397970365716689 145147117048477774287517)
                      ·
                        rfl

theorem cell23_282673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_282673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282673 prefixEnd_282673 := by exact prefixLift 282673
  have htrace : WordTrace (prefixWord ++ tailWord_282673) baseStart_282673 baseEnd_282673 := by
    simpa [prefixWord, tailWord_282673, baseEnd_282673] using wordTrace_append hprefix tailTrace_282673
  have hstable : (prefixWord ++ tailWord_282673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282673).length < 2 ^ (prefixWord ++ tailWord_282673).sum := by decide
  have hdescent : baseEnd_282673 < baseStart_282673 := by decide
  rcases family_descends (prefixWord ++ tailWord_282673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282689 : List Nat := [1, 2, 5, 1, 2, 1, 2, 1, 2, 3, 3]
def baseStart_282689 : Nat := 118140960795 + 282689 * 2 ^ 59
def prefixEnd_282689 : Nat := 4983230072969 + 3 ^ 40 * 282689 * 2
def baseEnd_282689 : Nat := 145155332738949711687443

theorem tailTrace_282689 : CollatzResearch.WordTrace tailWord_282689 prefixEnd_282689 145155332738949711687443 := by
  unfold tailWord_282689
  simp only [CollatzResearch.WordTrace]
  refine ⟨10310514872873507282587121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6873676581915671521724747 10310514872873507282587121)
  ·
    refine ⟨7732886154655130461940341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10310514872873507282587121 7732886154655130461940341)
    ·
      refine ⟨724958076998918480806907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7732886154655130461940341 724958076998918480806907)
      ·
        refine ⟨1087437115498377721210361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 724958076998918480806907 1087437115498377721210361)
        ·
          refine ⟨815577836623783290907771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1087437115498377721210361 815577836623783290907771)
          ·
            refine ⟨1223366754935674936361657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 815577836623783290907771 1223366754935674936361657)
            ·
              refine ⟨917525066201756202271243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1223366754935674936361657 917525066201756202271243)
              ·
                refine ⟨1376287599302634303406865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 917525066201756202271243 1376287599302634303406865)
                ·
                  refine ⟨1032215699476975727555149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1376287599302634303406865 1032215699476975727555149)
                  ·
                    refine ⟨387080887303865897833181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1032215699476975727555149 387080887303865897833181)
                    ·
                      refine ⟨145155332738949711687443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 387080887303865897833181 145155332738949711687443)
                      ·
                        rfl

theorem cell23_282689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_282689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282689 prefixEnd_282689 := by exact prefixLift 282689
  have htrace : WordTrace (prefixWord ++ tailWord_282689) baseStart_282689 baseEnd_282689 := by
    simpa [prefixWord, tailWord_282689, baseEnd_282689] using wordTrace_append hprefix tailTrace_282689
  have hstable : (prefixWord ++ tailWord_282689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282689).length < 2 ^ (prefixWord ++ tailWord_282689).sum := by decide
  have hdescent : baseEnd_282689 < baseStart_282689 := by decide
  rcases family_descends (prefixWord ++ tailWord_282689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282705 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 1, 10]
def baseStart_282705 : Nat := 118140960795 + 282705 * 2 ^ 59
def prefixEnd_282705 : Nat := 4983230072969 + 3 ^ 40 * 282705 * 2
def baseEnd_282705 : Nat := 48387849476473883029123

theorem tailTrace_282705 : CollatzResearch.WordTrace tailWord_282705 prefixEnd_282705 48387849476473883029123 := by
  unfold tailWord_282705
  simp only [CollatzResearch.WordTrace]
  refine ⟨10311098440815542015169569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6874065627210361343446379 10311098440815542015169569)
  ·
    refine ⟨7733323830611656511377177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10311098440815542015169569 7733323830611656511377177)
    ·
      refine ⟨5799992872958742383532883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7733323830611656511377177 5799992872958742383532883)
      ·
        refine ⟨8699989309438113575299325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5799992872958742383532883 8699989309438113575299325)
        ·
          refine ⟨3262495991039292590737247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8699989309438113575299325 3262495991039292590737247)
          ·
            refine ⟨4893743986558938886105871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3262495991039292590737247 4893743986558938886105871)
            ·
              refine ⟨7340615979838408329158807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4893743986558938886105871 7340615979838408329158807)
              ·
                refine ⟨11010923969757612493738211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7340615979838408329158807 11010923969757612493738211)
                ·
                  refine ⟨16516385954636418740607317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11010923969757612493738211 16516385954636418740607317)
                  ·
                    refine ⟨48387849476473883029123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 16516385954636418740607317 48387849476473883029123)
                    ·
                      rfl

theorem cell23_282705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 10].length) (baseStart_282705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282705 prefixEnd_282705 := by exact prefixLift 282705
  have htrace : WordTrace (prefixWord ++ tailWord_282705) baseStart_282705 baseEnd_282705 := by
    simpa [prefixWord, tailWord_282705, baseEnd_282705] using wordTrace_append hprefix tailTrace_282705
  have hstable : (prefixWord ++ tailWord_282705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282705).length < 2 ^ (prefixWord ++ tailWord_282705).sum := by decide
  have hdescent : baseEnd_282705 < baseStart_282705 := by decide
  rcases family_descends (prefixWord ++ tailWord_282705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282712 : List Nat := [2, 1, 2, 2, 1, 4, 2, 1, 1, 3, 4]
def baseStart_282712 : Nat := 118140960795 + 282712 * 2 ^ 59
def prefixEnd_282712 : Nat := 4983230072969 + 3 ^ 40 * 282712 * 2
def baseEnd_282712 : Nat := 145167142794003121699837

theorem tailTrace_282712 : CollatzResearch.WordTrace tailWord_282712 prefixEnd_282712 145167142794003121699837 := by
  unfold tailWord_282712
  simp only [CollatzResearch.WordTrace]
  refine ⟨5155676875895091105337195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6874235834526788140449593 5155676875895091105337195)
  ·
    refine ⟨7733515313842636658005793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5155676875895091105337195 7733515313842636658005793)
    ·
      refine ⟨5800136485381977493504345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7733515313842636658005793 5800136485381977493504345)
      ·
        refine ⟨4350102364036483120128259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5800136485381977493504345 4350102364036483120128259)
        ·
          refine ⟨6525153546054724680192389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4350102364036483120128259 6525153546054724680192389)
          ·
            refine ⟨1223466289885260877536073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6525153546054724680192389 1223466289885260877536073)
            ·
              refine ⟨917599717413945658152055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1223466289885260877536073 917599717413945658152055)
              ·
                refine ⟨1376399576120918487228083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 917599717413945658152055 1376399576120918487228083)
                ·
                  refine ⟨2064599364181377730842125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1376399576120918487228083 2064599364181377730842125)
                  ·
                    refine ⟨774224761568016649065797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2064599364181377730842125 774224761568016649065797)
                    ·
                      refine ⟨145167142794003121699837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 774224761568016649065797 145167142794003121699837)
                      ·
                        rfl

theorem cell23_282712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_282712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282712 prefixEnd_282712 := by exact prefixLift 282712
  have htrace : WordTrace (prefixWord ++ tailWord_282712) baseStart_282712 baseEnd_282712 := by
    simpa [prefixWord, tailWord_282712, baseEnd_282712] using wordTrace_append hprefix tailTrace_282712
  have hstable : (prefixWord ++ tailWord_282712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282712).length < 2 ^ (prefixWord ++ tailWord_282712).sum := by decide
  have hdescent : baseEnd_282712 < baseStart_282712 := by decide
  rcases family_descends (prefixWord ++ tailWord_282712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282786 : List Nat := [3, 3, 1, 3, 1, 2, 2, 2, 6]
def baseStart_282786 : Nat := 118140960795 + 282786 * 2 ^ 59
def prefixEnd_282786 : Nat := 4983230072969 + 3 ^ 40 * 282786 * 2
def baseEnd_282786 : Nat := 16133904484715092463833

theorem tailTrace_282786 : CollatzResearch.WordTrace tailWord_282786 prefixEnd_282786 16133904484715092463833 := by
  unfold tailWord_282786
  simp only [CollatzResearch.WordTrace]
  refine ⟨2578513188380523212217053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6876035169014728565912141 2578513188380523212217053)
  ·
    refine ⟨966942445642696204581395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2578513188380523212217053 966942445642696204581395)
    ·
      refine ⟨1450413668464044306872093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 966942445642696204581395 1450413668464044306872093)
      ·
        refine ⟨543905125674016615077035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1450413668464044306872093 543905125674016615077035)
        ·
          refine ⟨815857688511024922615553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 543905125674016615077035 815857688511024922615553)
          ·
            refine ⟨611893266383268691961665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 815857688511024922615553 611893266383268691961665)
            ·
              refine ⟨458919949787451518971249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 611893266383268691961665 458919949787451518971249)
              ·
                refine ⟨344189962340588639228437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 458919949787451518971249 344189962340588639228437)
                ·
                  refine ⟨16133904484715092463833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 344189962340588639228437 16133904484715092463833)
                  ·
                    rfl

theorem cell23_282786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_282786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282786 prefixEnd_282786 := by exact prefixLift 282786
  have htrace : WordTrace (prefixWord ++ tailWord_282786) baseStart_282786 baseEnd_282786 := by
    simpa [prefixWord, tailWord_282786, baseEnd_282786] using wordTrace_append hprefix tailTrace_282786
  have hstable : (prefixWord ++ tailWord_282786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282786).length < 2 ^ (prefixWord ++ tailWord_282786).sum := by decide
  have hdescent : baseEnd_282786 < baseStart_282786 := by decide
  rcases family_descends (prefixWord ++ tailWord_282786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282830 : List Nat := [4, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3]
def baseStart_282830 : Nat := 118140960795 + 282830 * 2 ^ 59
def prefixEnd_282830 : Nat := 4983230072969 + 3 ^ 40 * 282830 * 2
def baseEnd_282830 : Nat := 145227733511233660024295

theorem tailTrace_282830 : CollatzResearch.WordTrace tailWord_282830 prefixEnd_282830 145227733511233660024295 := by
  unfold tailWord_282830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1289457195670336045433743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6877105043575125575646629 1289457195670336045433743)
  ·
    refine ⟨1934185793505504068150615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1289457195670336045433743 1934185793505504068150615)
    ·
      refine ⟨2901278690258256102225923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1934185793505504068150615 2901278690258256102225923)
      ·
        refine ⟨4351918035387384153338885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2901278690258256102225923 4351918035387384153338885)
        ·
          refine ⟨815984631635134528751041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4351918035387384153338885 815984631635134528751041)
          ·
            refine ⟨611988473726350896563281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 815984631635134528751041 611988473726350896563281)
            ·
              refine ⟨458991355294763172422461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 611988473726350896563281 458991355294763172422461)
              ·
                refine ⟨172121758235536189658423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 458991355294763172422461 172121758235536189658423)
                ·
                  refine ⟨258182637353304284487635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 172121758235536189658423 258182637353304284487635)
                  ·
                    refine ⟨387273956029956426731453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 258182637353304284487635 387273956029956426731453)
                    ·
                      refine ⟨145227733511233660024295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 387273956029956426731453 145227733511233660024295)
                      ·
                        rfl

theorem cell23_282830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3].length) (baseStart_282830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282830 prefixEnd_282830 := by exact prefixLift 282830
  have htrace : WordTrace (prefixWord ++ tailWord_282830) baseStart_282830 baseEnd_282830 := by
    simpa [prefixWord, tailWord_282830, baseEnd_282830] using wordTrace_append hprefix tailTrace_282830
  have hstable : (prefixWord ++ tailWord_282830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282830).length < 2 ^ (prefixWord ++ tailWord_282830).sum := by decide
  have hdescent : baseEnd_282830 < baseStart_282830 := by decide
  rcases family_descends (prefixWord ++ tailWord_282830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282852 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 2, 2, 7]
def baseStart_282852 : Nat := 118140960795 + 282852 * 2 ^ 59
def prefixEnd_282852 : Nat := 4983230072969 + 3 ^ 40 * 282852 * 2
def baseEnd_282852 : Nat := 145239030085632573949193

theorem tailTrace_282852 : CollatzResearch.WordTrace tailWord_282852 prefixEnd_282852 145239030085632573949193 := by
  unfold tailWord_282852
  simp only [CollatzResearch.WordTrace]
  refine ⟨5158229985641493060385405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6877639980855324080513873 5158229985641493060385405)
  ·
    refine ⟨1934336244615559897644527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5158229985641493060385405 1934336244615559897644527)
    ·
      refine ⟨2901504366923339846466791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1934336244615559897644527 2901504366923339846466791)
      ·
        refine ⟨4352256550385009769700187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2901504366923339846466791 4352256550385009769700187)
        ·
          refine ⟨6528384825577514654550281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4352256550385009769700187 6528384825577514654550281)
          ·
            refine ⟨4896288619183135990912711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6528384825577514654550281 4896288619183135990912711)
            ·
              refine ⟨7344432928774703986369067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4896288619183135990912711 7344432928774703986369067)
              ·
                refine ⟨11016649393162055979553601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7344432928774703986369067 11016649393162055979553601)
                ·
                  refine ⟨8262487044871541984665201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11016649393162055979553601 8262487044871541984665201)
                  ·
                    refine ⟨6196865283653656488498901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8262487044871541984665201 6196865283653656488498901)
                    ·
                      refine ⟨145239030085632573949193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6196865283653656488498901 145239030085632573949193)
                      ·
                        rfl

theorem cell23_282852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_282852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282852 prefixEnd_282852 := by exact prefixLift 282852
  have htrace : WordTrace (prefixWord ++ tailWord_282852) baseStart_282852 baseEnd_282852 := by
    simpa [prefixWord, tailWord_282852, baseEnd_282852] using wordTrace_append hprefix tailTrace_282852
  have hstable : (prefixWord ++ tailWord_282852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282852).length < 2 ^ (prefixWord ++ tailWord_282852).sum := by decide
  have hdescent : baseEnd_282852 < baseStart_282852 := by decide
  rcases family_descends (prefixWord ++ tailWord_282852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282853 : List Nat := [1, 3, 1, 4, 2, 1, 1, 3, 3, 2, 2]
def baseStart_282853 : Nat := 118140960795 + 282853 * 2 ^ 59
def prefixEnd_282853 : Nat := 4983230072969 + 3 ^ 40 * 282853 * 2
def baseEnd_282853 : Nat := 145239543566287070036689

theorem tailTrace_282853 : CollatzResearch.WordTrace tailWord_282853 prefixEnd_282853 145239543566287070036689 := by
  unfold tailWord_282853
  simp only [CollatzResearch.WordTrace]
  refine ⟨10316496444279363291557213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6877664296186242194371475 10316496444279363291557213)
  ·
    refine ⟨3868686166604761234333955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10316496444279363291557213 3868686166604761234333955)
    ·
      refine ⟨5803029249907141851500933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3868686166604761234333955 5803029249907141851500933)
      ·
        refine ⟨1088067984357589097156425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5803029249907141851500933 1088067984357589097156425)
        ·
          refine ⟨816050988268191822867319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1088067984357589097156425 816050988268191822867319)
          ·
            refine ⟨1224076482402287734300979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 816050988268191822867319 1224076482402287734300979)
            ·
              refine ⟨1836114723603431601451469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1224076482402287734300979 1836114723603431601451469)
              ·
                refine ⟨688543021351286850544301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1836114723603431601451469 688543021351286850544301)
                ·
                  refine ⟨258203633006732568954113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 688543021351286850544301 258203633006732568954113)
                  ·
                    refine ⟨193652724755049426715585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 258203633006732568954113 193652724755049426715585)
                    ·
                      refine ⟨145239543566287070036689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 193652724755049426715585 145239543566287070036689)
                      ·
                        rfl

theorem cell23_282853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_282853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282853 prefixEnd_282853 := by exact prefixLift 282853
  have htrace : WordTrace (prefixWord ++ tailWord_282853) baseStart_282853 baseEnd_282853 := by
    simpa [prefixWord, tailWord_282853, baseEnd_282853] using wordTrace_append hprefix tailTrace_282853
  have hstable : (prefixWord ++ tailWord_282853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282853).length < 2 ^ (prefixWord ++ tailWord_282853).sum := by decide
  have hdescent : baseEnd_282853 < baseStart_282853 := by decide
  rcases family_descends (prefixWord ++ tailWord_282853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282863 : List Nat := [1, 1, 2, 1, 6, 2, 3, 1, 2, 4]
def baseStart_282863 : Nat := 118140960795 + 282863 * 2 ^ 59
def prefixEnd_282863 : Nat := 4983230072969 + 3 ^ 40 * 282863 * 2
def baseEnd_282863 : Nat := 48414892790944010303881

theorem tailTrace_282863 : CollatzResearch.WordTrace tailWord_282863 prefixEnd_282863 48414892790944010303881 := by
  unfold tailWord_282863
  simp only [CollatzResearch.WordTrace]
  refine ⟨10316861174243134999421243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6877907449495423332947495 10316861174243134999421243)
  ·
    refine ⟨15475291761364702499131865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10316861174243134999421243 15475291761364702499131865)
    ·
      refine ⟨11606468821023526874348899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15475291761364702499131865 11606468821023526874348899)
      ·
        refine ⟨17409703231535290311523349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11606468821023526874348899 17409703231535290311523349)
        ·
          refine ⟨816079838978216733352657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17409703231535290311523349 816079838978216733352657)
          ·
            refine ⟨612059879233662550014493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 816079838978216733352657 612059879233662550014493)
            ·
              refine ⟨229522454712623456255435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 612059879233662550014493 229522454712623456255435)
              ·
                refine ⟨344283682068935184383153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229522454712623456255435 344283682068935184383153)
                ·
                  refine ⟨258212761551701388287365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 344283682068935184383153 258212761551701388287365)
                  ·
                    refine ⟨48414892790944010303881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 258212761551701388287365 48414892790944010303881)
                    ·
                      rfl

theorem cell23_282863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 2, 4].length) (baseStart_282863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282863 prefixEnd_282863 := by exact prefixLift 282863
  have htrace : WordTrace (prefixWord ++ tailWord_282863) baseStart_282863 baseEnd_282863 := by
    simpa [prefixWord, tailWord_282863, baseEnd_282863] using wordTrace_append hprefix tailTrace_282863
  have hstable : (prefixWord ++ tailWord_282863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282863).length < 2 ^ (prefixWord ++ tailWord_282863).sum := by decide
  have hdescent : baseEnd_282863 < baseStart_282863 := by decide
  rcases family_descends (prefixWord ++ tailWord_282863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282866 : List Nat := [3, 2, 1, 3, 2, 1, 3, 1, 1, 2, 4]
def baseStart_282866 : Nat := 118140960795 + 282866 * 2 ^ 59
def prefixEnd_282866 : Nat := 4983230072969 + 3 ^ 40 * 282866 * 2
def baseEnd_282866 : Nat := 145246218814795519174129

theorem tailTrace_282866 : CollatzResearch.WordTrace tailWord_282866 prefixEnd_282866 145246218814795519174129 := by
  unfold tailWord_282866
  simp only [CollatzResearch.WordTrace]
  refine ⟨2579242648308066627945113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6877980395488177674520301 2579242648308066627945113)
  ·
    refine ⟨1934431986231049970958835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2579242648308066627945113 1934431986231049970958835)
    ·
      refine ⟨2901647979346574956438253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1934431986231049970958835 2901647979346574956438253)
      ·
        refine ⟨1088117992254965608664345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2901647979346574956438253 1088117992254965608664345)
        ·
          refine ⟨816088494191224206498259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1088117992254965608664345 816088494191224206498259)
          ·
            refine ⟨1224132741286836309747389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 816088494191224206498259 1224132741286836309747389)
            ·
              refine ⟨459049777982563616155271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1224132741286836309747389 459049777982563616155271)
              ·
                refine ⟨688574666973845424232907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 459049777982563616155271 688574666973845424232907)
                ·
                  refine ⟨1032862000460768136349361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 688574666973845424232907 1032862000460768136349361)
                  ·
                    refine ⟨774646500345576102262021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1032862000460768136349361 774646500345576102262021)
                    ·
                      refine ⟨145246218814795519174129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 774646500345576102262021 145246218814795519174129)
                      ·
                        rfl

theorem cell23_282866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_282866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282866 prefixEnd_282866 := by exact prefixLift 282866
  have htrace : WordTrace (prefixWord ++ tailWord_282866) baseStart_282866 baseEnd_282866 := by
    simpa [prefixWord, tailWord_282866, baseEnd_282866] using wordTrace_append hprefix tailTrace_282866
  have hstable : (prefixWord ++ tailWord_282866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282866).length < 2 ^ (prefixWord ++ tailWord_282866).sum := by decide
  have hdescent : baseEnd_282866 < baseStart_282866 := by decide
  rcases family_descends (prefixWord ++ tailWord_282866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282872 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 2, 7]
def baseStart_282872 : Nat := 118140960795 + 282872 * 2 ^ 59
def prefixEnd_282872 : Nat := 4983230072969 + 3 ^ 40 * 282872 * 2
def baseEnd_282872 : Nat := 48416433232907498566367

theorem tailTrace_282872 : CollatzResearch.WordTrace tailWord_282872 prefixEnd_282872 48416433232907498566367 := by
  unfold tailWord_282872
  simp only [CollatzResearch.WordTrace]
  refine ⟨5158594715605264768249435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6878126287473686357665913 5158594715605264768249435)
  ·
    refine ⟨7737892073407897152374153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5158594715605264768249435 7737892073407897152374153)
    ·
      refine ⟨5803419055055922864280615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7737892073407897152374153 5803419055055922864280615)
      ·
        refine ⟨8705128582583884296420923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5803419055055922864280615 8705128582583884296420923)
        ·
          refine ⟨13057692873875826444631385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8705128582583884296420923 13057692873875826444631385)
          ·
            refine ⟨9793269655406869833473539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13057692873875826444631385 9793269655406869833473539)
            ·
              refine ⟨14689904483110304750210309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9793269655406869833473539 14689904483110304750210309)
              ·
                refine ⟨2754357090583182140664433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14689904483110304750210309 2754357090583182140664433)
                ·
                  refine ⟨2065767817937386605498325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2754357090583182140664433 2065767817937386605498325)
                  ·
                    refine ⟨48416433232907498566367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2065767817937386605498325 48416433232907498566367)
                    ·
                      rfl

theorem cell23_282872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 2, 7].length) (baseStart_282872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282872 prefixEnd_282872 := by exact prefixLift 282872
  have htrace : WordTrace (prefixWord ++ tailWord_282872) baseStart_282872 baseEnd_282872 := by
    simpa [prefixWord, tailWord_282872, baseEnd_282872] using wordTrace_append hprefix tailTrace_282872
  have hstable : (prefixWord ++ tailWord_282872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282872).length < 2 ^ (prefixWord ++ tailWord_282872).sum := by decide
  have hdescent : baseEnd_282872 < baseStart_282872 := by decide
  rcases family_descends (prefixWord ++ tailWord_282872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282876 : List Nat := [2, 2, 2, 1, 4, 3, 2, 7]
def baseStart_282876 : Nat := 118140960795 + 282876 * 2 ^ 59
def prefixEnd_282876 : Nat := 4983230072969 + 3 ^ 40 * 282876 * 2
def baseEnd_282876 : Nat := 5379679763753351112929

theorem tailTrace_282876 : CollatzResearch.WordTrace tailWord_282876 prefixEnd_282876 5379679763753351112929 := by
  unfold tailWord_282876
  simp only [CollatzResearch.WordTrace]
  refine ⟨5158667661598019109822241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6878223548797358813096321 5158667661598019109822241)
  ·
    refine ⟨3869000746198514332366681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5158667661598019109822241 3869000746198514332366681)
    ·
      refine ⟨2901750559648885749275011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3869000746198514332366681 2901750559648885749275011)
      ·
        refine ⟨4352625839473328623912517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2901750559648885749275011 4352625839473328623912517)
        ·
          refine ⟨816117344901249116983597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4352625839473328623912517 816117344901249116983597)
          ·
            refine ⟨306044004337968418868849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 816117344901249116983597 306044004337968418868849)
            ·
              refine ⟨229533003253476314151637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 306044004337968418868849 229533003253476314151637)
              ·
                refine ⟨5379679763753351112929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 229533003253476314151637 5379679763753351112929)
                ·
                  rfl

theorem cell23_282876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 7].length) (baseStart_282876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282876 prefixEnd_282876 := by exact prefixLift 282876
  have htrace : WordTrace (prefixWord ++ tailWord_282876) baseStart_282876 baseEnd_282876 := by
    simpa [prefixWord, tailWord_282876, baseEnd_282876] using wordTrace_append hprefix tailTrace_282876
  have hstable : (prefixWord ++ tailWord_282876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282876).length < 2 ^ (prefixWord ++ tailWord_282876).sum := by decide
  have hdescent : baseEnd_282876 < baseStart_282876 := by decide
  rcases family_descends (prefixWord ++ tailWord_282876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282920 : List Nat := [2, 1, 5, 1, 3, 1, 1, 3, 2, 1, 3]
def baseStart_282920 : Nat := 118140960795 + 282920 * 2 ^ 59
def prefixEnd_282920 : Nat := 4983230072969 + 3 ^ 40 * 282920 * 2
def baseEnd_282920 : Nat := 145273946770138307898881

theorem tailTrace_282920 : CollatzResearch.WordTrace tailWord_282920 prefixEnd_282920 145273946770138307898881 := by
  unfold tailWord_282920
  simp only [CollatzResearch.WordTrace]
  refine ⟨5159470067518316867123107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6879293423357755822830809 5159470067518316867123107)
  ·
    refine ⟨7739205101277475300684661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5159470067518316867123107 7739205101277475300684661)
    ·
      refine ⟨725550478244763309439187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7739205101277475300684661 725550478244763309439187)
      ·
        refine ⟨1088325717367144964158781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 725550478244763309439187 1088325717367144964158781)
        ·
          refine ⟨408122144012679361559543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1088325717367144964158781 408122144012679361559543)
          ·
            refine ⟨612183216019019042339315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408122144012679361559543 612183216019019042339315)
            ·
              refine ⟨918274824028528563508973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 612183216019019042339315 918274824028528563508973)
              ·
                refine ⟨344353059010698211315865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 918274824028528563508973 344353059010698211315865)
                ·
                  refine ⟨258264794258023658486899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 344353059010698211315865 258264794258023658486899)
                  ·
                    refine ⟨387397191387035487730349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 258264794258023658486899 387397191387035487730349)
                    ·
                      refine ⟨145273946770138307898881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 387397191387035487730349 145273946770138307898881)
                      ·
                        rfl

theorem cell23_282920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_282920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282920 prefixEnd_282920 := by exact prefixLift 282920
  have htrace : WordTrace (prefixWord ++ tailWord_282920) baseStart_282920 baseEnd_282920 := by
    simpa [prefixWord, tailWord_282920, baseEnd_282920] using wordTrace_append hprefix tailTrace_282920
  have hstable : (prefixWord ++ tailWord_282920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282920).length < 2 ^ (prefixWord ++ tailWord_282920).sum := by decide
  have hdescent : baseEnd_282920 < baseStart_282920 := by decide
  rcases family_descends (prefixWord ++ tailWord_282920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282960 : List Nat := [2, 1, 1, 1, 1, 7, 2, 2, 2, 2, 2]
def baseStart_282960 : Nat := 118140960795 + 282960 * 2 ^ 59
def prefixEnd_282960 : Nat := 4983230072969 + 3 ^ 40 * 282960 * 2
def baseEnd_282960 : Nat := 145294485996318151398697

theorem tailTrace_282960 : CollatzResearch.WordTrace tailWord_282960 prefixEnd_282960 145294485996318151398697 := by
  unfold tailWord_282960
  simp only [CollatzResearch.WordTrace]
  refine ⟨5160199527445860282851167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6880266036594480377134889 5160199527445860282851167)
  ·
    refine ⟨7740299291168790424276751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5160199527445860282851167 7740299291168790424276751)
    ·
      refine ⟨11610448936753185636415127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7740299291168790424276751 11610448936753185636415127)
      ·
        refine ⟨17415673405129778454622691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11610448936753185636415127 17415673405129778454622691)
        ·
          refine ⟨26123510107694667681934037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17415673405129778454622691 26123510107694667681934037)
          ·
            refine ⟨612269768149093773795329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 26123510107694667681934037 612269768149093773795329)
            ·
              refine ⟨459202326111820330346497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 612269768149093773795329 459202326111820330346497)
              ·
                refine ⟨344401744583865247759873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 459202326111820330346497 344401744583865247759873)
                ·
                  refine ⟨258301308437898935819905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 344401744583865247759873 258301308437898935819905)
                  ·
                    refine ⟨193725981328424201864929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 258301308437898935819905 193725981328424201864929)
                    ·
                      refine ⟨145294485996318151398697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 193725981328424201864929 145294485996318151398697)
                      ·
                        rfl

theorem cell23_282960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 2, 2, 2].length) (baseStart_282960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282960 prefixEnd_282960 := by exact prefixLift 282960
  have htrace : WordTrace (prefixWord ++ tailWord_282960) baseStart_282960 baseEnd_282960 := by
    simpa [prefixWord, tailWord_282960, baseEnd_282960] using wordTrace_append hprefix tailTrace_282960
  have hstable : (prefixWord ++ tailWord_282960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282960).length < 2 ^ (prefixWord ++ tailWord_282960).sum := by decide
  have hdescent : baseEnd_282960 < baseStart_282960 := by decide
  rcases family_descends (prefixWord ++ tailWord_282960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282979 : List Nat := [1, 1, 1, 5, 2, 1, 2, 2, 1, 7]
def baseStart_282979 : Nat := 118140960795 + 282979 * 2 ^ 59
def prefixEnd_282979 : Nat := 4983230072969 + 3 ^ 40 * 282979 * 2
def baseEnd_282979 : Nat := 48434747376251192353703

theorem tailTrace_282979 : CollatzResearch.WordTrace tailWord_282979 prefixEnd_282979 48434747376251192353703 := by
  unfold tailWord_282979
  simp only [CollatzResearch.WordTrace]
  refine ⟨10321092041822886810643991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6880728027881924540429327 10321092041822886810643991)
  ·
    refine ⟨15481638062734330215965987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10321092041822886810643991 15481638062734330215965987)
    ·
      refine ⟨23222457094101495323948981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15481638062734330215965987 23222457094101495323948981)
      ·
        refine ⟨2177105352572015186620217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23222457094101495323948981 2177105352572015186620217)
        ·
          refine ⟨1632829014429011389965163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2177105352572015186620217 1632829014429011389965163)
          ·
            refine ⟨2449243521643517084947745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1632829014429011389965163 2449243521643517084947745)
            ·
              refine ⟨1836932641232637813710809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2449243521643517084947745 1836932641232637813710809)
              ·
                refine ⟨1377699480924478360283107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1836932641232637813710809 1377699480924478360283107)
                ·
                  refine ⟨2066549221386717540424661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1377699480924478360283107 2066549221386717540424661)
                  ·
                    refine ⟨48434747376251192353703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2066549221386717540424661 48434747376251192353703)
                    ·
                      rfl

theorem cell23_282979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 7].length) (baseStart_282979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_282979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_282979 prefixEnd_282979 := by exact prefixLift 282979
  have htrace : WordTrace (prefixWord ++ tailWord_282979) baseStart_282979 baseEnd_282979 := by
    simpa [prefixWord, tailWord_282979, baseEnd_282979] using wordTrace_append hprefix tailTrace_282979
  have hstable : (prefixWord ++ tailWord_282979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282979).length < 2 ^ (prefixWord ++ tailWord_282979).sum := by decide
  have hdescent : baseEnd_282979 < baseStart_282979 := by decide
  rcases family_descends (prefixWord ++ tailWord_282979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283016 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 4, 1, 4]
def baseStart_283016 : Nat := 118140960795 + 283016 * 2 ^ 59
def prefixEnd_283016 : Nat := 4983230072969 + 3 ^ 40 * 283016 * 2
def baseEnd_283016 : Nat := 145323240912969932298439

theorem tailTrace_283016 : CollatzResearch.WordTrace tailWord_283016 prefixEnd_283016 145323240912969932298439 := by
  unfold tailWord_283016
  simp only [CollatzResearch.WordTrace]
  refine ⟨5161220771344421064870451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6881627695125894753160601 5161220771344421064870451)
  ·
    refine ⟨7741831157016631597305677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5161220771344421064870451 7741831157016631597305677)
    ·
      refine ⟨2903186683881236848989629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7741831157016631597305677 2903186683881236848989629)
      ·
        refine ⟨1088695006455463818371111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2903186683881236848989629 1088695006455463818371111)
        ·
          refine ⟨1633042509683195727556667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1088695006455463818371111 1633042509683195727556667)
          ·
            refine ⟨2449563764524793591335001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1633042509683195727556667 2449563764524793591335001)
            ·
              refine ⟨1837172823393595193501251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2449563764524793591335001 1837172823393595193501251)
              ·
                refine ⟨2755759235090392790251877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1837172823393595193501251 2755759235090392790251877)
                ·
                  refine ⟨516704856579448648172227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2755759235090392790251877 516704856579448648172227)
                  ·
                    refine ⟨775057284869172972258341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 516704856579448648172227 775057284869172972258341)
                    ·
                      refine ⟨145323240912969932298439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 775057284869172972258341 145323240912969932298439)
                      ·
                        rfl

theorem cell23_283016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_283016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283016 prefixEnd_283016 := by exact prefixLift 283016
  have htrace : WordTrace (prefixWord ++ tailWord_283016) baseStart_283016 baseEnd_283016 := by
    simpa [prefixWord, tailWord_283016, baseEnd_283016] using wordTrace_append hprefix tailTrace_283016
  have hstable : (prefixWord ++ tailWord_283016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283016).length < 2 ^ (prefixWord ++ tailWord_283016).sum := by decide
  have hdescent : baseEnd_283016 < baseStart_283016 := by decide
  rcases family_descends (prefixWord ++ tailWord_283016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283029 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 4, 1, 6]
def baseStart_283029 : Nat := 118140960795 + 283029 * 2 ^ 59
def prefixEnd_283029 : Nat := 4983230072969 + 3 ^ 40 * 283029 * 2
def baseEnd_283029 : Nat := 145329916161478381435879

theorem tailTrace_283029 : CollatzResearch.WordTrace tailWord_283029 prefixEnd_283029 145329916161478381435879 := by
  unfold tailWord_283029
  simp only [CollatzResearch.WordTrace]
  refine ⟨10322915691641745349964141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6881943794427830233309427 10322915691641745349964141)
  ·
    refine ⟨3871093384365654506236553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10322915691641745349964141 3871093384365654506236553)
    ·
      refine ⟨2903320038274240879677415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3871093384365654506236553 2903320038274240879677415)
      ·
        refine ⟨4354980057411361319516123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2903320038274240879677415 4354980057411361319516123)
        ·
          refine ⟨6532470086117041979274185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4354980057411361319516123 6532470086117041979274185)
          ·
            refine ⟨4899352564587781484455639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6532470086117041979274185 4899352564587781484455639)
            ·
              refine ⟨7349028846881672226683459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4899352564587781484455639 7349028846881672226683459)
              ·
                refine ⟨11023543270322508340025189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7349028846881672226683459 11023543270322508340025189)
                ·
                  refine ⟨2066914363185470313754723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11023543270322508340025189 2066914363185470313754723)
                  ·
                    refine ⟨3100371544778205470632085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2066914363185470313754723 3100371544778205470632085)
                    ·
                      refine ⟨145329916161478381435879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3100371544778205470632085 145329916161478381435879)
                      ·
                        rfl

theorem cell23_283029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_283029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283029 prefixEnd_283029 := by exact prefixLift 283029
  have htrace : WordTrace (prefixWord ++ tailWord_283029) baseStart_283029 baseEnd_283029 := by
    simpa [prefixWord, tailWord_283029, baseEnd_283029] using wordTrace_append hprefix tailTrace_283029
  have hstable : (prefixWord ++ tailWord_283029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283029).length < 2 ^ (prefixWord ++ tailWord_283029).sum := by decide
  have hdescent : baseEnd_283029 < baseStart_283029 := by decide
  rcases family_descends (prefixWord ++ tailWord_283029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283086 : List Nat := [4, 1, 1, 1, 2, 1, 1, 4, 3, 5]
def baseStart_283086 : Nat := 118140960795 + 283086 * 2 ^ 59
def prefixEnd_283086 : Nat := 4983230072969 + 3 ^ 40 * 283086 * 2
def baseEnd_283086 : Nat := 48453061519594886141039

theorem tailTrace_283086 : CollatzResearch.WordTrace tailWord_283086 prefixEnd_283086 48453061519594886141039 := by
  unfold tailWord_283086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1290624331554405510598639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6883329768290162723192741 1290624331554405510598639)
  ·
    refine ⟨1935936497331608265897959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1290624331554405510598639 1935936497331608265897959)
    ·
      refine ⟨2903904745997412398846939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1935936497331608265897959 2903904745997412398846939)
      ·
        refine ⟨4355857118996118598270409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2903904745997412398846939 4355857118996118598270409)
        ·
          refine ⟨3266892839247088948702807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4355857118996118598270409 3266892839247088948702807)
          ·
            refine ⟨4900339258870633423054211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3266892839247088948702807 4900339258870633423054211)
            ·
              refine ⟨7350508888305950134581317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4900339258870633423054211 7350508888305950134581317)
              ·
                refine ⟨1378220416557365650233997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7350508888305950134581317 1378220416557365650233997)
                ·
                  refine ⟨516832656209012118837749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1378220416557365650233997 516832656209012118837749)
                  ·
                    refine ⟨48453061519594886141039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 516832656209012118837749 48453061519594886141039)
                    ·
                      rfl

theorem cell23_283086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_283086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283086 prefixEnd_283086 := by exact prefixLift 283086
  have htrace : WordTrace (prefixWord ++ tailWord_283086) baseStart_283086 baseEnd_283086 := by
    simpa [prefixWord, tailWord_283086, baseEnd_283086] using wordTrace_append hprefix tailTrace_283086
  have hstable : (prefixWord ++ tailWord_283086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283086).length < 2 ^ (prefixWord ++ tailWord_283086).sum := by decide
  have hdescent : baseEnd_283086 < baseStart_283086 := by decide
  rcases family_descends (prefixWord ++ tailWord_283086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283090 : List Nat := [3, 2, 2, 4, 1, 1, 1, 3, 6]
def baseStart_283090 : Nat := 118140960795 + 283090 * 2 ^ 59
def prefixEnd_283090 : Nat := 4983230072969 + 3 ^ 40 * 283090 * 2
def baseEnd_283090 : Nat := 16151248720155849197011

theorem tailTrace_283090 : CollatzResearch.WordTrace tailWord_283090 prefixEnd_283090 16151248720155849197011 := by
  unfold tailWord_283090
  simp only [CollatzResearch.WordTrace]
  refine ⟨2581285136105188191983681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6883427029613835178623149 2581285136105188191983681)
  ·
    refine ⟨1935963852078891143987761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2581285136105188191983681 1935963852078891143987761)
    ·
      refine ⟨1451972889059168357990821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1935963852078891143987761 1451972889059168357990821)
      ·
        refine ⟨272244916698594067123279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1451972889059168357990821 272244916698594067123279)
        ·
          refine ⟨408367375047891100684919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272244916698594067123279 408367375047891100684919)
          ·
            refine ⟨612551062571836651027379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408367375047891100684919 612551062571836651027379)
            ·
              refine ⟨918826593857754976541069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 612551062571836651027379 918826593857754976541069)
              ·
                refine ⟨344559972696658116202901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 918826593857754976541069 344559972696658116202901)
                ·
                  refine ⟨16151248720155849197011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 344559972696658116202901 16151248720155849197011)
                  ·
                    rfl

theorem cell23_283090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 6].length) (baseStart_283090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283090 prefixEnd_283090 := by exact prefixLift 283090
  have htrace : WordTrace (prefixWord ++ tailWord_283090) baseStart_283090 baseEnd_283090 := by
    simpa [prefixWord, tailWord_283090, baseEnd_283090] using wordTrace_append hprefix tailTrace_283090
  have hstable : (prefixWord ++ tailWord_283090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283090).length < 2 ^ (prefixWord ++ tailWord_283090).sum := by decide
  have hdescent : baseEnd_283090 < baseStart_283090 := by decide
  rcases family_descends (prefixWord ++ tailWord_283090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283103 : List Nat := [1, 1, 2, 3, 3, 2, 3, 2, 1, 5]
def baseStart_283103 : Nat := 118140960795 + 283103 * 2 ^ 59
def prefixEnd_283103 : Nat := 4983230072969 + 3 ^ 40 * 283103 * 2
def baseEnd_283103 : Nat := 48455971243303697303513

theorem tailTrace_283103 : CollatzResearch.WordTrace tailWord_283103 prefixEnd_283103 48455971243303697303513 := by
  unfold tailWord_283103
  simp only [CollatzResearch.WordTrace]
  refine ⟨10325614693373655988157963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6883743128915770658771975 10325614693373655988157963)
  ·
    refine ⟨15488422040060483982236945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10325614693373655988157963 15488422040060483982236945)
    ·
      refine ⟨11616316530045362986677709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15488422040060483982236945 11616316530045362986677709)
      ·
        refine ⟨4356118698767011120004141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11616316530045362986677709 4356118698767011120004141)
        ·
          refine ⟨1633544512037629170001553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4356118698767011120004141 1633544512037629170001553)
          ·
            refine ⟨1225158384028221877501165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1633544512037629170001553 1225158384028221877501165)
            ·
              refine ⟨459434394010583204062937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1225158384028221877501165 459434394010583204062937)
              ·
                refine ⟨344575795507937403047203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 459434394010583204062937 344575795507937403047203)
                ·
                  refine ⟨516863693261906104570805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 344575795507937403047203 516863693261906104570805)
                  ·
                    refine ⟨48455971243303697303513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 516863693261906104570805 48455971243303697303513)
                    ·
                      rfl

theorem cell23_283103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 5].length) (baseStart_283103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283103 prefixEnd_283103 := by exact prefixLift 283103
  have htrace : WordTrace (prefixWord ++ tailWord_283103) baseStart_283103 baseEnd_283103 := by
    simpa [prefixWord, tailWord_283103, baseEnd_283103] using wordTrace_append hprefix tailTrace_283103
  have hstable : (prefixWord ++ tailWord_283103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283103).length < 2 ^ (prefixWord ++ tailWord_283103).sum := by decide
  have hdescent : baseEnd_283103 < baseStart_283103 := by decide
  rcases family_descends (prefixWord ++ tailWord_283103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283116 : List Nat := [2, 2, 1, 1, 2, 1, 5, 2, 1, 6]
def baseStart_283116 : Nat := 118140960795 + 283116 * 2 ^ 59
def prefixEnd_283116 : Nat := 4983230072969 + 3 ^ 40 * 283116 * 2
def baseEnd_283116 : Nat := 48458196326139847015993

theorem tailTrace_283116 : CollatzResearch.WordTrace tailWord_283116 prefixEnd_283116 48458196326139847015993 := by
  unfold tailWord_283116
  simp only [CollatzResearch.WordTrace]
  refine ⟨5163044421163279604190601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6884059228217706138920801 5163044421163279604190601)
  ·
    refine ⟨3872283315872459703142951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5163044421163279604190601 3872283315872459703142951)
    ·
      refine ⟨5808424973808689554714427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3872283315872459703142951 5808424973808689554714427)
      ·
        refine ⟨8712637460713034332071641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5808424973808689554714427 8712637460713034332071641)
        ·
          refine ⟨6534478095534775749053731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8712637460713034332071641 6534478095534775749053731)
          ·
            refine ⟨9801717143302163623580597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6534478095534775749053731 9801717143302163623580597)
            ·
              refine ⟨918910982184577839710681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9801717143302163623580597 918910982184577839710681)
              ·
                refine ⟨689183236638433379783011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 918910982184577839710681 689183236638433379783011)
                ·
                  refine ⟨1033774854957650069674517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 689183236638433379783011 1033774854957650069674517)
                  ·
                    refine ⟨48458196326139847015993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1033774854957650069674517 48458196326139847015993)
                    ·
                      rfl

theorem cell23_283116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 6].length) (baseStart_283116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283116 prefixEnd_283116 := by exact prefixLift 283116
  have htrace : WordTrace (prefixWord ++ tailWord_283116) baseStart_283116 baseEnd_283116 := by
    simpa [prefixWord, tailWord_283116, baseEnd_283116] using wordTrace_append hprefix tailTrace_283116
  have hstable : (prefixWord ++ tailWord_283116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283116).length < 2 ^ (prefixWord ++ tailWord_283116).sum := by decide
  have hdescent : baseEnd_283116 < baseStart_283116 := by decide
  rcases family_descends (prefixWord ++ tailWord_283116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283150 : List Nat := [4, 1, 1, 2, 3, 1, 2, 3, 2, 4]
def baseStart_283150 : Nat := 118140960795 + 283150 * 2 ^ 59
def prefixEnd_283150 : Nat := 4983230072969 + 3 ^ 40 * 283150 * 2
def baseEnd_283150 : Nat := 48464015773557469340941

theorem tailTrace_283150 : CollatzResearch.WordTrace tailWord_283150 prefixEnd_283150 48464015773557469340941 := by
  unfold tailWord_283150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1290916115525422876889863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6884885949468922010079269 1290916115525422876889863)
  ·
    refine ⟨1936374173288134315334795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1290916115525422876889863 1936374173288134315334795)
    ·
      refine ⟨2904561259932201473002193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1936374173288134315334795 2904561259932201473002193)
      ·
        refine ⟨2178420944949151104751645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2904561259932201473002193 2178420944949151104751645)
        ·
          refine ⟨816907854355931664281867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2178420944949151104751645 816907854355931664281867)
          ·
            refine ⟨1225361781533897496422801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 816907854355931664281867 1225361781533897496422801)
            ·
              refine ⟨919021336150423122317101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1225361781533897496422801 919021336150423122317101)
              ·
                refine ⟨344633001056408670868913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 919021336150423122317101 344633001056408670868913)
                ·
                  refine ⟨258474750792306503151685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 344633001056408670868913 258474750792306503151685)
                  ·
                    refine ⟨48464015773557469340941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 258474750792306503151685 48464015773557469340941)
                    ·
                      rfl

theorem cell23_283150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_283150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283150 prefixEnd_283150 := by exact prefixLift 283150
  have htrace : WordTrace (prefixWord ++ tailWord_283150) baseStart_283150 baseEnd_283150 := by
    simpa [prefixWord, tailWord_283150, baseEnd_283150] using wordTrace_append hprefix tailTrace_283150
  have hstable : (prefixWord ++ tailWord_283150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283150).length < 2 ^ (prefixWord ++ tailWord_283150).sum := by decide
  have hdescent : baseEnd_283150 < baseStart_283150 := by decide
  rcases family_descends (prefixWord ++ tailWord_283150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283173 : List Nat := [1, 3, 1, 2, 2, 1, 4, 2, 1, 3, 3]
def baseStart_283173 : Nat := 118140960795 + 283173 * 2 ^ 59
def prefixEnd_283173 : Nat := 4983230072969 + 3 ^ 40 * 283173 * 2
def baseEnd_283173 : Nat := 145403857375725818035217

theorem tailTrace_283173 : CollatzResearch.WordTrace tailWord_283173 prefixEnd_283173 145403857375725818035217 := by
  unfold tailWord_283173
  simp only [CollatzResearch.WordTrace]
  refine ⟨10328167803120057943206173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6885445202080038628804115 10328167803120057943206173)
  ·
    refine ⟨3873062926170021728702315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10328167803120057943206173 3873062926170021728702315)
    ·
      refine ⟨5809594389255032593053473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3873062926170021728702315 5809594389255032593053473)
      ·
        refine ⟨4357195791941274444790105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5809594389255032593053473 4357195791941274444790105)
        ·
          refine ⟨3267896843955955833592579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4357195791941274444790105 3267896843955955833592579)
          ·
            refine ⟨4901845265933933750388869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3267896843955955833592579 4901845265933933750388869)
            ·
              refine ⟨919095987362612578197913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4901845265933933750388869 919095987362612578197913)
              ·
                refine ⟨689321990521959433648435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 919095987362612578197913 689321990521959433648435)
                ·
                  refine ⟨1033982985782939150472653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 689321990521959433648435 1033982985782939150472653)
                  ·
                    refine ⟨387743619668602181427245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1033982985782939150472653 387743619668602181427245)
                    ·
                      refine ⟨145403857375725818035217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 387743619668602181427245 145403857375725818035217)
                      ·
                        rfl

theorem cell23_283173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_283173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283173 prefixEnd_283173 := by exact prefixLift 283173
  have htrace : WordTrace (prefixWord ++ tailWord_283173) baseStart_283173 baseEnd_283173 := by
    simpa [prefixWord, tailWord_283173, baseEnd_283173] using wordTrace_append hprefix tailTrace_283173
  have hstable : (prefixWord ++ tailWord_283173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283173).length < 2 ^ (prefixWord ++ tailWord_283173).sum := by decide
  have hdescent : baseEnd_283173 < baseStart_283173 := by decide
  rcases family_descends (prefixWord ++ tailWord_283173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283217 : List Nat := [1, 2, 2, 1, 3, 4, 2, 2, 1, 3, 2]
def baseStart_283217 : Nat := 118140960795 + 283217 * 2 ^ 59
def prefixEnd_283217 : Nat := 4983230072969 + 3 ^ 40 * 283217 * 2
def baseEnd_283217 : Nat := 145426450524523645885015

theorem tailTrace_283217 : CollatzResearch.WordTrace tailWord_283217 prefixEnd_283217 145426450524523645885015 := by
  unfold tailWord_283217
  simp only [CollatzResearch.WordTrace]
  refine ⟨10329772614960653457807905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6886515076640435638538603 10329772614960653457807905)
  ·
    refine ⟨7747329461220490093355929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10329772614960653457807905 7747329461220490093355929)
    ·
      refine ⟨5810497095915367570016947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7747329461220490093355929 5810497095915367570016947)
      ·
        refine ⟨8715745643873051355025421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5810497095915367570016947 8715745643873051355025421)
        ·
          refine ⟨3268404616452394258134533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8715745643873051355025421 3268404616452394258134533)
          ·
            refine ⟨612825865584823923400225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3268404616452394258134533 612825865584823923400225)
            ·
              refine ⟨459619399188617942550169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 612825865584823923400225 459619399188617942550169)
              ·
                refine ⟨344714549391463456912627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 459619399188617942550169 344714549391463456912627)
                ·
                  refine ⟨517071824087195185368941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 344714549391463456912627 517071824087195185368941)
                  ·
                    refine ⟨193901934032698194513353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 517071824087195185368941 193901934032698194513353)
                    ·
                      refine ⟨145426450524523645885015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 193901934032698194513353 145426450524523645885015)
                      ·
                        rfl

theorem cell23_283217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 3, 2].length) (baseStart_283217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283217 prefixEnd_283217 := by exact prefixLift 283217
  have htrace : WordTrace (prefixWord ++ tailWord_283217) baseStart_283217 baseEnd_283217 := by
    simpa [prefixWord, tailWord_283217, baseEnd_283217] using wordTrace_append hprefix tailTrace_283217
  have hstable : (prefixWord ++ tailWord_283217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283217).length < 2 ^ (prefixWord ++ tailWord_283217).sum := by decide
  have hdescent : baseEnd_283217 < baseStart_283217 := by decide
  rcases family_descends (prefixWord ++ tailWord_283217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283233 : List Nat := [1, 2, 3, 1, 1, 5, 1, 1, 2, 1, 5]
def baseStart_283233 : Nat := 118140960795 + 283233 * 2 ^ 59
def prefixEnd_283233 : Nat := 4983230072969 + 3 ^ 40 * 283233 * 2
def baseEnd_283233 : Nat := 145434666214995583284941

theorem tailTrace_283233 : CollatzResearch.WordTrace tailWord_283233 prefixEnd_283233 145434666214995583284941 := by
  unfold tailWord_283233
  simp only [CollatzResearch.WordTrace]
  refine ⟨10330356182902688190390353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6886904121935125460260235 10330356182902688190390353)
  ·
    refine ⟨7747767137177016142792765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10330356182902688190390353 7747767137177016142792765)
    ·
      refine ⟨2905412676441381053547287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7747767137177016142792765 2905412676441381053547287)
      ·
        refine ⟨4358119014662071580320931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2905412676441381053547287 4358119014662071580320931)
        ·
          refine ⟨6537178521993107370481397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4358119014662071580320931 6537178521993107370481397)
          ·
            refine ⟨612860486436853815982631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6537178521993107370481397 612860486436853815982631)
            ·
              refine ⟨919290729655280723973947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 612860486436853815982631 919290729655280723973947)
              ·
                refine ⟨1378936094482921085960921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 919290729655280723973947 1378936094482921085960921)
                ·
                  refine ⟨1034202070862190814470691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1378936094482921085960921 1034202070862190814470691)
                  ·
                    refine ⟨1551303106293286221706037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1034202070862190814470691 1551303106293286221706037)
                    ·
                      refine ⟨145434666214995583284941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1551303106293286221706037 145434666214995583284941)
                      ·
                        rfl

theorem cell23_283233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_283233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283233 prefixEnd_283233 := by exact prefixLift 283233
  have htrace : WordTrace (prefixWord ++ tailWord_283233) baseStart_283233 baseEnd_283233 := by
    simpa [prefixWord, tailWord_283233, baseEnd_283233] using wordTrace_append hprefix tailTrace_283233
  have hstable : (prefixWord ++ tailWord_283233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283233).length < 2 ^ (prefixWord ++ tailWord_283233).sum := by decide
  have hdescent : baseEnd_283233 < baseStart_283233 := by decide
  rcases family_descends (prefixWord ++ tailWord_283233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283264 : List Nat := [2, 1, 1, 2, 1, 5, 4, 1, 2, 2, 2]
def baseStart_283264 : Nat := 118140960795 + 283264 * 2 ^ 59
def prefixEnd_283264 : Nat := 4983230072969 + 3 ^ 40 * 283264 * 2
def baseEnd_283264 : Nat := 145450584115284961997299

theorem tailTrace_283264 : CollatzResearch.WordTrace tailWord_283264 prefixEnd_283264 145450584115284961997299 := by
  unfold tailWord_283264
  simp only [CollatzResearch.WordTrace]
  refine ⟨5165743422895190242384423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6887657897193586989845897 5165743422895190242384423)
  ·
    refine ⟨7748615134342785363576635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5165743422895190242384423 7748615134342785363576635)
    ·
      refine ⟨11622922701514178045364953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7748615134342785363576635 11622922701514178045364953)
      ·
        refine ⟨8717192026135633534023715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11622922701514178045364953 8717192026135633534023715)
        ·
          refine ⟨13075788039203450301035573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8717192026135633534023715 13075788039203450301035573)
          ·
            refine ⟨1225855128675323465722085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13075788039203450301035573 1225855128675323465722085)
            ·
              refine ⟨229847836626623149822891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1225855128675323465722085 229847836626623149822891)
              ·
                refine ⟨344771754939934724734337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229847836626623149822891 344771754939934724734337)
                ·
                  refine ⟨258578816204951043550753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 344771754939934724734337 258578816204951043550753)
                  ·
                    refine ⟨193934112153713282663065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 258578816204951043550753 193934112153713282663065)
                    ·
                      refine ⟨145450584115284961997299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 193934112153713282663065 145450584115284961997299)
                      ·
                        rfl

theorem cell23_283264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 2, 2, 2].length) (baseStart_283264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283264 prefixEnd_283264 := by exact prefixLift 283264
  have htrace : WordTrace (prefixWord ++ tailWord_283264) baseStart_283264 baseEnd_283264 := by
    simpa [prefixWord, tailWord_283264, baseEnd_283264] using wordTrace_append hprefix tailTrace_283264
  have hstable : (prefixWord ++ tailWord_283264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283264).length < 2 ^ (prefixWord ++ tailWord_283264).sum := by decide
  have hdescent : baseEnd_283264 < baseStart_283264 := by decide
  rcases family_descends (prefixWord ++ tailWord_283264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283293 : List Nat := [1, 4, 2, 1, 1, 1, 3, 2, 1, 2, 5]
def baseStart_283293 : Nat := 118140960795 + 283293 * 2 ^ 59
def prefixEnd_283293 : Nat := 4983230072969 + 3 ^ 40 * 283293 * 2
def baseEnd_283293 : Nat := 145465475054265348534665

theorem tailTrace_283293 : CollatzResearch.WordTrace tailWord_283293 prefixEnd_283293 145465475054265348534665 := by
  unfold tailWord_283293
  simp only [CollatzResearch.WordTrace]
  refine ⟨10332544562685318437574533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6888363041790212291716355 10332544562685318437574533)
  ·
    refine ⟨1937352105503497207045225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10332544562685318437574533 1937352105503497207045225)
    ·
      refine ⟨1453014079127622905283919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1937352105503497207045225 1453014079127622905283919)
      ·
        refine ⟨2179521118691434357925879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1453014079127622905283919 2179521118691434357925879)
        ·
          refine ⟨3269281678037151536888819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2179521118691434357925879 3269281678037151536888819)
          ·
            refine ⟨4903922517055727305333229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3269281678037151536888819 4903922517055727305333229)
            ·
              refine ⟨1838970943895897739499961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4903922517055727305333229 1838970943895897739499961)
              ·
                refine ⟨1379228207921923304624971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1838970943895897739499961 1379228207921923304624971)
                ·
                  refine ⟨2068842311882884956937457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1379228207921923304624971 2068842311882884956937457)
                  ·
                    refine ⟨1551631733912163717703093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2068842311882884956937457 1551631733912163717703093)
                    ·
                      refine ⟨145465475054265348534665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1551631733912163717703093 145465475054265348534665)
                      ·
                        rfl

theorem cell23_283293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_283293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283293 prefixEnd_283293 := by exact prefixLift 283293
  have htrace : WordTrace (prefixWord ++ tailWord_283293) baseStart_283293 baseEnd_283293 := by
    simpa [prefixWord, tailWord_283293, baseEnd_283293] using wordTrace_append hprefix tailTrace_283293
  have hstable : (prefixWord ++ tailWord_283293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283293).length < 2 ^ (prefixWord ++ tailWord_283293).sum := by decide
  have hdescent : baseEnd_283293 < baseStart_283293 := by decide
  rcases family_descends (prefixWord ++ tailWord_283293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283334 : List Nat := [6, 1, 2, 1, 2, 1, 1, 1, 1, 7]
def baseStart_283334 : Nat := 118140960795 + 283334 * 2 ^ 59
def prefixEnd_283334 : Nat := 4983230072969 + 3 ^ 40 * 283334 * 2
def baseEnd_283334 : Nat := 48495509253699896040659

theorem tailTrace_283334 : CollatzResearch.WordTrace tailWord_283334 prefixEnd_283334 48495509253699896040659 := by
  unfold tailWord_283334
  simp only [CollatzResearch.WordTrace]
  refine ⟨322938748610524451244283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6889359970357854959878037 322938748610524451244283)
  ·
    refine ⟨484408122915786676866425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 322938748610524451244283 484408122915786676866425)
    ·
      refine ⟨363306092186840007649819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 484408122915786676866425 363306092186840007649819)
      ·
        refine ⟨544959138280260011474729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363306092186840007649819 544959138280260011474729)
        ·
          refine ⟨408719353710195008606047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 544959138280260011474729 408719353710195008606047)
          ·
            refine ⟨613079030565292512909071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408719353710195008606047 613079030565292512909071)
            ·
              refine ⟨919618545847938769363607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 613079030565292512909071 919618545847938769363607)
              ·
                refine ⟨1379427818771908154045411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 919618545847938769363607 1379427818771908154045411)
                ·
                  refine ⟨2069141728157862231068117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1379427818771908154045411 2069141728157862231068117)
                  ·
                    refine ⟨48495509253699896040659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2069141728157862231068117 48495509253699896040659)
                    ·
                      rfl

theorem cell23_283334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_283334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283334 prefixEnd_283334 := by exact prefixLift 283334
  have htrace : WordTrace (prefixWord ++ tailWord_283334) baseStart_283334 baseEnd_283334 := by
    simpa [prefixWord, tailWord_283334, baseEnd_283334] using wordTrace_append hprefix tailTrace_283334
  have hstable : (prefixWord ++ tailWord_283334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283334).length < 2 ^ (prefixWord ++ tailWord_283334).sum := by decide
  have hdescent : baseEnd_283334 < baseStart_283334 := by decide
  rcases family_descends (prefixWord ++ tailWord_283334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283403 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 3, 6]
def baseStart_283403 : Nat := 118140960795 + 283403 * 2 ^ 59
def prefixEnd_283403 : Nat := 4983230072969 + 3 ^ 40 * 283403 * 2
def baseEnd_283403 : Nat := 48507319308753306053053

theorem tailTrace_283403 : CollatzResearch.WordTrace tailWord_283403 prefixEnd_283403 48507319308753306053053 := by
  unfold tailWord_283403
  simp only [CollatzResearch.WordTrace]
  refine ⟨10336556592286807224078863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6891037728191204816052575 10336556592286807224078863)
  ·
    refine ⟨15504834888430210836118295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10336556592286807224078863 15504834888430210836118295)
    ·
      refine ⟨23257252332645316254177443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15504834888430210836118295 23257252332645316254177443)
      ·
        refine ⟨34885878498967974381266165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23257252332645316254177443 34885878498967974381266165)
        ·
          refine ⟨3270551109278247598243703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34885878498967974381266165 3270551109278247598243703)
          ·
            refine ⟨4905826663917371397365555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3270551109278247598243703 4905826663917371397365555)
            ·
              refine ⟨7358739995876057096048333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4905826663917371397365555 7358739995876057096048333)
              ·
                refine ⟨2759527498453521411018125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7358739995876057096048333 2759527498453521411018125)
                ·
                  refine ⟨1034822811920070529131797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2759527498453521411018125 1034822811920070529131797)
                  ·
                    refine ⟨48507319308753306053053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1034822811920070529131797 48507319308753306053053)
                    ·
                      rfl

theorem cell23_283403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 6].length) (baseStart_283403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283403 prefixEnd_283403 := by exact prefixLift 283403
  have htrace : WordTrace (prefixWord ++ tailWord_283403) baseStart_283403 baseEnd_283403 := by
    simpa [prefixWord, tailWord_283403, baseEnd_283403] using wordTrace_append hprefix tailTrace_283403
  have hstable : (prefixWord ++ tailWord_283403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283403).length < 2 ^ (prefixWord ++ tailWord_283403).sum := by decide
  have hdescent : baseEnd_283403 < baseStart_283403 := by decide
  rcases family_descends (prefixWord ++ tailWord_283403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283444 : List Nat := [2, 5, 1, 1, 3, 1, 1, 1, 3, 1, 4]
def baseStart_283444 : Nat := 118140960795 + 283444 * 2 ^ 59
def prefixEnd_283444 : Nat := 4983230072969 + 3 ^ 40 * 283444 * 2
def baseEnd_283444 : Nat := 145543010633094257746471

theorem tailTrace_283444 : CollatzResearch.WordTrace tailWord_283444 prefixEnd_283444 145543010633094257746471 := by
  unfold tailWord_283444
  simp only [CollatzResearch.WordTrace]
  refine ⟨5169025992569135613160693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6892034656758847484214257 5169025992569135613160693)
  ·
    refine ⟨484596186803356463733815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5169025992569135613160693 484596186803356463733815)
    ·
      refine ⟨726894280205034695600723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 484596186803356463733815 726894280205034695600723)
      ·
        refine ⟨1090341420307552043401085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 726894280205034695600723 1090341420307552043401085)
        ·
          refine ⟨408878032615332016275407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1090341420307552043401085 408878032615332016275407)
          ·
            refine ⟨613317048922998024413111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408878032615332016275407 613317048922998024413111)
            ·
              refine ⟨919975573384497036619667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 613317048922998024413111 919975573384497036619667)
              ·
                refine ⟨1379963360076745554929501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 919975573384497036619667 1379963360076745554929501)
                ·
                  refine ⟨517486260028779583098563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1379963360076745554929501 517486260028779583098563)
                  ·
                    refine ⟨776229390043169374647845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 517486260028779583098563 776229390043169374647845)
                    ·
                      refine ⟨145543010633094257746471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 776229390043169374647845 145543010633094257746471)
                      ·
                        rfl

theorem cell23_283444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_283444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283444 prefixEnd_283444 := by exact prefixLift 283444
  have htrace : WordTrace (prefixWord ++ tailWord_283444) baseStart_283444 baseEnd_283444 := by
    simpa [prefixWord, tailWord_283444, baseEnd_283444] using wordTrace_append hprefix tailTrace_283444
  have hstable : (prefixWord ++ tailWord_283444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283444).length < 2 ^ (prefixWord ++ tailWord_283444).sum := by decide
  have hdescent : baseEnd_283444 < baseStart_283444 := by decide
  rcases family_descends (prefixWord ++ tailWord_283444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283464 : List Nat := [2, 1, 3, 1, 1, 3, 5, 1, 1, 2, 3]
def baseStart_283464 : Nat := 118140960795 + 283464 * 2 ^ 59
def prefixEnd_283464 : Nat := 4983230072969 + 3 ^ 40 * 283464 * 2
def baseEnd_283464 : Nat := 145553280246184179496379

theorem tailTrace_283464 : CollatzResearch.WordTrace tailWord_283464 prefixEnd_283464 145553280246184179496379 := by
  unfold tailWord_283464
  simp only [CollatzResearch.WordTrace]
  refine ⟨5169390722532907321024723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6892520963377209761366297 5169390722532907321024723)
  ·
    refine ⟨7754086083799360981537085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5169390722532907321024723 7754086083799360981537085)
    ·
      refine ⟨2907782281424760368076407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7754086083799360981537085 2907782281424760368076407)
      ·
        refine ⟨4361673422137140552114611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2907782281424760368076407 4361673422137140552114611)
        ·
          refine ⟨6542510133205710828171917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4361673422137140552114611 6542510133205710828171917)
          ·
            refine ⟨2453441299952141560564469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6542510133205710828171917 2453441299952141560564469)
            ·
              refine ⟨230010121870513271302919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2453441299952141560564469 230010121870513271302919)
              ·
                refine ⟨345015182805769906954379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230010121870513271302919 345015182805769906954379)
                ·
                  refine ⟨517522774208654860431569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 345015182805769906954379 517522774208654860431569)
                  ·
                    refine ⟨388142080656491145323677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 517522774208654860431569 388142080656491145323677)
                    ·
                      refine ⟨145553280246184179496379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 388142080656491145323677 145553280246184179496379)
                      ·
                        rfl

theorem cell23_283464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 1, 2, 3].length) (baseStart_283464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283464 prefixEnd_283464 := by exact prefixLift 283464
  have htrace : WordTrace (prefixWord ++ tailWord_283464) baseStart_283464 baseEnd_283464 := by
    simpa [prefixWord, tailWord_283464, baseEnd_283464] using wordTrace_append hprefix tailTrace_283464
  have hstable : (prefixWord ++ tailWord_283464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283464).length < 2 ^ (prefixWord ++ tailWord_283464).sum := by decide
  have hdescent : baseEnd_283464 < baseStart_283464 := by decide
  rcases family_descends (prefixWord ++ tailWord_283464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283483 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 8]
def baseStart_283483 : Nat := 118140960795 + 283483 * 2 ^ 59
def prefixEnd_283483 : Nat := 4983230072969 + 3 ^ 40 * 283483 * 2
def baseEnd_283483 : Nat := 145563036378619605158791

theorem tailTrace_283483 : CollatzResearch.WordTrace tailWord_283483 prefixEnd_283483 145563036378619605158791 := by
  unfold tailWord_283483
  simp only [CollatzResearch.WordTrace]
  refine ⟨10339474431996980886991103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6892982954664653924660735 10339474431996980886991103)
  ·
    refine ⟨15509211647995471330486655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10339474431996980886991103 15509211647995471330486655)
    ·
      refine ⟨23263817471993206995729983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15509211647995471330486655 23263817471993206995729983)
      ·
        refine ⟨34895726207989810493594975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23263817471993206995729983 34895726207989810493594975)
        ·
          refine ⟨52343589311984715740392463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34895726207989810493594975 52343589311984715740392463)
          ·
            refine ⟨78515383967977073610588695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52343589311984715740392463 78515383967977073610588695)
            ·
              refine ⟨117773075951965610415883043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78515383967977073610588695 117773075951965610415883043)
              ·
                refine ⟨176659613927948415623824565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117773075951965610415883043 176659613927948415623824565)
                ·
                  refine ⟨16561838805745163964733553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 176659613927948415623824565 16561838805745163964733553)
                  ·
                    refine ⟨12421379104308872973550165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16561838805745163964733553 12421379104308872973550165)
                    ·
                      refine ⟨145563036378619605158791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 12421379104308872973550165 145563036378619605158791)
                      ·
                        rfl

theorem cell23_283483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 8].length) (baseStart_283483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283483 prefixEnd_283483 := by exact prefixLift 283483
  have htrace : WordTrace (prefixWord ++ tailWord_283483) baseStart_283483 baseEnd_283483 := by
    simpa [prefixWord, tailWord_283483, baseEnd_283483] using wordTrace_append hprefix tailTrace_283483
  have hstable : (prefixWord ++ tailWord_283483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283483).length < 2 ^ (prefixWord ++ tailWord_283483).sum := by decide
  have hdescent : baseEnd_283483 < baseStart_283483 := by decide
  rcases family_descends (prefixWord ++ tailWord_283483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283487 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 5, 3, 2]
def baseStart_283487 : Nat := 118140960795 + 283487 * 2 ^ 59
def prefixEnd_283487 : Nat := 4983230072969 + 3 ^ 40 * 283487 * 2
def baseEnd_283487 : Nat := 145565090301237589508773

theorem tailTrace_283487 : CollatzResearch.WordTrace tailWord_283487 prefixEnd_283487 145565090301237589508773 := by
  unfold tailWord_283487
  simp only [CollatzResearch.WordTrace]
  refine ⟨10339620323982489570136715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6893080215988326380091143 10339620323982489570136715)
  ·
    refine ⟨15509430485973734355205073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10339620323982489570136715 15509430485973734355205073)
    ·
      refine ⟨11632072864480300766403805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15509430485973734355205073 11632072864480300766403805)
      ·
        refine ⟨4362027324180112787401427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11632072864480300766403805 4362027324180112787401427)
        ·
          refine ⟨6543040986270169181102141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4362027324180112787401427 6543040986270169181102141)
          ·
            refine ⟨2453640369851313442913303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6543040986270169181102141 2453640369851313442913303)
            ·
              refine ⟨3680460554776970164369955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2453640369851313442913303 3680460554776970164369955)
              ·
                refine ⟨5520690832165455246554933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3680460554776970164369955 5520690832165455246554933)
                ·
                  refine ⟨517564765515511429364525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5520690832165455246554933 517564765515511429364525)
                  ·
                    refine ⟨194086787068316786011697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 517564765515511429364525 194086787068316786011697)
                    ·
                      refine ⟨145565090301237589508773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 194086787068316786011697 145565090301237589508773)
                      ·
                        rfl

theorem cell23_283487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 3, 2].length) (baseStart_283487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283487 prefixEnd_283487 := by exact prefixLift 283487
  have htrace : WordTrace (prefixWord ++ tailWord_283487) baseStart_283487 baseEnd_283487 := by
    simpa [prefixWord, tailWord_283487, baseEnd_283487] using wordTrace_append hprefix tailTrace_283487
  have hstable : (prefixWord ++ tailWord_283487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283487).length < 2 ^ (prefixWord ++ tailWord_283487).sum := by decide
  have hdescent : baseEnd_283487 < baseStart_283487 := by decide
  rcases family_descends (prefixWord ++ tailWord_283487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283500 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 4]
def baseStart_283500 : Nat := 118140960795 + 283500 * 2 ^ 59
def prefixEnd_283500 : Nat := 4983230072969 + 3 ^ 40 * 283500 * 2
def baseEnd_283500 : Nat := 145571765549746038646213

theorem tailTrace_283500 : CollatzResearch.WordTrace tailWord_283500 prefixEnd_283500 145571765549746038646213 := by
  unfold tailWord_283500
  simp only [CollatzResearch.WordTrace]
  refine ⟨5170047236467696395179977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6893396315290261860239969 5170047236467696395179977)
  ·
    refine ⟨3877535427350772296384983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5170047236467696395179977 3877535427350772296384983)
    ·
      refine ⟨5816303141026158444577475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3877535427350772296384983 5816303141026158444577475)
      ·
        refine ⟨8724454711539237666866213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5816303141026158444577475 8724454711539237666866213)
        ·
          refine ⟨1635835258413607062537415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8724454711539237666866213 1635835258413607062537415)
          ·
            refine ⟨2453752887620410593806123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1635835258413607062537415 2453752887620410593806123)
            ·
              refine ⟨3680629331430615890709185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2453752887620410593806123 3680629331430615890709185)
              ·
                refine ⟨2760471998572961918031889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3680629331430615890709185 2760471998572961918031889)
                ·
                  refine ⟨2070353998929721438523917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2760471998572961918031889 2070353998929721438523917)
                  ·
                    refine ⟨776382749598645539446469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2070353998929721438523917 776382749598645539446469)
                    ·
                      refine ⟨145571765549746038646213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 776382749598645539446469 145571765549746038646213)
                      ·
                        rfl

theorem cell23_283500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_283500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283500 prefixEnd_283500 := by exact prefixLift 283500
  have htrace : WordTrace (prefixWord ++ tailWord_283500) baseStart_283500 baseEnd_283500 := by
    simpa [prefixWord, tailWord_283500, baseEnd_283500] using wordTrace_append hprefix tailTrace_283500
  have hstable : (prefixWord ++ tailWord_283500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283500).length < 2 ^ (prefixWord ++ tailWord_283500).sum := by decide
  have hdescent : baseEnd_283500 < baseStart_283500 := by decide
  rcases family_descends (prefixWord ++ tailWord_283500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283520 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 3]
def baseStart_283520 : Nat := 118140960795 + 283520 * 2 ^ 59
def prefixEnd_283520 : Nat := 4983230072969 + 3 ^ 40 * 283520 * 2
def baseEnd_283520 : Nat := 145582035162835960396121

theorem tailTrace_283520 : CollatzResearch.WordTrace tailWord_283520 prefixEnd_283520 145582035162835960396121 := by
  unfold tailWord_283520
  simp only [CollatzResearch.WordTrace]
  refine ⟨5170411966431468103044007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6893882621908624137392009 5170411966431468103044007)
  ·
    refine ⟨7755617949647202154566011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5170411966431468103044007 7755617949647202154566011)
    ·
      refine ⟨11633426924470803231849017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7755617949647202154566011 11633426924470803231849017)
      ·
        refine ⟨8725070193353102423886763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11633426924470803231849017 8725070193353102423886763)
        ·
          refine ⟨13087605290029653635830145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8725070193353102423886763 13087605290029653635830145)
          ·
            refine ⟨9815703967522240226872609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13087605290029653635830145 9815703967522240226872609)
            ·
              refine ⟨7361777975641680170154457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9815703967522240226872609 7361777975641680170154457)
              ·
                refine ⟨5521333481731260127615843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7361777975641680170154457 5521333481731260127615843)
                ·
                  refine ⟨8282000222596890191423765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5521333481731260127615843 8282000222596890191423765)
                  ·
                    refine ⟨388218760434229227722989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8282000222596890191423765 388218760434229227722989)
                    ·
                      refine ⟨145582035162835960396121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 388218760434229227722989 145582035162835960396121)
                      ·
                        rfl

theorem cell23_283520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 3].length) (baseStart_283520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283520 prefixEnd_283520 := by exact prefixLift 283520
  have htrace : WordTrace (prefixWord ++ tailWord_283520) baseStart_283520 baseEnd_283520 := by
    simpa [prefixWord, tailWord_283520, baseEnd_283520] using wordTrace_append hprefix tailTrace_283520
  have hstable : (prefixWord ++ tailWord_283520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283520).length < 2 ^ (prefixWord ++ tailWord_283520).sum := by decide
  have hdescent : baseEnd_283520 < baseStart_283520 := by decide
  rcases family_descends (prefixWord ++ tailWord_283520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283551 : List Nat := [1, 1, 2, 5, 2, 3, 1, 1, 1, 4, 2]
def baseStart_283551 : Nat := 118140960795 + 283551 * 2 ^ 59
def prefixEnd_283551 : Nat := 4983230072969 + 3 ^ 40 * 283551 * 2
def baseEnd_283551 : Nat := 145597953063125339108479

theorem tailTrace_283551 : CollatzResearch.WordTrace tailWord_283551 prefixEnd_283551 145597953063125339108479 := by
  unfold tailWord_283551
  simp only [CollatzResearch.WordTrace]
  refine ⟨10341954595750628500466507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6894636397167085666977671 10341954595750628500466507)
  ·
    refine ⟨15512931893625942750699761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10341954595750628500466507 15512931893625942750699761)
    ·
      refine ⟨11634698920219457063024821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15512931893625942750699761 11634698920219457063024821)
      ·
        refine ⟨1090753023770574099658577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11634698920219457063024821 1090753023770574099658577)
        ·
          refine ⟨818064767827930574743933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1090753023770574099658577 818064767827930574743933)
          ·
            refine ⟨306774287935473965528975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 818064767827930574743933 306774287935473965528975)
            ·
              refine ⟨460161431903210948293463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306774287935473965528975 460161431903210948293463)
              ·
                refine ⟨690242147854816422440195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 460161431903210948293463 690242147854816422440195)
                ·
                  refine ⟨1035363221782224633660293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 690242147854816422440195 1035363221782224633660293)
                  ·
                    refine ⟨194130604084167118811305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1035363221782224633660293 194130604084167118811305)
                    ·
                      refine ⟨145597953063125339108479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 194130604084167118811305 145597953063125339108479)
                      ·
                        rfl

theorem cell23_283551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_283551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283551 prefixEnd_283551 := by exact prefixLift 283551
  have htrace : WordTrace (prefixWord ++ tailWord_283551) baseStart_283551 baseEnd_283551 := by
    simpa [prefixWord, tailWord_283551, baseEnd_283551] using wordTrace_append hprefix tailTrace_283551
  have hstable : (prefixWord ++ tailWord_283551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283551).length < 2 ^ (prefixWord ++ tailWord_283551).sum := by decide
  have hdescent : baseEnd_283551 < baseStart_283551 := by decide
  rcases family_descends (prefixWord ++ tailWord_283551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283617 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 5, 4]
def baseStart_283617 : Nat := 118140960795 + 283617 * 2 ^ 59
def prefixEnd_283617 : Nat := 4983230072969 + 3 ^ 40 * 283617 * 2
def baseEnd_283617 : Nat := 48543947595440693627725

theorem tailTrace_283617 : CollatzResearch.WordTrace tailWord_283617 prefixEnd_283617 48543947595440693627725 := by
  unfold tailWord_283617
  simp only [CollatzResearch.WordTrace]
  refine ⟨10344361813511521772369105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6896241209007681181579403 10344361813511521772369105)
  ·
    refine ⟨7758271360133641329276829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10344361813511521772369105 7758271360133641329276829)
    ·
      refine ⟨2909351760050115498478811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7758271360133641329276829 2909351760050115498478811)
      ·
        refine ⟨4364027640075173247718217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2909351760050115498478811 4364027640075173247718217)
        ·
          refine ⟨3273020730056379935788663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4364027640075173247718217 3273020730056379935788663)
          ·
            refine ⟨4909531095084569903682995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3273020730056379935788663 4909531095084569903682995)
            ·
              refine ⟨7364296642626854855524493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4909531095084569903682995 7364296642626854855524493)
              ·
                refine ⟨2761611240985070570821685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7364296642626854855524493 2761611240985070570821685)
                ·
                  refine ⟨258901053842350366014533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2761611240985070570821685 258901053842350366014533)
                  ·
                    refine ⟨48543947595440693627725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 258901053842350366014533 48543947595440693627725)
                    ·
                      rfl

theorem cell23_283617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_283617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283617 prefixEnd_283617 := by exact prefixLift 283617
  have htrace : WordTrace (prefixWord ++ tailWord_283617) baseStart_283617 baseEnd_283617 := by
    simpa [prefixWord, tailWord_283617, baseEnd_283617] using wordTrace_append hprefix tailTrace_283617
  have hstable : (prefixWord ++ tailWord_283617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283617).length < 2 ^ (prefixWord ++ tailWord_283617).sum := by decide
  have hdescent : baseEnd_283617 < baseStart_283617 := by decide
  rcases family_descends (prefixWord ++ tailWord_283617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283621 : List Nat := [1, 3, 1, 6, 1, 1, 2, 1, 2, 5]
def baseStart_283621 : Nat := 118140960795 + 283621 * 2 ^ 59
def prefixEnd_283621 : Nat := 4983230072969 + 3 ^ 40 * 283621 * 2
def baseEnd_283621 : Nat := 48544632236313355077719

theorem tailTrace_283621 : CollatzResearch.WordTrace tailWord_283621 prefixEnd_283621 48544632236313355077719 := by
  unfold tailWord_283621
  simp only [CollatzResearch.WordTrace]
  refine ⟨10344507705497030455514717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6896338470331353637009811 10344507705497030455514717)
  ·
    refine ⟨3879190389561386420818019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10344507705497030455514717 3879190389561386420818019)
    ·
      refine ⟨5818785584342079631227029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3879190389561386420818019 5818785584342079631227029)
      ·
        refine ⟨272755574266034982713767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5818785584342079631227029 272755574266034982713767)
        ·
          refine ⟨409133361399052474070651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272755574266034982713767 409133361399052474070651)
          ·
            refine ⟨613700042098578711105977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409133361399052474070651 613700042098578711105977)
            ·
              refine ⟨460275031573934033329483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 613700042098578711105977 460275031573934033329483)
              ·
                refine ⟨690412547360901049994225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 460275031573934033329483 690412547360901049994225)
                ·
                  refine ⟨517809410520675787495669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 690412547360901049994225 517809410520675787495669)
                  ·
                    refine ⟨48544632236313355077719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 517809410520675787495669 48544632236313355077719)
                    ·
                      rfl

theorem cell23_283621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 5].length) (baseStart_283621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283621 prefixEnd_283621 := by exact prefixLift 283621
  have htrace : WordTrace (prefixWord ++ tailWord_283621) baseStart_283621 baseEnd_283621 := by
    simpa [prefixWord, tailWord_283621, baseEnd_283621] using wordTrace_append hprefix tailTrace_283621
  have hstable : (prefixWord ++ tailWord_283621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283621).length < 2 ^ (prefixWord ++ tailWord_283621).sum := by decide
  have hdescent : baseEnd_283621 < baseStart_283621 := by decide
  rcases family_descends (prefixWord ++ tailWord_283621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283644 : List Nat := [2, 2, 2, 1, 2, 3, 2, 2, 2, 2, 3]
def baseStart_283644 : Nat := 118140960795 + 283644 * 2 ^ 59
def prefixEnd_283644 : Nat := 4983230072969 + 3 ^ 40 * 283644 * 2
def baseEnd_283644 : Nat := 145645706763993475245551

theorem tailTrace_283644 : CollatzResearch.WordTrace tailWord_283644 prefixEnd_283644 145645706763993475245551 := by
  unfold tailWord_283644
  simp only [CollatzResearch.WordTrace]
  refine ⟨5172673292206852691800993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6896897722942470255734657 5172673292206852691800993)
  ·
    refine ⟨3879504969155139518850745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5172673292206852691800993 3879504969155139518850745)
    ·
      refine ⟨2909628726866354639138059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3879504969155139518850745 2909628726866354639138059)
      ·
        refine ⟨4364443090299531958707089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2909628726866354639138059 4364443090299531958707089)
        ·
          refine ⟨3273332317724648969030317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4364443090299531958707089 3273332317724648969030317)
          ·
            refine ⟨1227499619146743363386369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3273332317724648969030317 1227499619146743363386369)
            ·
              refine ⟨920624714360057522539777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1227499619146743363386369 920624714360057522539777)
              ·
                refine ⟨690468535770043141904833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 920624714360057522539777 690468535770043141904833)
                ·
                  refine ⟨517851401827532356428625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 690468535770043141904833 517851401827532356428625)
                  ·
                    refine ⟨388388551370649267321469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 517851401827532356428625 388388551370649267321469)
                    ·
                      refine ⟨145645706763993475245551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 388388551370649267321469 145645706763993475245551)
                      ·
                        rfl

theorem cell23_283644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_283644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283644 prefixEnd_283644 := by exact prefixLift 283644
  have htrace : WordTrace (prefixWord ++ tailWord_283644) baseStart_283644 baseEnd_283644 := by
    simpa [prefixWord, tailWord_283644, baseEnd_283644] using wordTrace_append hprefix tailTrace_283644
  have hstable : (prefixWord ++ tailWord_283644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283644).length < 2 ^ (prefixWord ++ tailWord_283644).sum := by decide
  have hdescent : baseEnd_283644 < baseStart_283644 := by decide
  rcases family_descends (prefixWord ++ tailWord_283644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283708 : List Nat := [2, 2, 2, 2, 2, 2, 2, 4, 1, 1, 3]
def baseStart_283708 : Nat := 118140960795 + 283708 * 2 ^ 59
def prefixEnd_283708 : Nat := 4983230072969 + 3 ^ 40 * 283708 * 2
def baseEnd_283708 : Nat := 145678569525881224845257

theorem tailTrace_283708 : CollatzResearch.WordTrace tailWord_283708 prefixEnd_283708 145678569525881224845257 := by
  unfold tailWord_283708
  simp only [CollatzResearch.WordTrace]
  refine ⟨5173840428090922156965889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6898453904121229542621185 5173840428090922156965889)
  ·
    refine ⟨3880380321068191617724417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5173840428090922156965889 3880380321068191617724417)
    ·
      refine ⟨2910285240801143713293313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3880380321068191617724417 2910285240801143713293313)
      ·
        refine ⟨2182713930600857784969985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2910285240801143713293313 2182713930600857784969985)
        ·
          refine ⟨1637035447950643338727489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2182713930600857784969985 1637035447950643338727489)
          ·
            refine ⟨1227776585962982504045617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1637035447950643338727489 1227776585962982504045617)
            ·
              refine ⟨920832439472236878034213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1227776585962982504045617 920832439472236878034213)
              ·
                refine ⟨172656082401044414631415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 920832439472236878034213 172656082401044414631415)
                ·
                  refine ⟨258984123601566621947123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 172656082401044414631415 258984123601566621947123)
                  ·
                    refine ⟨388476185402349932920685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 258984123601566621947123 388476185402349932920685)
                    ·
                      refine ⟨145678569525881224845257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 388476185402349932920685 145678569525881224845257)
                      ·
                        rfl

theorem cell23_283708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_283708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283708 prefixEnd_283708 := by exact prefixLift 283708
  have htrace : WordTrace (prefixWord ++ tailWord_283708) baseStart_283708 baseEnd_283708 := by
    simpa [prefixWord, tailWord_283708, baseEnd_283708] using wordTrace_append hprefix tailTrace_283708
  have hstable : (prefixWord ++ tailWord_283708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283708).length < 2 ^ (prefixWord ++ tailWord_283708).sum := by decide
  have hdescent : baseEnd_283708 < baseStart_283708 := by decide
  rcases family_descends (prefixWord ++ tailWord_283708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283717 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 3, 1, 5]
def baseStart_283717 : Nat := 118140960795 + 283717 * 2 ^ 59
def prefixEnd_283717 : Nat := 4983230072969 + 3 ^ 40 * 283717 * 2
def baseEnd_283717 : Nat := 145683190851771689632715

theorem tailTrace_283717 : CollatzResearch.WordTrace tailWord_283717 prefixEnd_283717 145683190851771689632715 := by
  unfold tailWord_283717
  simp only [CollatzResearch.WordTrace]
  refine ⟨10348009113149238851009405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6898672742099492567339603 10348009113149238851009405)
  ·
    refine ⟨3880503417430964569128527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10348009113149238851009405 3880503417430964569128527)
    ·
      refine ⟨5820755126146446853692791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3880503417430964569128527 5820755126146446853692791)
      ·
        refine ⟨8731132689219670280539187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5820755126146446853692791 8731132689219670280539187)
        ·
          refine ⟨13096699033829505420808781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8731132689219670280539187 13096699033829505420808781)
          ·
            refine ⟨4911262137686064532803293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13096699033829505420808781 4911262137686064532803293)
            ·
              refine ⟨1841723301632274199801235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4911262137686064532803293 1841723301632274199801235)
              ·
                refine ⟨2762584952448411299701853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1841723301632274199801235 2762584952448411299701853)
                ·
                  refine ⟨1035969357168154237388195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2762584952448411299701853 1035969357168154237388195)
                  ·
                    refine ⟨1553954035752231356082293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1035969357168154237388195 1553954035752231356082293)
                    ·
                      refine ⟨145683190851771689632715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1553954035752231356082293 145683190851771689632715)
                      ·
                        rfl

theorem cell23_283717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_283717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283717 prefixEnd_283717 := by exact prefixLift 283717
  have htrace : WordTrace (prefixWord ++ tailWord_283717) baseStart_283717 baseEnd_283717 := by
    simpa [prefixWord, tailWord_283717, baseEnd_283717] using wordTrace_append hprefix tailTrace_283717
  have hstable : (prefixWord ++ tailWord_283717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283717).length < 2 ^ (prefixWord ++ tailWord_283717).sum := by decide
  have hdescent : baseEnd_283717 < baseStart_283717 := by decide
  rcases family_descends (prefixWord ++ tailWord_283717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283718 : List Nat := [6, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2]
def baseStart_283718 : Nat := 118140960795 + 283718 * 2 ^ 59
def prefixEnd_283718 : Nat := 4983230072969 + 3 ^ 40 * 283718 * 2
def baseEnd_283718 : Nat := 145683704332426185720211

theorem tailTrace_283718 : CollatzResearch.WordTrace tailWord_283718 prefixEnd_283718 145683704332426185720211 := by
  unfold tailWord_283718
  simp only [CollatzResearch.WordTrace]
  refine ⟨323376424567050500681119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6898697057430410681197205 323376424567050500681119)
  ·
    refine ⟨485064636850575751021679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 323376424567050500681119 485064636850575751021679)
    ·
      refine ⟨727596955275863626532519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 485064636850575751021679 727596955275863626532519)
      ·
        refine ⟨1091395432913795439798779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 727596955275863626532519 1091395432913795439798779)
        ·
          refine ⟨1637093149370693159698169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1091395432913795439798779 1637093149370693159698169)
          ·
            refine ⟨1227819862028019869773627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1637093149370693159698169 1227819862028019869773627)
            ·
              refine ⟨1841729793042029804660441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1227819862028019869773627 1841729793042029804660441)
              ·
                refine ⟨1381297344781522353495331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1841729793042029804660441 1381297344781522353495331)
                ·
                  refine ⟨2071946017172283530242997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1381297344781522353495331 2071946017172283530242997)
                  ·
                    refine ⟨194244939109901580960281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2071946017172283530242997 194244939109901580960281)
                    ·
                      refine ⟨145683704332426185720211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 194244939109901580960281 145683704332426185720211)
                      ·
                        rfl

theorem cell23_283718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_283718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283718 prefixEnd_283718 := by exact prefixLift 283718
  have htrace : WordTrace (prefixWord ++ tailWord_283718) baseStart_283718 baseEnd_283718 := by
    simpa [prefixWord, tailWord_283718, baseEnd_283718] using wordTrace_append hprefix tailTrace_283718
  have hstable : (prefixWord ++ tailWord_283718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283718).length < 2 ^ (prefixWord ++ tailWord_283718).sum := by decide
  have hdescent : baseEnd_283718 < baseStart_283718 := by decide
  rcases family_descends (prefixWord ++ tailWord_283718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283751 : List Nat := [1, 1, 5, 1, 1, 3, 2, 3, 1, 2, 3]
def baseStart_283751 : Nat := 118140960795 + 283751 * 2 ^ 59
def prefixEnd_283751 : Nat := 4983230072969 + 3 ^ 40 * 283751 * 2
def baseEnd_283751 : Nat := 145700649194024556607559

theorem tailTrace_283751 : CollatzResearch.WordTrace tailWord_283751 prefixEnd_283751 145700649194024556607559 := by
  unfold tailWord_283751
  simp only [CollatzResearch.WordTrace]
  refine ⟨10349249195026062657747107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6899499463350708438498071 10349249195026062657747107)
  ·
    refine ⟨15523873792539093986620661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10349249195026062657747107 15523873792539093986620661)
    ·
      refine ⟨1455363168050540061245687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15523873792539093986620661 1455363168050540061245687)
      ·
        refine ⟨2183044752075810091868531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1455363168050540061245687 2183044752075810091868531)
        ·
          refine ⟨3274567128113715137802797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2183044752075810091868531 3274567128113715137802797)
          ·
            refine ⟨1227962673042643176676049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3274567128113715137802797 1227962673042643176676049)
            ·
              refine ⟨920972004781982382507037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1227962673042643176676049 920972004781982382507037)
              ·
                refine ⟨345364501793243393440139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 920972004781982382507037 345364501793243393440139)
                ·
                  refine ⟨518046752689865090160209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 345364501793243393440139 518046752689865090160209)
                  ·
                    refine ⟨388535064517398817620157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 518046752689865090160209 388535064517398817620157)
                    ·
                      refine ⟨145700649194024556607559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 388535064517398817620157 145700649194024556607559)
                      ·
                        rfl

theorem cell23_283751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_283751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283751 prefixEnd_283751 := by exact prefixLift 283751
  have htrace : WordTrace (prefixWord ++ tailWord_283751) baseStart_283751 baseEnd_283751 := by
    simpa [prefixWord, tailWord_283751, baseEnd_283751] using wordTrace_append hprefix tailTrace_283751
  have hstable : (prefixWord ++ tailWord_283751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283751).length < 2 ^ (prefixWord ++ tailWord_283751).sum := by decide
  have hdescent : baseEnd_283751 < baseStart_283751 := by decide
  rcases family_descends (prefixWord ++ tailWord_283751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283754 : List Nat := [3, 1, 3, 2, 2, 3, 9]
def baseStart_283754 : Nat := 118140960795 + 283754 * 2 ^ 59
def prefixEnd_283754 : Nat := 4983230072969 + 3 ^ 40 * 283754 * 2
def baseEnd_283754 : Nat := 1798792464641827714445

theorem tailTrace_283754 : CollatzResearch.WordTrace tailWord_283754 prefixEnd_283754 1798792464641827714445 := by
  unfold tailWord_283754
  simp only [CollatzResearch.WordTrace]
  refine ⟨2587339653503798542526579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6899572409343462780070877 2587339653503798542526579)
  ·
    refine ⟨3881009480255697813789869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2587339653503798542526579 3881009480255697813789869)
    ·
      refine ⟨1455378555095886680171201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3881009480255697813789869 1455378555095886680171201)
      ·
        refine ⟨1091533916321915010128401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1455378555095886680171201 1091533916321915010128401)
        ·
          refine ⟨818650437241436257596301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1091533916321915010128401 818650437241436257596301)
          ·
            refine ⟨306993913965538596598613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 818650437241436257596301 306993913965538596598613)
            ·
              refine ⟨1798792464641827714445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 306993913965538596598613 1798792464641827714445)
              ·
                rfl

theorem cell23_283754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 9].length) (baseStart_283754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283754 prefixEnd_283754 := by exact prefixLift 283754
  have htrace : WordTrace (prefixWord ++ tailWord_283754) baseStart_283754 baseEnd_283754 := by
    simpa [prefixWord, tailWord_283754, baseEnd_283754] using wordTrace_append hprefix tailTrace_283754
  have hstable : (prefixWord ++ tailWord_283754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283754).length < 2 ^ (prefixWord ++ tailWord_283754).sum := by decide
  have hdescent : baseEnd_283754 < baseStart_283754 := by decide
  rcases family_descends (prefixWord ++ tailWord_283754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283767 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 2, 7]
def baseStart_283767 : Nat := 118140960795 + 283767 * 2 ^ 59
def prefixEnd_283767 : Nat := 4983230072969 + 3 ^ 40 * 283767 * 2
def baseEnd_283767 : Nat := 48569621628165498002495

theorem tailTrace_283767 : CollatzResearch.WordTrace tailWord_283767 prefixEnd_283767 48569621628165498002495 := by
  unfold tailWord_283767
  simp only [CollatzResearch.WordTrace]
  refine ⟨10349832762968097390329555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6899888508645398260219703 10349832762968097390329555)
  ·
    refine ⟨15524749144452146085494333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10349832762968097390329555 15524749144452146085494333)
    ·
      refine ⟨5821780929169554782060375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15524749144452146085494333 5821780929169554782060375)
      ·
        refine ⟨8732671393754332173090563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5821780929169554782060375 8732671393754332173090563)
        ·
          refine ⟨13099007090631498259635845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8732671393754332173090563 13099007090631498259635845)
          ·
            refine ⟨2456063829493405923681721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13099007090631498259635845 2456063829493405923681721)
            ·
              refine ⟨1842047872120054442761291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2456063829493405923681721 1842047872120054442761291)
              ·
                refine ⟨2763071808180081664141937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1842047872120054442761291 2763071808180081664141937)
                ·
                  refine ⟨2072303856135061248106453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2763071808180081664141937 2072303856135061248106453)
                  ·
                    refine ⟨48569621628165498002495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2072303856135061248106453 48569621628165498002495)
                    ·
                      rfl

theorem cell23_283767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 7].length) (baseStart_283767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283767 prefixEnd_283767 := by exact prefixLift 283767
  have htrace : WordTrace (prefixWord ++ tailWord_283767) baseStart_283767 baseEnd_283767 := by
    simpa [prefixWord, tailWord_283767, baseEnd_283767] using wordTrace_append hprefix tailTrace_283767
  have hstable : (prefixWord ++ tailWord_283767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283767).length < 2 ^ (prefixWord ++ tailWord_283767).sum := by decide
  have hdescent : baseEnd_283767 < baseStart_283767 := by decide
  rcases family_descends (prefixWord ++ tailWord_283767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283797 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 3, 8]
def baseStart_283797 : Nat := 118140960795 + 283797 * 2 ^ 59
def prefixEnd_283797 : Nat := 4983230072969 + 3 ^ 40 * 283797 * 2
def baseEnd_283797 : Nat := 48574756434710458877449

theorem tailTrace_283797 : CollatzResearch.WordTrace tailWord_283797 prefixEnd_283797 48574756434710458877449 := by
  unfold tailWord_283797
  simp only [CollatzResearch.WordTrace]
  refine ⟨10350926952859412513921645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6900617968572941675947763 10350926952859412513921645)
  ·
    refine ⟨3881597607322279692720617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10350926952859412513921645 3881597607322279692720617)
    ·
      refine ⟨2911198205491709769540463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3881597607322279692720617 2911198205491709769540463)
      ·
        refine ⟨4366797308237564654310695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2911198205491709769540463 4366797308237564654310695)
        ·
          refine ⟨6550195962356346981466043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4366797308237564654310695 6550195962356346981466043)
          ·
            refine ⟨9825293943534520472199065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6550195962356346981466043 9825293943534520472199065)
            ·
              refine ⟨7368970457650890354149299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9825293943534520472199065 7368970457650890354149299)
              ·
                refine ⟨11053455686476335531223949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7368970457650890354149299 11053455686476335531223949)
                ·
                  refine ⟨4145045882428625824208981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11053455686476335531223949 4145045882428625824208981)
                  ·
                    refine ⟨48574756434710458877449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4145045882428625824208981 48574756434710458877449)
                    ·
                      rfl

theorem cell23_283797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_283797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283797 prefixEnd_283797 := by exact prefixLift 283797
  have htrace : WordTrace (prefixWord ++ tailWord_283797) baseStart_283797 baseEnd_283797 := by
    simpa [prefixWord, tailWord_283797, baseEnd_283797] using wordTrace_append hprefix tailTrace_283797
  have hstable : (prefixWord ++ tailWord_283797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283797).length < 2 ^ (prefixWord ++ tailWord_283797).sum := by decide
  have hdescent : baseEnd_283797 < baseStart_283797 := by decide
  rcases family_descends (prefixWord ++ tailWord_283797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283815 : List Nat := [1, 1, 6, 2, 1, 2, 2, 2, 2, 1, 3]
def baseStart_283815 : Nat := 118140960795 + 283815 * 2 ^ 59
def prefixEnd_283815 : Nat := 4983230072969 + 3 ^ 40 * 283815 * 2
def baseEnd_283815 : Nat := 145733511955912306207265

theorem tailTrace_283815 : CollatzResearch.WordTrace tailWord_283815 prefixEnd_283815 145733511955912306207265 := by
  unfold tailWord_283815
  simp only [CollatzResearch.WordTrace]
  refine ⟨10351583466794201588076899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6901055644529467725384599 10351583466794201588076899)
  ·
    refine ⟨15527375200191302382115349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10351583466794201588076899 15527375200191302382115349)
    ·
      refine ⟨727845712508967299161657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15527375200191302382115349 727845712508967299161657)
      ·
        refine ⟨545884284381725474371243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 727845712508967299161657 545884284381725474371243)
        ·
          refine ⟨818826426572588211556865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 545884284381725474371243 818826426572588211556865)
          ·
            refine ⟨614119819929441158667649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 818826426572588211556865 614119819929441158667649)
            ·
              refine ⟨460589864947080869000737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 614119819929441158667649 460589864947080869000737)
              ·
                refine ⟨345442398710310651750553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 460589864947080869000737 345442398710310651750553)
                ·
                  refine ⟨259081799032732988812915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 345442398710310651750553 259081799032732988812915)
                  ·
                    refine ⟨388622698549099483219373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 259081799032732988812915 388622698549099483219373)
                    ·
                      refine ⟨145733511955912306207265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 388622698549099483219373 145733511955912306207265)
                      ·
                        rfl

theorem cell23_283815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_283815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283815 prefixEnd_283815 := by exact prefixLift 283815
  have htrace : WordTrace (prefixWord ++ tailWord_283815) baseStart_283815 baseEnd_283815 := by
    simpa [prefixWord, tailWord_283815, baseEnd_283815] using wordTrace_append hprefix tailTrace_283815
  have hstable : (prefixWord ++ tailWord_283815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283815).length < 2 ^ (prefixWord ++ tailWord_283815).sum := by decide
  have hdescent : baseEnd_283815 < baseStart_283815 := by decide
  rcases family_descends (prefixWord ++ tailWord_283815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283838 : List Nat := [4, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2]
def baseStart_283838 : Nat := 118140960795 + 283838 * 2 ^ 59
def prefixEnd_283838 : Nat := 4983230072969 + 3 ^ 40 * 283838 * 2
def baseEnd_283838 : Nat := 145745322010965716219659

theorem tailTrace_283838 : CollatzResearch.WordTrace tailWord_283838 prefixEnd_283838 145745322010965716219659 := by
  unfold tailWord_283838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1294052793213859564520521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6901614897140584344109445 1294052793213859564520521)
  ·
    refine ⟨970539594910394673390391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1294052793213859564520521 970539594910394673390391)
    ·
      refine ⟨1455809392365592010085587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 970539594910394673390391 1455809392365592010085587)
      ·
        refine ⟨2183714088548388015128381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1455809392365592010085587 2183714088548388015128381)
        ·
          refine ⟨818892783205645505673143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2183714088548388015128381 818892783205645505673143)
          ·
            refine ⟨1228339174808468258509715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 818892783205645505673143 1228339174808468258509715)
            ·
              refine ⟨1842508762212702387764573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1228339174808468258509715 1842508762212702387764573)
              ·
                refine ⟨690940785829763395411715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1842508762212702387764573 690940785829763395411715)
                ·
                  refine ⟨1036411178744645093117573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 690940785829763395411715 1036411178744645093117573)
                  ·
                    refine ⟨194327096014620954959545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1036411178744645093117573 194327096014620954959545)
                    ·
                      refine ⟨145745322010965716219659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 194327096014620954959545 145745322010965716219659)
                      ·
                        rfl

theorem cell23_283838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_283838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283838 prefixEnd_283838 := by exact prefixLift 283838
  have htrace : WordTrace (prefixWord ++ tailWord_283838) baseStart_283838 baseEnd_283838 := by
    simpa [prefixWord, tailWord_283838, baseEnd_283838] using wordTrace_append hprefix tailTrace_283838
  have hstable : (prefixWord ++ tailWord_283838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283838).length < 2 ^ (prefixWord ++ tailWord_283838).sum := by decide
  have hdescent : baseEnd_283838 < baseStart_283838 := by decide
  rcases family_descends (prefixWord ++ tailWord_283838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283914 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5]
def baseStart_283914 : Nat := 118140960795 + 283914 * 2 ^ 59
def prefixEnd_283914 : Nat := 4983230072969 + 3 ^ 40 * 283914 * 2
def baseEnd_283914 : Nat := 145784346540707418869309

theorem tailTrace_283914 : CollatzResearch.WordTrace tailWord_283914 prefixEnd_283914 145784346540707418869309 := by
  unfold tailWord_283914
  simp only [CollatzResearch.WordTrace]
  refine ⟨2588798573358885373982699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6903462862290360997287197 2588798573358885373982699)
  ·
    refine ⟨3883197860038328060974049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2588798573358885373982699 3883197860038328060974049)
    ·
      refine ⟨2912398395028746045730537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3883197860038328060974049 2912398395028746045730537)
      ·
        refine ⟨2184298796271559534297903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2912398395028746045730537 2184298796271559534297903)
        ·
          refine ⟨3276448194407339301446855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2184298796271559534297903 3276448194407339301446855)
          ·
            refine ⟨4914672291611008952170283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3276448194407339301446855 4914672291611008952170283)
            ·
              refine ⟨7372008437416513428255425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4914672291611008952170283 7372008437416513428255425)
              ·
                refine ⟨5529006328062385071191569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7372008437416513428255425 5529006328062385071191569)
                ·
                  refine ⟨4146754746046788803393677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5529006328062385071191569 4146754746046788803393677)
                  ·
                    refine ⟨1555033029767545801272629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4146754746046788803393677 1555033029767545801272629)
                    ·
                      refine ⟨145784346540707418869309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1555033029767545801272629 145784346540707418869309)
                      ·
                        rfl

theorem cell23_283914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_283914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_283914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_283914 prefixEnd_283914 := by exact prefixLift 283914
  have htrace : WordTrace (prefixWord ++ tailWord_283914) baseStart_283914 baseEnd_283914 := by
    simpa [prefixWord, tailWord_283914, baseEnd_283914] using wordTrace_append hprefix tailTrace_283914
  have hstable : (prefixWord ++ tailWord_283914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283914).length < 2 ^ (prefixWord ++ tailWord_283914).sum := by decide
  have hdescent : baseEnd_283914 < baseStart_283914 := by decide
  rcases family_descends (prefixWord ++ tailWord_283914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284018 : List Nat := [3, 2, 1, 2, 1, 2, 2, 4, 1, 1, 4]
def baseStart_284018 : Nat := 118140960795 + 284018 * 2 ^ 59
def prefixEnd_284018 : Nat := 4983230072969 + 3 ^ 40 * 284018 * 2
def baseEnd_284018 : Nat := 145837748528775011968831

theorem tailTrace_284018 : CollatzResearch.WordTrace tailWord_284018 prefixEnd_284018 145837748528775011968831 := by
  unfold tailWord_284018
  simp only [CollatzResearch.WordTrace]
  refine ⟨2589746871264691814429177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6905991656705844838477805 2589746871264691814429177)
  ·
    refine ⟨1942310153448518860821883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2589746871264691814429177 1942310153448518860821883)
    ·
      refine ⟨2913465230172778291232825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1942310153448518860821883 2913465230172778291232825)
      ·
        refine ⟨2185098922629583718424619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2913465230172778291232825 2185098922629583718424619)
        ·
          refine ⟨3277648383944375577636929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2185098922629583718424619 3277648383944375577636929)
          ·
            refine ⟨2458236287958281683227697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3277648383944375577636929 2458236287958281683227697)
            ·
              refine ⟨1843677215968711262420773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2458236287958281683227697 1843677215968711262420773)
              ·
                refine ⟨345689477994133361703895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1843677215968711262420773 345689477994133361703895)
                ·
                  refine ⟨518534216991200042555843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 345689477994133361703895 518534216991200042555843)
                  ·
                    refine ⟨777801325486800063833765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 518534216991200042555843 777801325486800063833765)
                    ·
                      refine ⟨145837748528775011968831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 777801325486800063833765 145837748528775011968831)
                      ·
                        rfl

theorem cell23_284018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_284018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_284018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_284018 prefixEnd_284018 := by exact prefixLift 284018
  have htrace : WordTrace (prefixWord ++ tailWord_284018) baseStart_284018 baseEnd_284018 := by
    simpa [prefixWord, tailWord_284018, baseEnd_284018] using wordTrace_append hprefix tailTrace_284018
  have hstable : (prefixWord ++ tailWord_284018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284018).length < 2 ^ (prefixWord ++ tailWord_284018).sum := by decide
  have hdescent : baseEnd_284018 < baseStart_284018 := by decide
  rcases family_descends (prefixWord ++ tailWord_284018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
